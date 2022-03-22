#include <fstream>
#include <memory>
#include <algorithm>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm-c/Core.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Analysis/InstructionSimplify.h"

#include "llvm/IR/InstIterator.h"
#include "llvm/Transforms/Utils/FunctionComparator.h"
#include "llvm/IR/Value.h"

using namespace llvm;


static void CommonSubexpressionElimination(Module *);

static void summarize(Module *M);
static void print_csv_file(std::string outputfile);

static cl::opt<std::string>
        InputFilename(cl::Positional, cl::desc("<input bitcode>"), cl::Required, cl::init("-"));

static cl::opt<std::string>
        OutputFilename(cl::Positional, cl::desc("<output bitcode>"), cl::Required, cl::init("out.bc"));

static cl::opt<bool>
        Mem2Reg("mem2reg",
                cl::desc("Perform memory to register promotion before CSE."),
                cl::init(false));

static cl::opt<bool>
        NoCSE("no-cse",
              cl::desc("Do not perform CSE Optimization."),
              cl::init(false));

static cl::opt<bool>
        Verbose("verbose",
                    cl::desc("Verbose stats."),
                    cl::init(false));

static cl::opt<bool>
        NoCheck("no",
                cl::desc("Do not check for valid IR."),
                cl::init(false));

int main(int argc, char **argv) {
    // Parse command line arguments
    cl::ParseCommandLineOptions(argc, argv, "llvm system compiler\n");

    // Handle creating output files and shutting down properly
    llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.
    LLVMContext Context;

    // LLVM idiom for constructing output file.
    std::unique_ptr<ToolOutputFile> Out;
    std::string ErrorInfo;
    std::error_code EC;
    Out.reset(new ToolOutputFile(OutputFilename.c_str(), EC,
                                 sys::fs::OF_None));

    EnableStatistics();

    // Read in module
    SMDiagnostic Err;
    std::unique_ptr<Module> M;
    M = parseIRFile(InputFilename, Err, Context);

    // If errors, fail
    if (M.get() == 0)
    {
        Err.print(argv[0], errs());
        return 1;
    }

    // If requested, do some early optimizations
    if (Mem2Reg)
    {
        legacy::PassManager Passes;
        Passes.add(createPromoteMemoryToRegisterPass());
        Passes.run(*M.get());
    }

    if (!NoCSE) {
        CommonSubexpressionElimination(M.get());
    }

    // Collect statistics on Module
    summarize(M.get());
    print_csv_file(OutputFilename);

    if (Verbose)
        PrintStatistics(errs());

    // Verify integrity of Module, do this by default
    if (!NoCheck)
    {
        legacy::PassManager Passes;
        Passes.add(createVerifierPass());
        Passes.run(*M.get());
    }

    // Write final bitcode
    WriteBitcodeToFile(*M.get(), Out->os());
    Out->keep();

    return 0;
}

static llvm::Statistic nFunctions = {"", "Functions", "number of functions"};
static llvm::Statistic nInstructions = {"", "Instructions", "number of instructions"};
static llvm::Statistic nLoads = {"", "Loads", "number of loads"};
static llvm::Statistic nStores = {"", "Stores", "number of stores"};

static void summarize(Module *M) {
    for (auto i = M->begin(); i != M->end(); i++) {
        if (i->begin() != i->end()) {
            nFunctions++;
        }

        for (auto j = i->begin(); j != i->end(); j++) {
            for (auto k = j->begin(); k != j->end(); k++) {
                Instruction &I = *k;
                nInstructions++;
                if (isa<LoadInst>(&I)) {
                    nLoads++;
                } else if (isa<StoreInst>(&I)) {
                    nStores++;
                }
            }
        }
    }
}

static void print_csv_file(std::string outputfile)
{
    std::ofstream stats(outputfile + ".stats");
    auto a = GetStatistics();
    for (auto p : a) {
        stats << p.first.str() << "," << p.second << std::endl;
    }
    stats.close();
}

static llvm::Statistic CSEDead = {"", "CSEDead", "CSE found dead instructions"};
static llvm::Statistic CSEElim = {"", "CSEElim", "CSE redundant instructions"};
static llvm::Statistic CSESimplify = {"", "CSESimplify", "CSE simplified instructions"};
static llvm::Statistic CSELdElim = {"", "CSELdElim", "CSE redundant loads"};
static llvm::Statistic CSEStore2Load = {"", "CSEStore2Load", "CSE forwarded store to load"};
static llvm::Statistic CSEStElim = {"", "CSEStElim", "CSE redundant stores"};


static bool ignoreForCSE(Instruction &I){
    /* Instruction is not a good candidate for CSE if they are of the following
     * type: Loads, Stores, Terminators, VAArg, Calls, Allocas, and FCmps
     */
    if (isa<LoadInst>(&I) || isa<StoreInst>(&I) ||
        isa<AllocaInst>(&I) || isa<FCmpInst>(&I) ||
        isa<CallInst>(&I) || isa<VAArgInst>(&I)  ||
        I.isTerminator()
       ){
        return true;
    }

    return false; 
}

static bool isLiteralMatch(Instruction &a, Instruction &b){
    /* Remove IF:
     * Same opcode
     * Same type (LLVMTypeOf of the instruction not its operands)
     * Same number of operands
     * Same operands in the same order (no commutativity)
     * */
    if (a.getOpcode() == b.getOpcode() && a.getType() == b.getType() &&
        a.getNumOperands() == b.getNumOperands()
       ){

        int c = a.getNumOperands() - 1;
        while (c >= 0){
            if (a.getOperand(c)->getType() == b.getOperand(c)->getType()) {return false;}
            if (a.getOperand(c)->getValueID() == b.getOperand(c)->getValueID()) {return false;}
            c--;
        } 
    	return true;
    }
    
    return false;
} 


static bool shouldRemoveTrivialDeadCode(Instruction &x){
    /* Similar to isTriviallyDeadInstruction
     *
     * Check whether instruction has any side effects
     *
     * Store / Volatie {load,store}/ Branch / Fence
     * */
    if (isa<CallInst>(&x) || x.mayHaveSideEffects() ||
        x.isTerminator()
       ){
        return false;
    }

    if (x.use_empty()){
        return true;
    }

    return false;
}


static void populateWorkList(std::set<Instruction *> &wl, BasicBlock *blk){

      // blk is a pointer to a BasicBlock instance
     for (BasicBlock::iterator i = blk->begin(), e = blk->end(); i != e; ++i){

        Instruction& inst = *i;
        if (!ignoreForCSE(inst)){
            wl.insert(&inst);
        }
     }
     printf("after populating\n"); 
     printf("size of the worklist: %d\n", wl.size());
}

static void CSEOnWorkListInstructions(std::set<Instruction*> &cleanup_list){
    std::set<Instruction*> to_remove;
    std::set<Instruction*>::iterator inner, it;
    printf("before working on it\n"); 
    printf("Size of the worklist: %d\n", cleanup_list.size());
    int i = (int) cleanup_list.size();
    
    for (auto i:cleanup_list){
        i->print(errs());
    }

    //while (i > 0){
    //    Instruction* i = *cleanup_list.begin();

        //i->print(errs());
            //if isLiteralMatch(x, y);
            //y.replaceUsesWith(x);
            //y.eraseFromParent();
            //cleanup
    //    i--;
   // }
}


static void SeparateCSEBasicV2(Module *M){

    DominatorTreeBase<BasicBlock,false> *DT=nullptr; //dominance
    DT = new DominatorTreeBase<BasicBlock,false>();

    std::set<Instruction*> worklist;
    for (Module::iterator func = M->begin(); func != M->end(); ++func){

        DT->recalculate(*func);

            DomTreeNodeBase<BasicBlock>::iterator it,end;
            DomTreeNodeBase<BasicBlock> *Node = DT->getRootNode();
            
            printf("before getting into the loop\n");
            if (Node->begin() == Node->end()){
                printf("same beginning and end\n");
                continue;
            }
            for(it=Node->begin(),end=Node->end(); it!=end; it++){
                populateWorkList(worklist, Node->getBlock());
            }
            CSEOnWorkListInstructions(worklist);
            worklist.clear();
    }
}


static void SeparateCSEBasic(Module *M){

    DominatorTreeBase<BasicBlock,false> *DT=nullptr; //dominance
    DT = new DominatorTreeBase<BasicBlock,false>();

    std::set<Instruction*> worklist;
    for (Module::iterator func = M->begin(); func != M->end(); ++func){
        Function& f = *func;
        
        DT->recalculate(f);
        if (f.begin() == f.end()){
            printf("no basic block in this function\n");
            continue;
        }

        DomTreeNodeBase<BasicBlock>::iterator it,end;
        DomTreeNodeBase<BasicBlock> *Node = DT->getRootNode();

        
        for(it=Node->begin(),end=Node->end(); it!=end; it++){
            //Taverse all the child of 'it'
            //Does this return the first block or the second one?
            //BasicBlock *child = (*it)->getBlock();
            //while (child != Node.end()){
                //BasicBlock *child = (*child)->getBlock(); // get each bb it immediately dominates
                //BasicBlock *child = (*it)->getBlock(); // get each bb it immediately dominates
                populateWorkList(worklist, Node->getBlock());

            //}
        
        }
        CSEOnWorkListInstructions(worklist);
        worklist.clear();
    }
}



static bool RunSimplifyInstruction(Instruction &I, const SimplifyQuery &Q){
    /* Runs the simplifyInstruction library function
     *
     * If any simplification was achieved, it replaces the uses of this value
     * */

    Instruction *k;
    k = &I;
    Value* result = SimplifyInstruction(k, Q);
    
    if (result != nullptr) {
        //replace uses with result
        k->replaceAllUsesWith(result);
        CSESimplify++;
        return true;
    }
    //leave it be
    return false;
}

static void SimplifyInstructionPass(Module *M){
    /* Runs a pass where you try do simple constant folding and such things
     *
     * */

    for (Module::iterator func = M->begin(); func != M->end(); ++func){
        for (Function::iterator fi = func->begin(); fi != func->end(); ++fi){
            for (BasicBlock::iterator bbi = fi->begin(); bbi != fi->end(); ++bbi){
               Instruction& inst = *bbi;
                if (RunSimplifyInstruction(inst, M->getDataLayout())){
                    ++bbi;
                    inst.eraseFromParent();
                }
            }
        }
    }
}

static void CommonSubexpressionElimination(Module *M) {
    /* Driver function
     * 
     * Runs different optimization sub-passes in a certain order
     * */

    //runCSEBasic(M);
    SeparateCSEBasicV2(M);
}

