declare a dominator tree object dt
for each function in a module
    dt->recalculate(function)
    node = get root of this dt (BasicBlock)
    for each node(=BasicBlock) in the dominator tree
        for each instruction in node
            wl = populate_worklist(inst, inst->parent())
            perfor_cse_on(inst, wl)
            

def populate_worklist(inst, bb)
    while (bb != end) {
        if (inst->getParent() == parent_bb){
            //start from the location after this
            start = next_instruction
        } else
            start = it-begin()
        for (it->begin(); it != end; ++it){
            wl.insert(bb-);
        }

        it++;
        bb = (*it)->getBlock();
   
   return wl
}

def CSEBasicOnInstruction(Instruction I, w){
    for dominated_inst in w{
        if isLiteralMatch(){
            //remove from basic block
            //increament counter
        }
        
    }
}
