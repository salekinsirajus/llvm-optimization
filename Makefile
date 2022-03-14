.PHONY: p2

%.ll:%.bc
	llvm-dis-13 $<
	cat $@

%.o:%.cpp
	clang++-13 -c `llvm-config-13 --cxxflags` -o $@ $<

%.ll:%.c
	clang-13 -c -S -emit-llvm -o $@ $<

%.o:%.bc
	clang++-13 -c -o$@ $<

p2: p2.o
	clang++-13 -o$@ $^ `llvm-config-13 --cxxflags --ldflags --libs --system-libs`

clean:
	rm -f p2.o p2 *~ main.bc main.ll
