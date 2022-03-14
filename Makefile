.PHONY: p2

%.ll:%.bc
	llvm-dis $<
	cat $@

%.o:%.cpp
	clang++ -c `llvm-config --cxxflags` -o $@ $<

%.ll:%.c
	clang -c -S -emit-llvm -o $@ $<

%.o:%.bc
	clang++ -c -o$@ $<

p2: p2.o
	clang++ -o$@ $^ `llvm-config --cxxflags --ldflags --libs --system-libs`

clean:
	rm -f p2.o p2 *~ main.bc main.ll
