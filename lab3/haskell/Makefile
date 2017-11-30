# Makefile for PLT lab 3

.PHONY : lab3 test testsuite

testcore=test

default : test

# cannot be default goal, will loop forever
all : test testsuite

test : test/$(testcore).cc lab3 Runtime.class
	lab3 $<
	java $(testcore)

testsuite : lab3 Runtime.class
	./run-testsuite.sh

lab3 : lab3.hs TypeChecker.hs Compiler.hs CPP/Test Ann/Abs.hs
	ghc --make lab3.hs -o lab3

CPP/Test.hs CPP/Lex.x CPP/Layout.hs CPP/Par.y : CPP.cf
	bnfc --haskell -d $<

CPP/Par.hs: CPP/Par.y
	happy -gcai $<

CPP/Lex.hs: CPP/Lex.x
	alex -g $<

CPP/Test: CPP/Test.hs CPP/Par.hs CPP/Lex.hs
	ghc --make $< -o $@

Ann/Abs.hs Ann/Test.hs Ann/Lex.x Ann/Layout.hs Ann/Par.y : Ann.cf
	bnfc --haskell -d $<

Ann/Par.hs: Ann/Par.y
	happy -gcai $<

Ann/Lex.hs: Ann/Lex.x
	alex -g $<

Ann/Test: Ann/Test.hs Ann/Par.hs Ann/Lex.hs
	ghc --make $< -o $@

%.class : %.java
	javac $<

clean:
	-rm -f Ann/*.log Ann/*.aux Ann/*.hi Ann/*.o Ann/*.dvi
	-rm -f CPP/*.log CPP/*.aux CPP/*.hi CPP/*.o CPP/*.dvi

distclean: clean
	-rm -f Ann/Doc.* Ann/Lex.* Ann/Par.* Ann/Layout.* Ann/Skel.* Ann/Print.* Ann/Test.* Ann/Abs.* Ann/Test Ann/ErrM.* Ann/SharedString.* Ann/ComposOp.* Ann/Ann.dtd Ann/XML.*
	-rmdir -p Ann/
	-rm -f CPP/Doc.* CPP/Lex.* CPP/Par.* CPP/Layout.* CPP/Skel.* CPP/Print.* CPP/Test.* CPP/Abs.* CPP/Test CPP/ErrM.* CPP/SharedString.* CPP/ComposOp.* CPP/CPP.dtd CPP/XML.*
	-rmdir -p CPP/


# EOF
