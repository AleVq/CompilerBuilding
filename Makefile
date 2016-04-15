all:
	happy -gca ParC.y
	alex -g LexC.x
	ghc --make TestC.hs -o TestC

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f  LexC.* ParC.* TestImpy.* AbsC.* TestC ErrM.*
	
testDefaultPrint:
	