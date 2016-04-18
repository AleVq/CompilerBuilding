all:
	happy -gca ParCLike.y
	alex -g LexCLike.x
	ghc --make TestCLike.hs -o TestCLike

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi

distclean: clean
	-rm -f DocCLike.* LexCLike.* ParCLike.* LayoutCLike.* SkelCLike.* PrintCLike.* TestCLike.* AbsCLike.* TestCLike ErrM.* SharedString.* ComposOp.* C_like22.dtd XMLCLike.* Makefile*
	
