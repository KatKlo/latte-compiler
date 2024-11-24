GHC        = ghc

COMPILER_NAME = latc
COMPILER_SOURCE = Main.hs

.PHONY : all clean cleanDist

all : $(COMPILER_NAME) clean

$(COMPILER_NAME) : $(COMPILER_SOURCE)
	${GHC} $< -o ../$@

clean :
	find . \( -name '*.hi' -o -name '*.o' \) -type f -exec rm -f {} \;
	rm -f Grammar/*.x Grammar/*.y Grammar/*.info Grammar/*.hs.bak Grammar/*.txt Grammar/Makefile Grammar/ErrM.hs Grammar/SkelLatte.hs Grammar/TestLatte.hs Grammar/TestLatte

cleanDist : clean
	rm -f ../$(COMPILER_NAME)
