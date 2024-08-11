GHC        = ghc

COMPILER_NAME = latc_x86_64
COMPILER_SOURCE = Main.hs

.PHONY : all clean

all : $(COMPILER_NAME) cleanDist

$(COMPILER_NAME) : $(COMPILER_SOURCE)
	${GHC} $< -o ../$@

cleanDist :
	find . \( -name '*.hi' -o -name '*.o' \) -type f -exec rm -f {} \;

clean : cleanDist
	rm -f ../$(COMPILER_NAME)
