.PHONY : all clean

all :
	make -C src

clean :
	make clean -C src

cleanDist :
	make cleanDist -C src
