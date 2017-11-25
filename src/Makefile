###############################################################################
##
##               Nilpotent Quotient for Lie Rings            
## Makefile                                                     Csaba Schneider
##                                                           schcs@math.klte.hu
##

CPPFLAGS = -DVERSION='"3.0 2017-11-24"'
COPTS = -O0 -g -Wall -Werror
CXXFLAGS = -std=c++11 $(COPTS)
CFLAGS = $(COPTS)
LDLIBS = -lgmp
LDFLAGS = $(COPTS)

## LieNQ prefers GNU C compiler.

CC = gcc-7
CXX = g++-7
OBJ = presentation.o print.o readpres.o operations.o matrix.o epim.o addgen.o consistency.o tails.o auxialiary.o lienq.o

lienq: $(OBJ)
#	$(CC) $^ -o $@ -lgmp

clean:
	rm -f $(OBJ)

addgen.o: addgen.C lienq.h lietype.h  

auxialiary.o: auxialiary.C lienq.h lietype.h  

consistency.o: consistency.C lienq.h lietype.h

epim.o: epim.C lienq.h lietype.h

lienq.o: lienq.C lienq.h lietype.h

matrix.o: matrix.C lienq.h lietype.h

operations.o: operations.C lienq.h lietype.h  

presentation.o: presentation.C lienq.h lietype.h

print.o: print.C lienq.h lietype.h  

readpres.o: readpres.C readpres.h lienq.h lietype.h

tails.o: tails.C lienq.h lietype.h
