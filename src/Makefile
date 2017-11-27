###############################################################################
##
##               Nilpotent Quotient for Lie Rings            
## Makefile                                                     Csaba Schneider
##                                                           schcs@math.klte.hu
##

# CPPFLAGS = -DVERSION='"3.0 2017-11-24"' -DCOEFF_IS_MPZ
# CPPFLAGS = -DVERSION='"3.0 2017-11-27"' -DCOEFF_IS_MOD2_64
CPPFLAGS = -DVERSION='"3.0 2017-11-27"' -DCOEFF_IS_LONG
COPTS = -O0 -g -Wall -Werror
CXXFLAGS = -std=c++11 $(COPTS)
CFLAGS = $(COPTS)
LDLIBS = -lgmp
LDFLAGS = $(COPTS)

## LieNQ prefers GNU C compiler.

ifeq ($(UNAME),Darwin)
    CC = g++-7
    CXX = g++-7
else
    CC = g++
    CXX = g++
endif

OBJ = presentation.o print.o readpres.o operations.o matrix.o epim.o addgen.o consistency.o tails.o auxiliary.o lienq.o

lienq: $(OBJ)

clean:
	rm -f $(OBJ) lienq

addgen.o: addgen.C lienq.h  

auxiliary.o: auxiliary.C lienq.h  

consistency.o: consistency.C lienq.h

epim.o: epim.C lienq.h

lienq.o: lienq.C lienq.h

matrix.o: matrix.C lienq.h

operations.o: operations.C lienq.h  

presentation.o: presentation.C lienq.h

print.o: print.C lienq.h  

readpres.o: readpres.C lienq.h

tails.o: tails.C lienq.h

test: test.C
