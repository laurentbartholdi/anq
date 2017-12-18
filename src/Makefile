###############################################################################
##
##               Nilpotent Quotient for Lie Rings            
## Makefile                                                     Csaba Schneider
##                                                           schcs@math.klte.hu
##

#CPPFLAGS = -DVERSION='"3.0 2017-11-24"' -DCOEFF_IS_MPZ
#CPPFLAGS = -DVERSION='"3.0 2017-11-24"' -DCOEFF_IS_Z
#CPPFLAGS = -DVERSION='"3.0 2017-11-24"' -DCOEFF_IS_MODp_k -DMODULUS_PRIME=3 -DMODULUS_EXPONENT=16
CPPFLAGS = -DVERSION='"3.0 2017-11-27"' -DCOEFF_IS_MOD2_64
#CPPFLAGS = -DVERSION='"3.0 2017-11-27"' -DCOEFF_IS_LONG
OPT = -O0
DEBUG = -g -ggdb
CXXFLAGS = -std=gnu++11 -Wall -Werror $(DEBUG) $(OPT)
CFLAGS = -Wall -Werror $(DEBUG) $(OPT)
LDLIBS = -lgmp
LDFLAGS = $(DEBUG)

## LieNQ prefers GNU C compiler.

ifeq ($(shell uname -s),Darwin)
    CC = g++-7
    CXX = g++-7
else
    CC = g++
    CXX = g++
endif

LIENQ_OBJ = presentation.o print.o readpres.o operations.o matrix.o epim.o addgen.o consistency.o tails.o auxiliary.o lienq.o

LIENQ_INCLUDES = lienq.h coeff_long.h coeff_z.h coeff_mpz.h coeff_2_64.h coeff_p_k.h

all: lienq rips

lienq: $(LIENQ_OBJ)

clean:
	rm -f $(LIENQ_OBJ) lienq

addgen.o: addgen.cc $(LIENQ_INCLUDES)  

auxiliary.o: auxiliary.cc $(LIENQ_INCLUDES)  

consistency.o: consistency.cc $(LIENQ_INCLUDES)

epim.o: epim.cc $(LIENQ_INCLUDES)

lienq.o: lienq.cc $(LIENQ_INCLUDES)

matrix.o: matrix.cc $(LIENQ_INCLUDES)

operations.o: operations.cc $(LIENQ_INCLUDES)  

presentation.o: presentation.cc $(LIENQ_INCLUDES)

print.o: print.cc $(LIENQ_INCLUDES)  

readpres.o: readpres.cc $(LIENQ_INCLUDES)

tails.o: tails.cc $(LIENQ_INCLUDES)

test: test.cc

test.s: test.cc
	g++-7 -O3 -march=native -std=c++11 -S $< -o $@

rips: rips.cc rref.o
	g++-7 -g rips.cc rref.o -o rips -lgmp -lflint

mat: mat.cc rref.o
	g++-7 -std=c++14 -g mat.cc rref.o -o mat -lgmp -lflint # -lntl # -lgivaro -lgmp -lgmpxx -llinbox

rref.o: rref.cc
