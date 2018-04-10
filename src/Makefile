###############################################################################
##
##               Nilpotent Quotient for Lie Rings            
## Makefile                                                     Csaba Schneider
##                                                           schcs@math.klte.hu
##

LIENQVERSION = -DVERSION='"3.1.1 2017-12-31"'
OPT = -O0 #3
DEBUG = -g -ggdb
CXXFLAGS = -std=gnu++11 -Wall -Werror $(DEBUG) $(OPT)
CFLAGS = -Wall -Werror $(DEBUG) $(OPT)
LDFLAGS = $(DEBUG)

## LieNQ prefers GNU C compiler.

ifeq ($(shell uname -s),Darwin)
    CC = g++-7
    CXX = g++-7
else
    CC = g++
    CXX = g++
endif

LIENQ_OBJ = fppresentation.o pcpresentation.o print.o operations.o matrix.o consistency.o tails.o auxiliary.o lienq.o

all: lienq_long lienq_2_64 lienq_3_38 lienq_3_39 lienq_mpz


clean:
	rm -f *.o lienq

lienq_mpz: $(subst .o,_mpz.o,$(LIENQ_OBJ))
	$(CXX) -o $@ $^ -lgmp

%_mpz.o: %.cc lienq.h coeff.h coeff_mpz.h
	$(CXX) -c -DCOEFF_IS_MPZ $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_z: $(subst .o,_z.o,$(LIENQ_OBJ))
	$(CXX) -o $@ $^ -lgmp

%_z.o: %.cc lienq.h coeff.h coeff_z.h
	$(CXX) -c -DCOEFF_IS_Z $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_long: $(subst .o,_long.o,$(LIENQ_OBJ))

%_long.o: %.cc lienq.h coeff.h coeff_long.h
	$(CXX) -c -DCOEFF_IS_LONG $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_2_64: $(subst .o,_2_64.o,$(LIENQ_OBJ))

%_2_64.o: %.cc lienq.h coeff.h coeff_2_64.h
	$(CXX) -c -DCOEFF_IS_MOD2_64 $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_3_39: $(subst .o,_3_39.o,$(LIENQ_OBJ))

%_3_39.o: %.cc lienq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_MODp_k -DMODULUS_PRIME=3 -DMODULUS_EXPONENT=39 $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_3_38: $(subst .o,_3_38.o,$(LIENQ_OBJ))

%_3_38.o: %.cc lienq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_MODp_k -DMODULUS_PRIME=3 -DMODULUS_EXPONENT=38 $(CXXFLAGS) $(LIENQVERSION) $< -o $@

test: test.cc

test.s: test.cc
	g++-7 -O3 -march=native -std=c++11 -S $< -o $@

rips: rips.cc rref.o
	g++-7 -g rips.cc rref.o -o rips -lgmp -lflint -liml -lcblas

mat: mat.cc rref.o
	g++-7 -std=c++14 -g mat.cc rref.o -o mat -lgmp -lflint -liml -lcblas # -lntl # -lgivaro -lgmp -lgmpxx -llinbox

rref.o: rref.cc
