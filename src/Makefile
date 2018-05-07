###############################################################################
##
##               Nilpotent Quotient for Lie Rings            
## Makefile                                                     Csaba Schneider
##                                                           schcs@math.klte.hu
##

LIENQVERSION = -DVERSION='"3.2.1 2018-05-02"'
OPT = -O0 #3
DEBUG = -g -ggdb
CXXFLAGS = -std=gnu++11 -Wall -Werror $(DEBUG) $(OPT)
CFLAGS = -Wall -Werror $(DEBUG) $(OPT)
LDFLAGS = $(DEBUG) -lcolamd -lgmp

## LieNQ prefers GNU C compiler.

ifeq ($(shell uname -s),Darwin)
    CC = g++-8
    CXX = g++-8
else
    CC = g++
    CXX = g++
endif

LIENQ_OBJ = fppresentation.o pcpresentation.o print.o operations.o matrix.o consistency.o tails.o auxiliary.o lienq.o

all: lienq_2_64 lienq_2_320 lienq_3_39 lienq_5_27 lienq_5_100 lienq_long lienq_mpz

clean:
	rm -fr *.o lienq_[0-9]*_[0-9]* lienq_mpz lienq_long lienq_z *.dSYM

lienq_mpz: $(subst .o,_mpz.o,$(LIENQ_OBJ))

%_mpz.o: %.cc lienq.h coeff.h coeff_mpz.h
	$(CXX) -c -DCOEFF_IS_MPZ $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_z: $(subst .o,_z.o,$(LIENQ_OBJ))
	$(CXX) -o $@ $^ -lgmp

%_z.o: %.cc lienq.h coeff.h coeff_z.h
	$(CXX) -c -DCOEFF_IS_Z $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_long: $(subst .o,_long.o,$(LIENQ_OBJ))

%_long.o: %.cc lienq.h coeff.h coeff_long.h
	$(CXX) -c -DCOEFF_IS_LONG $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_2_3: $(subst .o,_2_3.o,$(LIENQ_OBJ))

%_2_3.o: %.cc lienq.h coeff.h coeff_2_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=3 $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_2_63: $(subst .o,_2_63.o,$(LIENQ_OBJ))

%_2_63.o: %.cc lienq.h coeff.h coeff_2_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=63 $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_2_64: $(subst .o,_2_64.o,$(LIENQ_OBJ))

%_2_64.o: %.cc lienq.h coeff.h coeff_2_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_2_257: $(subst .o,_2_257.o,$(LIENQ_OBJ))

%_2_257.o: %.cc lienq.h coeff.h coeff_2_mp.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=257 $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_2_320: $(subst .o,_2_320.o,$(LIENQ_OBJ))

%_2_320.o: %.cc lienq.h coeff.h coeff_2_mp.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=320 $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_3_38: $(subst .o,_3_38.o,$(LIENQ_OBJ))

%_3_38.o: %.cc lienq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=3 -DMODULUS_EXPONENT=38 $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_3_39: $(subst .o,_3_39.o,$(LIENQ_OBJ))

%_3_39.o: %.cc lienq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=3 -DMODULUS_EXPONENT=39 $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_5_26: $(subst .o,_5_26.o,$(LIENQ_OBJ))

%_5_26.o: %.cc lienq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=26 $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_5_27: $(subst .o,_5_27.o,$(LIENQ_OBJ))

%_5_27.o: %.cc lienq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=27 $(CXXFLAGS) $(LIENQVERSION) $< -o $@

lienq_5_100: $(subst .o,_5_100.o,$(LIENQ_OBJ))

%_5_100.o: %.cc lienq.h coeff.h coeff_p_mp.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=100 $(CXXFLAGS) $(LIENQVERSION) $< -o $@

coeff_test: coeff_test.cc coeff.h coeff_2_k.h coeff_p_k.h coeff_2_mp.h coeff_p_mp.h
	$(CXX) -o $@ coeff_test.cc -lgmp

test: test.cc

test.s: test.cc
	g++-7 -O3 -march=native -std=c++11 -S $< -o $@

rips: rips.cc rref.o
	g++-7 -g rips.cc rref.o -o rips -lgmp -lflint -liml -lcblas

mat: mat.cc rref.o
	g++-7 -std=c++14 -g mat.cc rref.o -o mat -lgmp -lflint -liml -lcblas # -lntl # -lgivaro -lgmp -lgmpxx -llinbox

rref.o: rref.cc
