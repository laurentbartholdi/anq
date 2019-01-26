###############################################################################
##
##               Nilpotent Quotient for Lie Rings            
## Makefile                                                     Csaba Schneider
##                                                           schcs@math.klte.hu
##

NQVERSION = -DVERSION='"3.2.1 2018-05-02"'
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

LIENQ_OBJ = fppresentation.o pcpresentation.o print.o operations.o matrix.o consistency.o tails.o auxiliary.o nq.o

all: lienq_2_64 lienq_2_320 lienq_3_39 lienq_5_27 lienq_5_100 lienq_long lienq_mpz gpnq_2_64 gpnq_2_320 gpnq_3_39 gpnq_5_27 gpnq_5_100 gpnq_long gpnq_mpz

clean:
	rm -fr *.o lienq_[0-9]*_[0-9]* lienq_mpz lienq_long lienq_z *.dSYM

lienq_mpz: $(subst .o,_lie_mpz.o,$(LIENQ_OBJ))

%_lie_mpz.o: %.cc nq.h coeff.h coeff_mpz.h
	$(CXX) -c -DCOEFF_IS_MPZ -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

lienq_z: $(subst .o,_lie_z.o,$(LIENQ_OBJ))

%_lie_z.o: %.cc nq.h coeff.h coeff_z.h
	$(CXX) -c -DCOEFF_IS_Z -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

lienq_long: $(subst .o,_lie_long.o,$(LIENQ_OBJ))

%_lie_long.o: %.cc nq.h coeff.h coeff_long.h
	$(CXX) -c -DCOEFF_IS_LONG -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

lienq_2_3: $(subst .o,_lie_2_3.o,$(LIENQ_OBJ))

%_lie_2_3.o: %.cc nq.h coeff.h coeff_2_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=3 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

lienq_2_63: $(subst .o,_lie_2_63.o,$(LIENQ_OBJ))

%_lie_2_63.o: %.cc nq.h coeff.h coeff_2_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=63 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

lienq_2_64: $(subst .o,_lie_2_64.o,$(LIENQ_OBJ))

%_lie_2_64.o: %.cc nq.h coeff.h coeff_2_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

lienq_2_257: $(subst .o,_lie_2_257.o,$(LIENQ_OBJ))

%_lie_2_257.o: %.cc nq.h coeff.h coeff_2_mp.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=257 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

lienq_2_320: $(subst .o,_lie_2_320.o,$(LIENQ_OBJ))

%_lie_2_320.o: %.cc nq.h coeff.h coeff_2_mp.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=320 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

lienq_3_38: $(subst .o,_lie_3_38.o,$(LIENQ_OBJ))

%_lie_3_38.o: %.cc nq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=3 -DMODULUS_EXPONENT=38 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

lienq_3_39: $(subst .o,_lie_3_39.o,$(LIENQ_OBJ))

%_lie_3_39.o: %.cc nq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=3 -DMODULUS_EXPONENT=39 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

lienq_5_26: $(subst .o,_lie_5_26.o,$(LIENQ_OBJ))

%_lie_5_26.o: %.cc nq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=26 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

lienq_5_27: $(subst .o,_lie_5_27.o,$(LIENQ_OBJ))

%_lie_5_27.o: %.cc nq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=27 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

lienq_5_100: $(subst .o,_lie_5_100.o,$(LIENQ_OBJ))

%_lie_5_100.o: %.cc nq.h coeff.h coeff_p_mp.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=100 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

gpnq_mpz: $(subst .o,_gp_mpz.o,$(LIENQ_OBJ))

%_gp_mpz.o: %.cc nq.h coeff.h coeff_mpz.h
	$(CXX) -c -DCOEFF_IS_MPZ -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

gpnq_z: $(subst .o,_gp_z.o,$(LIENQ_OBJ))

%_gp_z.o: %.cc nq.h coeff.h coeff_z.h
	$(CXX) -c -DCOEFF_IS_Z -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

gpnq_long: $(subst .o,_gp_long.o,$(LIENQ_OBJ))

%_gp_long.o: %.cc nq.h coeff.h coeff_long.h
	$(CXX) -c -DCOEFF_IS_LONG -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

gpnq_2_3: $(subst .o,_gp_2_3.o,$(LIENQ_OBJ))

%_gp_2_3.o: %.cc nq.h coeff.h coeff_2_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=3 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

gpnq_2_63: $(subst .o,_gp_2_63.o,$(LIENQ_OBJ))

%_gp_2_63.o: %.cc nq.h coeff.h coeff_2_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=63 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

gpnq_2_64: $(subst .o,_gp_2_64.o,$(LIENQ_OBJ))

%_gp_2_64.o: %.cc nq.h coeff.h coeff_2_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

gpnq_2_257: $(subst .o,_gp_2_257.o,$(LIENQ_OBJ))

%_gp_2_257.o: %.cc nq.h coeff.h coeff_2_mp.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=257 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

gpnq_2_320: $(subst .o,_gp_2_320.o,$(LIENQ_OBJ))

%_gp_2_320.o: %.cc nq.h coeff.h coeff_2_mp.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=320 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

gpnq_3_38: $(subst .o,_gp_3_38.o,$(LIENQ_OBJ))

%_gp_3_38.o: %.cc nq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=3 -DMODULUS_EXPONENT=38 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

gpnq_3_39: $(subst .o,_gp_3_39.o,$(LIENQ_OBJ))

%_gp_3_39.o: %.cc nq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=3 -DMODULUS_EXPONENT=39 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

gpnq_5_26: $(subst .o,_gp_5_26.o,$(LIENQ_OBJ))

%_gp_5_26.o: %.cc nq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=26 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

gpnq_5_27: $(subst .o,_gp_5_27.o,$(LIENQ_OBJ))

%_gp_5_27.o: %.cc nq.h coeff.h coeff_p_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=27 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

gpnq_5_100: $(subst .o,_gp_5_100.o,$(LIENQ_OBJ))

%_gp_5_100.o: %.cc nq.h coeff.h coeff_p_mp.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=100 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

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
