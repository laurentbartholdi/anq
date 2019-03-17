###############################################################################
##
##               Nilpotent Quotient for Lie Rings            
## Makefile                                                     Csaba Schneider
##                                                           schcs@math.klte.hu
##

TRIO = trio-1.16
NQVERSION = -DVERSION='"4.0.0 2019-02-26"'
OPT = -march=native -O0 #-Ofast
DEBUG = -g -fsanitize=address 
CFLAGS = -Wall -Werror -I$(TRIO) $(DEBUG) $(OPT)
CXXFLAGS = -std=gnu++11 $(CFLAGS)
LDFLAGS = $(DEBUG) -L$(TRIO) -lcolamd -lgmp -ltrio -Wl,-no_pie

CXX=g++
CC=$(CXX)

NQ_OBJ = fppresentation.o pcpresentation.o operations.o matrix.o nq.o
NQ_INCL = nq.h ring.hh vectors.hh

all: trio nql_2_64 nql_2_320 nql_3_39 nql_5_27 nql_5_100 nql_long nql_mpz \
	nqg_2_64 nqg_2_320 nqg_3_39 nqg_5_27 nqg_5_100 nqg_long nqg_mpz

nql: trio nql_long nql_2_64 nql_mpz

nqg: trio nqg_long nqg_2_64 nqg_mpz

coverage_nql:
	$(MAKE) -B OPT=-march=native CXX=clang++ DEBUG="-g -fprofile-instr-generate -fcoverage-mapping" nql nqg

# then use as follows:
# % LLVM_PROFILE_FILE="nq.profraw" ./nql_long ...
# % llvm-profdata merge -sparse nq.profraw -o nq.profdata
# % llvm-cov show -format=html ./nql_long -instr-profile=nq.profdata > coverage.html
# % llvm-cov report ./nql_long -instr-profile=nq.profdata

trio: $(TRIO)/libtrio.a

$(TRIO)/libtrio.a:
	(cd $(TRIO); ./configure)
	make -C $(TRIO) libtrio.a

coverage: clean
	$(MAKE) CXX=g++ DEBUG="-g -fprofile-instr-generate -fcoverage-mapping"

runcoverage:

viewcoverage:
	llvm-profdata merge -o default.profdata default.profraw
	llvm-cov show ./nql_long -instr-profile=default.profdata $(NAME)

profile: clean
	$(MAKE) CXX=g++ DEBUG="-g" OPT="-Ofast" LDFLAGS+="-lprofiler" nqg_2_64

runprofile:
	CPUPROFILE=nqg_2_64.prof CPUPROFILE_FREQUENCY=10000 ./nqg_2_64 -W40 p/gg
	pprof --pdf --nodecount=20 ./nqg_2_64 ./nqg_2_64.prof > profile.pdf

clean:
	rm -fr *.o *.gc?? nq[lg]_[0-9]*_[0-9]* nq[lg]_mpz nq[lg]_long nq[lg]_z *.dSYM

nql_mpz: $(subst .o,l_mpz.o,$(NQ_OBJ))

%l_mpz.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_MPZ -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_z: $(subst .o,l_z.o,$(NQ_OBJ))

%l_z.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_Z -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_long: $(subst .o,l_long.o,$(NQ_OBJ))

%l_long.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_LONG -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_2_3: $(subst .o,l_2_3.o,$(NQ_OBJ))

%l_2_3.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=3 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_2_63: $(subst .o,l_2_63.o,$(NQ_OBJ))

%l_2_63.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=63 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_2_64: $(subst .o,l_2_64.o,$(NQ_OBJ))

%l_2_64.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_2_257: $(subst .o,l_2_257.o,$(NQ_OBJ))

%l_2_257.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=257 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_2_320: $(subst .o,l_2_320.o,$(NQ_OBJ))

%l_2_320.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=320 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_3_38: $(subst .o,l_3_38.o,$(NQ_OBJ))

%l_3_38.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=3 -DMODULUS_EXPONENT=38 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_3_39: $(subst .o,l_3_39.o,$(NQ_OBJ))

%l_3_39.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=3 -DMODULUS_EXPONENT=39 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_5_26: $(subst .o,l_5_26.o,$(NQ_OBJ))

%l_5_26.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=26 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_5_27: $(subst .o,l_5_27.o,$(NQ_OBJ))

%l_5_27.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=27 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_5_100: $(subst .o,l_5_100.o,$(NQ_OBJ))

%l_5_100.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=100 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_mpz: $(subst .o,g_mpz.o,$(NQ_OBJ))

%g_mpz.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_MPZ -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_z: $(subst .o,g_z.o,$(NQ_OBJ))

%g_z.o: %.cc $(NQ_INCL) coeff_z.h
	$(CXX) -c -DCOEFF_IS_Z -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_long: $(subst .o,g_long.o,$(NQ_OBJ))

%g_long.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_LONG -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_2_3: $(subst .o,g_2_3.o,$(NQ_OBJ))

%g_2_3.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=3 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_2_63: $(subst .o,g_2_63.o,$(NQ_OBJ))

%g_2_63.o: %.cc $(NQ_INCL) coeff_2_k.h
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=63 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_2_64: $(subst .o,g_2_64.o,$(NQ_OBJ))

%g_2_64.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_2_257: $(subst .o,g_2_257.o,$(NQ_OBJ))

%g_2_257.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=257 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_2_320: $(subst .o,g_2_320.o,$(NQ_OBJ))

%g_2_320.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=2 -DMODULUS_EXPONENT=320 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_3_38: $(subst .o,g_3_38.o,$(NQ_OBJ))

%g_3_38.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=3 -DMODULUS_EXPONENT=38 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_3_39: $(subst .o,g_3_39.o,$(NQ_OBJ))

%g_3_39.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=3 -DMODULUS_EXPONENT=39 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_5_26: $(subst .o,g_5_26.o,$(NQ_OBJ))

%g_5_26.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=26 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_5_27: $(subst .o,g_5_27.o,$(NQ_OBJ))

%g_5_27.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF_IS_pADIC -DMODULUS_PRIME=5 -DMODULUS_EXPONENT=27 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_5_100: $(subst .o,g_5_100.o,$(NQ_OBJ))

%g_5_100.o: %.cc $(NQ_INCL)
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
