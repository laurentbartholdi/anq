###############################################################################
##
##               Nilpotent Quotient for Lie Rings            
## Makefile                                                     Csaba Schneider
##                                                           schcs@math.klte.hu
##

TRIO = trio-1.16
NQVERSION = -DVERSION='"4.0.1 2019-03-22"'
OPT = -march=native -O0 #-Ofast
DEBUG = -g -fsanitize=address 
CFLAGS = -Wall -Werror -I$(TRIO) $(DEBUG) $(OPT)
CXXFLAGS = -std=c++11 $(CFLAGS)
LDFLAGS = $(DEBUG) -L$(TRIO) -lcolamd -lgmp -ltrio -Wl,-no_pie $(LDEXTRA)

CXX=g++
CC=$(CXX)

ifndef COEFF
COEFF = integer<0,1>
endif

NQ_OBJ = fppresentation.o pcpresentation.o operations.o matrix.o nq.o
NQ_INCL = nq.h ring.hh r_*.hh vectors.hh

all: trio nql nqg

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

profile:
	$(MAKE) -B CXX=g++ DEBUG="-g" OPT="-Ofast" LDEXTRA="-lprofiler" nqg_2_2

runprofile:
	CPUPROFILE=nqg_2_2.prof CPUPROFILE_FREQUENCY=10000 ./nqg_2_2 -W40 p/gg
	pprof --pdf --nodecount=20 ./nqg_2_2 ./nqg_2_2.prof > profile.pdf

clean:
	rm -fr *.o *.gc?? nq[lg]_[0-9]*_[0-9]* nq[lg]_mpz nq[lg]_long nq[lg]_z *.dSYM

nql: $(subst .o,l.o,$(NQ_OBJ))

%l.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF="$(COEFF)" -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg: $(subst .o,g.o,$(NQ_OBJ))

%g.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF="$(COEFF)" -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_64: $(subst .o,l_64.o,$(NQ_OBJ))

%l_64.o: %.cc $(NQ_INCL)
	$(CXX) -c -DPCCOEFF_P=0 -DPCCOEFF_K=1 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_64: $(subst .o,g_64.o,$(NQ_OBJ))

%g_64.o: %.cc $(NQ_INCL)
	$(CXX) -c -DPCCOEFF_P=0 -DPCCOEFF_K=1 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_mpz: $(subst .o,l_mpz.o,$(NQ_OBJ))

%l_mpz.o: %.cc $(NQ_INCL)
	$(CXX) -c -DPCCOEFF_P=0 -DPCCOEFF_K=0 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_mpz: $(subst .o,g_mpz.o,$(NQ_OBJ))

%g_mpz.o: %.cc $(NQ_INCL)
	$(CXX) -c -DPCCOEFF_P=0 -DPCCOEFF_K=0 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_big: $(subst .o,g_big.o,$(NQ_OBJ))

%g_big.o: %.cc $(NQ_INCL)
	$(CXX) -c -DPCCOEFF_P=0 -DPCCOEFF_K=3 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_65521: $(subst .o,g_65521.o,$(NQ_OBJ))

%g_65521.o: %.cc $(NQ_INCL)
	$(CXX) -c -DPCCOEFF_P=65521 -DPCCOEFF_K=1 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_2_64: $(subst .o,l_2_64.o,$(NQ_OBJ))

%l_2_64.o: %.cc $(NQ_INCL)
	$(CXX) -c -DPCCOEFF_P=2 -DPCCOEFF_K=64 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_2_64: $(subst .o,g_2_64.o,$(NQ_OBJ))

%g_2_64.o: %.cc $(NQ_INCL)
	$(CXX) -c -DPCCOEFF_P=2 -DPCCOEFF_K=64 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_2_1: $(subst .o,l_2_1.o,$(NQ_OBJ))

%l_2_1.o: %.cc $(NQ_INCL)
	$(CXX) -c -DPCCOEFF_P=2 -DPCCOEFF_K=1 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_2_1: $(subst .o,g_2_1.o,$(NQ_OBJ))

%g_2_1.o: %.cc $(NQ_INCL)
	$(CXX) -c -DPCCOEFF_P=2 -DPCCOEFF_K=64 -DMATCOEFF_K=1 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nql_3_1: $(subst .o,l_3_1.o,$(NQ_OBJ))

%l_3_1.o: %.cc $(NQ_INCL)
	$(CXX) -c -DPCCOEFF_P=3 -DPCCOEFF_K=1 -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nqg_3_1: $(subst .o,g_3_1.o,$(NQ_OBJ))

%g_3_1.o: %.cc $(NQ_INCL)
	$(CXX) -c -DPCCOEFF_P=3 -DPCCOEFF_K=40 -DMATCOEFF_K=1 -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

test: test.cc

test.s: test.cc
	g++-7 -O3 -march=native -std=c++11 -S $< -o $@

rips: rips.cc rref.o
	g++-7 -g rips.cc rref.o -o rips -lgmp -lflint -liml -lcblas

mat: mat.cc rref.o
	g++-7 -std=c++14 -g mat.cc rref.o -o mat -lgmp -lflint -liml -lcblas # -lntl # -lgivaro -lgmp -lgmpxx -llinbox

rref.o: rref.cc
