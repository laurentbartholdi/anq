###############################################################################
##
##               Any Nilpotent Quotients

TRIO = trio-1.16
NQVERSION = -DVERSION='"5.0.1 2022-11-18"'
OPT = -march=native -Ofast # -O0 # for debugging
DEBUG = # -g -fsanitize=address 
CFLAGS = -Wall -Werror -I$(TRIO) $(DEBUG) $(OPT)
CXXFLAGS = -std=c++11 $(CFLAGS)
LDFLAGS = $(DEBUG) -L$(TRIO)
LDLIBS = -lcolamd -lgmp -ltrio

ifeq ($(shell uname -s),Darwin)
  LDFLAGS += -Wl,-no_pie
else
  CXXFLAGS += -I/usr/include/suitesparse
endif

ifeq ($(shell hostname -s),laurent-mbp) # private settings
  CXX=/usr/bin/clang++
endif

ifndef COEFF
COEFF = integer<0,1>
endif

# prevent automatic deletion
.SECONDARY:

NQ_OBJ := fppresentation.o pcpresentation.o operations.o matrix.o nq.o
NQ_INCL := nq.h ring.hh r_*.hh vectors.hh

all: trio nq_a nq_l nq_g

coverage_nql:
	$(MAKE) -B OPT=-march=native CXX=clang++ DEBUG="-g -fprofile-instr-generate -fcoverage-mapping" nq_l nq_g nq_a

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
	rm -fr *.o *.gc?? nq_[lga]_[0-9]*_[0-9]* nq_[lga] *.dSYM $(TRIO)/libtrio.a

nq_l: $(subst .o,_l.o,$(NQ_OBJ))

%_l.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF="$(COEFF)" -DLIEALG $(CXXFLAGS) $(NQVERSION) $< -o $@

nq_g: $(subst .o,_g.o,$(NQ_OBJ))

%_g.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF="$(COEFF)" -DGROUP $(CXXFLAGS) $(NQVERSION) $< -o $@

nq_a: $(subst .o,_a.o,$(NQ_OBJ))

%_a.o: %.cc $(NQ_INCL)
	$(CXX) -c -DCOEFF="$(COEFF)" -DASSOCALG $(CXXFLAGS) $(NQVERSION) $< -o $@

.SECONDEXPANSION:

%.o: $$(word 1,$$(subst _, ,$$*)).cc $(NQ_INCL)
	$(if $(findstring $(word 2,$(subst _, ,$*)),lga),,$(error l or g or a required in stem of $*))
	$(CXX) -c -DPCCOEFF_P=$(word 3,$(subst _, ,$*)) -DPCCOEFF_K=$(word 4,$(subst _, ,$*)) -DMATCOEFF_P=$(if $(word 5,$(subst _, ,$*)),$(word 5,$(subst _, ,$*)),$(word 3,$(subst _, ,$*))) -DMATCOEFF_K=$(if $(word 5,$(subst _, ,$*)),$(word 6,$(subst _, ,$*)),$(word 4,$(subst _, ,$*))) -D$(if $(findstring $(word 2,$(subst _, ,$*)),l),LIEALG,$(if $(findstring $(word 2,$(subst _, ,$*)),g),GROUP,ASSOCALG)) $(CXXFLAGS) $(NQVERSION) $< -o $@

nq_%: trio $$(subst .o,_%.o,$(NQ_OBJ))
	$(CXX) -o $@ $(CXXFLAGS) $(LDFLAGS) $(filter-out $<,$^) $(LOADLIBES) $(LDLIBS)

################################################################
# the following are unused targets, used for testing / experimenting

test: test.cc

test.s: test.cc
	g++-7 -O3 -march=native -std=c++11 -S $< -o $@

rips: rips.cc rref.o
	g++-7 -g rips.cc rref.o -o rips -lgmp -lflint -liml -lcblas

mat: mat.cc rref.o
	g++-7 -std=c++14 -g mat.cc rref.o -o mat -lgmp -lflint -liml -lcblas # -lntl # -lgivaro -lgmp -lgmpxx -llinbox

rref.o: rref.cc
