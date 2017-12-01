###############################################################################
##
##               Nilpotent Quotient for Lie Rings            
## Makefile                                                     Csaba Schneider
##                                                           schcs@math.klte.hu
##

# CPPFLAGS = -DVERSION='"3.0 2017-11-24"' -DCOEFF_IS_MPZ
# CPPFLAGS = -DVERSION='"3.0 2017-11-24"' -DCOEFF_IS_Z
# CPPFLAGS = -DVERSION='"3.0 2017-11-24"' -DCOEFF_IS_MODp_k -DBASEMODULUS=3 -DLOGMODULUS=4 -DMODULUS=81
CPPFLAGS = -DVERSION='"3.0 2017-11-27"' -DCOEFF_IS_MOD2_64
# CPPFLAGS = -DVERSION='"3.0 2017-11-27"' -DCOEFF_IS_LONG
OPT = -O0
DEBUG = -g -ggdb
CXXFLAGS = -std=c++11 -Wall -Werror $(DEBUG) $(OPT)
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

lienq: $(LIENQ_OBJ)

clean:
	rm -f $(LIENQ_OBJ) lienq

addgen.o: addgen.C $(LIENQ_INCLUDES)  

auxiliary.o: auxiliary.C $(LIENQ_INCLUDES)  

consistency.o: consistency.C $(LIENQ_INCLUDES)

epim.o: epim.C $(LIENQ_INCLUDES)

lienq.o: lienq.C $(LIENQ_INCLUDES)

matrix.o: matrix.C $(LIENQ_INCLUDES)

operations.o: operations.C $(LIENQ_INCLUDES)  

presentation.o: presentation.C $(LIENQ_INCLUDES)

print.o: print.C $(LIENQ_INCLUDES)  

readpres.o: readpres.C $(LIENQ_INCLUDES)

tails.o: tails.C $(LIENQ_INCLUDES)

test: test.C
