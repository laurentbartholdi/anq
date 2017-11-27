/******************************************************************************
**
**                 Nilpotent Quotient for Lie Rings
** operations.c                                                 Csaba Schneider
**                                                           schcs@math.klte.hu
*/

#include "lienq.h"

/*
** The purpose of this couple of functions is to handle the Lie-algebra
** operations in the PC-presentation. There are 3 main operations i.e.
** a summation:        with respect to this the elements form an Abelian-group;
** a Lie product:      equipped with the usual Jacoby, anti-commutativity, and
**                     distributivity. It is stored in the Power[][] matrix.
** an integer-product: A module-operation of course. Makes no problem(?).
*/

/*
**  The following function writes a coeffvec in normal form i.e. cancels the
**  coefficients that are not allowed becausee of the power relations. The
**  result remains in <ev>.
*/

void Collect(coeffvec ev) {
  coeff mp;
  coeff_init(mp);
  for (unsigned i = 1; i <= NrTotalGens; i++) {
    if (!coeff_nz(Coefficients[i]))
      continue;
    coeff_fdiv_q(mp, ev[i], Coefficients[i]);
    if (coeff_nz(mp)) {
      coeff_submul(ev[i], mp, Coefficients[i]);
      for (constgpvec p = Power[i]; p->g != EOW; p++)
        coeff_addmul(ev[p->g], mp, p->c);
    }
  }
  coeff_clear(mp);
}

void ShrinkCollect(gpvec &v) {
  for (gpvec p = v; p->g != EOW; p++)
    if(!coeff_reduced_p(p->c, Coefficients[p->g])) {
      coeffvec cv = GpVecToCoeffVec(v);
      Collect(cv);
      FreeGpVec(v);
      v = CoeffVecToGpVec(cv);
      FreeCoeffVec(cv);
      break;
    }
}

void Collect(gpvec v0, constgpvec gv) {
  coeffvec cv;

  cv = GpVecToCoeffVec(gv);
  Collect(cv);
  CoeffVecToGpVec(v0,cv);
  FreeCoeffVec(cv);
}

#if 0
gpvec Collect(gpvec gv) {
  gpvec result = malloc(lots...);
  struct { coeff c; constgpvec p; } *queue = malloc(lots...);
  queue[0] = { 1, gv };
  int qlen = 1, gen  = 0;
  while (qlen > 0) {
    find minimum of all gens in queue; when one queue is exhausted, pop;
    sum all corresponding coefficients;
    if non-zero, reduce; and if non-trivial reduction, add power to queue;
    if non-zero, put in result;
  }
  return result;
}
#endif

/* v += x*w */
void Sum(coeffvec v, const coeff x, constgpvec w) {
  for (constgpvec p = w; p->g != EOW; p++)
    coeff_addmul(v[p->g], x, p->c);
}

/* v += w */
void Sum(coeffvec v, constgpvec w) {
  for (constgpvec p = w; p->g != EOW; p++)
    coeff_add(v[p->g], v[p->g], p->c);
}

/* v -= x*w */
void Diff(coeffvec v, const coeff x, constgpvec w) {
  for (constgpvec p = w; p->g != EOW; p++)
    coeff_submul(v[p->g], x, p->c);
}

/* v -= w */
void Diff(coeffvec v, constgpvec w) {
  for (constgpvec p; p->g != EOW; p++)
    coeff_sub(v[p->g], v[p->g], p->c);
}

/* vec0 = vec1 + vec2 */
void Sum(gpvec vec0, constgpvec vec1, constgpvec vec2) {
  for (constgpvec p1 = vec1, p2 = vec2;;) {
    if (p1->g == EOW) {
      while (p2->g != EOW) {
	coeff_set(vec0->c, p2->c), vec0->g = p2->g;
	vec0++;
	p2++;
      }
      goto done;
    }
    if (p2->g == EOW) {
      while (p1->g != EOW) {
	coeff_set(vec0->c, p1->c), vec0->g = p1->g;
	vec0++;
	p1++;
      }
      goto done;
    }
    if (p1->g < p2->g) {
      coeff_set(vec0->c, p1->c), vec0->g = p1->g;
      vec0++;
      p1++;
    } else if (p1->g > p2->g) {
	coeff_set(vec0->c, p2->c), vec0->g = p2->g;
	vec0++;
	p2++;
    } else {
      coeff c;
      coeff_add(c, p1->c, p2->c);
      if (coeff_nz(c))
	coeff_set(vec0->c, c), vec0->g = p1->g, vec0++;
      p1++;
      p2++;
    }
  }
 done:
  vec0->g = EOW;
  return;
}

/* vec0 = vec1 + x*vec2 */
unsigned Sum(gpvec vec0, constgpvec vec1, const coeff x, constgpvec vec2) {
  unsigned len = 0;
  if (!coeff_nz(x)) {
    for (constgpvec p1 = vec1; p1->g != EOW; p1++) {
      coeff_set(vec0[len].c, p1->c), vec0->g = p1->g;
      len++;
    }
    goto done;    
  }
  
  for (constgpvec p1 = vec1, p2 = vec2;;) {
    if (p1->g == EOW) {
      while (p2->g != EOW) {
	coeff_mul(vec0[len].c, x, p2->c), vec0[len].g = p2->g;
	len++;
	p2++;
      }
      goto done;
    }
    if (p2->g == EOW) {
      while (p1->g != EOW) {
	coeff_set(vec0[len].c, p1->c), vec0[len].g = p1->g;
	len++;
	p1++;
      }
      goto done;
    }
    if (p1->g < p2->g) {
      coeff_set(vec0[len].c, p1->c), vec0[len].g = p1->g;
      len++;
      p1++;
    } else if (p1->g > p2->g) {
      coeff_mul(vec0[len].c, x, p2->c), vec0[len].g = p2->g;
      len++;
      p2++;
    } else {
      coeff c;
      coeff_init_set(c, p1->c);
      coeff_addmul(c, x, p2->c);
      if (coeff_nz(c))
	coeff_set(vec0[len].c, c), vec0[len].g = p1->g, len++;
      coeff_clear(c);
      p1++;
      p2++;
    }
  }
 done:
  vec0[len].g = EOW;
  return len;
}

/* vec0 = vec1 - vec2 */
void Diff(gpvec vec0, constgpvec vec1, constgpvec vec2) {
  for (constgpvec p1 = vec1, p2 = vec2;;) {
    if (p1->g == EOW) {
      while (p2->g != EOW) {
	coeff_neg(vec0->c, p2->c), vec0->g = p2->g;
	vec0++;
	p2++;
      }
      goto done;
    }
    if (p2->g == EOW) {
      while (p1->g != EOW) {
	coeff_set(vec0->c, p1->c), vec0->g = p1->g;
	vec0++;
	p1++;
      }
      goto done;
    }
    if (p1->g < p2->g) {
      coeff_set(vec0->c, p1->c), vec0->g = p1->g;
      vec0++;
      p1++;
    } else if (p1->g > p2->g) {      
      coeff_neg(vec0->c, p2->c), vec0->g = p2->g;
      vec0++;
      p2++;
    } else {
      coeff c;
      coeff_sub(c, p1->c, p2->c);
      if (coeff_nz(c))
	coeff_set(vec0->c, c), vec0->g = p1->g, vec0++;
      p1++;
      p2++;
    }
  }
 done:
  vec0->g = EOW;
}

/* vec0 = vec1 - x*vec2 */
unsigned Diff(gpvec vec0, constgpvec vec1, const coeff x, constgpvec vec2) {
  if (!coeff_nz(x)) {
    unsigned len = 0;
    for (constgpvec p1 = vec1; p1->g != EOW; p1++) {
      coeff_set(vec0[len].c, p1->c), vec0[len].g = p1->g;
      len++;
    }
    vec0[len].g = EOW;
    return len;
  }

  coeff y;
  coeff_init(y);
  coeff_neg(y, x);
  unsigned len = Sum(vec0, vec1, y, vec2);
  coeff_clear(y);
  return len;
}

/* puts n * vec into vec */
void ModProd(const coeff n, gpvec vec) {
  for (; vec->g != EOW; vec++)
    coeff_mul(vec->c, vec->c, n);
}

/* puts -vec into vec */
void ModNeg(gpvec vec) {
  for(; vec->g != EOW; vec++)
    coeff_neg(vec->c, vec->c);
}

/* vec0 = [ vec1, vec2 ] */
void Prod(gpvec vec0, constgpvec vec1, constgpvec vec2) {
  gpvec temp[2];
  bool parity = 0;
  temp[0] = NewGpVec(NrTotalGens);
  temp[1] = NewGpVec(NrTotalGens);
  temp[0][0].g = EOW;
  coeff c;
  
  for (constgpvec p1 = vec1; p1->g != EOW; p1++)
    for (constgpvec p2 = vec2; p2->g != EOW; p2++)
      if (p1->g <= NrPcGens && p2->g <= NrPcGens && Weight[p1->g] + Weight[p2->g] <= Class) {
        if (p1->g > p2->g) {
	  coeff_mul(c, p1->c, p2->c);
	  Sum(temp[!parity], temp[parity], c, Product[p1->g][p2->g]);
	  parity ^= 1;
	} else if (p2->g > p1->g) {
	  coeff_mul(c, p1->c, p2->c);
	  coeff_neg(c, c);
	  Sum(temp[!parity], temp[parity], c, Product[p2->g][p1->g]);
	  parity ^= 1;
	}
      }
  CpVec(vec0, temp[parity]);
  free(temp[0]);
  free(temp[1]);
}

/* vec0 += [ vec1, vec2 ] */
void Prod(coeffvec vec0, constgpvec vec1, constgpvec vec2) {
  coeff c;
  coeff_init(c);
  
  for (constgpvec p1 = vec1; p1->g != EOW; p1++)
    for (constgpvec p2 = vec2; p2->g != EOW; p2++)
      if (p1->g <= NrPcGens && p2->g <= NrPcGens && Weight[p1->g] + Weight[p2->g] <= Class) {
        if (p1->g > p2->g) {
	  coeff_mul(c, p1->c, p2->c);
	  Sum(vec0, c, Product[p1->g][p2->g]);
	} else if (p2->g > p1->g) {
	  coeff_mul(c, p1->c, p2->c);
	  coeff_neg(c, c);
	  Sum(vec0, c, Product[p2->g][p1->g]);
	}
      }
  coeff_clear(c);
}
