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

/****************************************************************
 vector addition and scalar multiplication
****************************************************************/
/* vec0 = vec1 + vec2 */
void Sum(gpvec vec0, constgpvec vec1, constgpvec vec2) {
  for (;;) {
    if (vec1->g == EOW) {
      Copy(vec0, vec2);
      return;
    }
    if (vec2->g == EOW) {
      Copy(vec0, vec1);
      return;
    }
    if (vec1->g < vec2->g) {
      coeff_set(vec0->c, vec1->c), vec0->g = vec1->g;
      vec0++;
      vec1++;
    } else if (vec1->g > vec2->g) {
      coeff_set(vec0->c, vec2->c), vec0->g = vec2->g;
      vec0++;
      vec2++;
    } else {
      coeff_add(vec0->c, vec1->c, vec2->c);
      if (coeff_nz(vec0->c))
	vec0->g = vec1->g, vec0++;
      vec1++;
      vec2++;
    }
  }
}

/* vec0 = vec1 + x2*vec2 */
void Sum(gpvec vec0, constgpvec vec1, const coeff x2, constgpvec vec2) {
  if (!coeff_nz(x2)) {
    Copy(vec0, vec1);
    return;
  }
  
  for (;;) {
    if (vec1->g == EOW) {
      Prod(vec0, x2, vec2);
      return;
    }
    if (vec2->g == EOW) {
      Copy(vec0, vec1);
      return;
    }
    if (vec1->g < vec2->g) {
      coeff_set(vec0->c, vec1->c), vec0->g = vec1->g;
      vec0++;
      vec1++;
    } else if (vec1->g > vec2->g) {
      coeff_mul(vec0->c, x2, vec2->c);
      if (coeff_nz(vec0->c))
	vec0->g = vec2->g, vec0++;
      vec2++;
    } else {
      coeff_set(vec0->c, vec1->c);
      coeff_addmul(vec0->c, x2, vec2->c);
      if (coeff_nz(vec0->c))
	vec0->g = vec1->g, vec0++;
      vec1++;
      vec2++;
    }
  }
}

/* vec0 = x1*vec1 + x2*vec2 */
void Sum(gpvec vec0, const coeff x1, constgpvec vec1, const coeff x2, constgpvec vec2) {
  if (!coeff_nz(x1)) {
    Prod(vec0, x2, vec2);
    return;
  }
  if (!coeff_nz(x2)) {
    Prod(vec0, x1, vec1);
    return;
  }
  
  for (;;) {
    if (vec1->g == EOW) {
      Prod(vec0, x2, vec2);
      return;
    }
    if (vec2->g == EOW) {
      Prod(vec0, x1, vec1);
      return;
    }
    if (vec1->g < vec2->g) {
      coeff_mul(vec0->c, x1, vec1->c);
      if (coeff_nz(vec0->c))
	vec0->g = vec1->g, vec0++;
      vec1++;
    } else if (vec1->g > vec2->g) {
      coeff_mul(vec0->c, x2, vec2->c);
      if (coeff_nz(vec0->c))
	vec0->g = vec2->g, vec0++;
      vec2++;
    } else {
      coeff_mul(vec0->c, x1, vec1->c);
      coeff_addmul(vec0->c, x2, vec2->c);
      if (coeff_nz(vec0->c))
	vec0->g = vec1->g, vec0++;
      vec1++;
      vec2++;
    }
  }
}

/* vec0 = vec1 - vec2 */
void Diff(gpvec vec0, constgpvec vec1, constgpvec vec2) {
  for (;;) {
    if (vec1->g == EOW) {
      Neg(vec0, vec2);
      return;
    }
    if (vec2->g == EOW) {
      Copy(vec0, vec1);
      return;
    }
    if (vec1->g < vec2->g) {
      coeff_set(vec0->c, vec1->c), vec0->g = vec1->g;
      vec0++;
      vec1++;
    } else if (vec1->g > vec2->g) {
      coeff_neg(vec0->c, vec2->c), vec0->g = vec2->g;
      vec0++;
      vec2++;
    } else {
      coeff_sub(vec0->c, vec1->c, vec2->c);
      if (coeff_nz(vec0->c))
	vec0->g = vec1->g, vec0++;
      vec1++;
      vec2++;
    }
  }
}

/****************************************************************
 Lie bracket of vectors

 this could be very inefficient the way it's implemented:
 if vec1 and vec2 are almost full vectors (of length N), and each
 Product[] entry is a short vector (of length n), then we have
 complexity O(N^3) while we could achieve O(N^2n) in theory.

 it would be better to do this with a container storing all
 coefficients of all sums of Product[]s, and reading the results from
 there into vec0.
****************************************************************/
/* vec0 = [ vec1, vec2 ] */
void Prod(gpvec vec0, constgpvec vec1, constgpvec vec2) {
  gpvec temp[2];
  bool parity = false;
  temp[0] = FreshVec();
  temp[1] = FreshVec();
  coeff c;
  coeff_init(c);
  
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
  Copy(vec0, temp[parity]);
  PopVec();
  PopVec();
}

/* the main collection routine. It could be optimized:
   if all Power relations have length n, and gv is full of length N,
   then the complexity is O(N^3) rather than O(N^2 n).

   We should do it with a container such as <map>
*/
void Collect(gpvec vec0, constgpvec v) {
  gpvec temp[2], p;
  temp[0] = FreshVec();
  temp[1] = FreshVec();
  bool parity = false;
  coeff mp;
  coeff_init(mp);
  
  for (p = (gpvec) v; p->g != EOW;) {
    gen i = p->g;
    if(coeff_reduced_p(p->c, Coefficients[i])) {
      coeff_set(vec0->c, p->c), vec0->g = i;
      vec0++;
      p++;
    } else {
      coeff_fdiv_q(mp, p->c, Coefficients[i]);
      coeff_set(vec0->c, p->c);
      coeff_submul(vec0->c, mp, Coefficients[i]);
      if (coeff_nz(vec0->c))
	vec0->g = i, vec0++;
      p++;
      if (Power[i]->g != EOW) {
	Sum(temp[!parity], p, mp, Power[i]);
	parity ^= 1;
	p = temp[parity];
      }
    }
  }
  vec0->g = EOW;
  PopVec();
  PopVec();
  coeff_clear(mp);
}

void ShrinkCollect(gpvec &v) {
  gpvec newv = NewVec(NrTotalGens);
  Collect(newv, v);
  FreeVec(v);
  v = ResizeVec(newv);
}

#if 0
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
#endif
