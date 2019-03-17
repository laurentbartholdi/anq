#include "../ring.hh"
#include <stdio.h>

template<uint64_t P, unsigned K> void testP() {
  integer<P,K> x, y, z;
  
  printf("%s: size=%ld...", x.COEFF_ID(), sizeof x);
  if (!std::is_trivial<decltype(x)>::value) printf(" std::is_trivial failed");
  if (!std::is_standard_layout<decltype(x)>::value) printf(" std::is_standard_layout failed");

  x.set_si(x.hash());
  x.zero();
  if (x.nz_p()) printf(" 0.nz_p() failed");
  if (!x.z_p()) printf(" 0.z_p() failed");
  y.set_si(1);
  if (!x.reduced_p(y)) printf(" 0.reduced_p(1) failed");
  x.set(y); if (x.reduced_p(y)) printf(" 1.reduced_p(1) failed");
  y.add(y,x); if (x.cmp(y) == 0) printf(" 1.cmp(2) failed");
  y.add_si(y,-3); if (y.cmp_si(-1) != 0) printf(" -1.cmp(-1) failed");
  x.addmul(x,y); if (!x.z_p()) printf(" addmul failed");
  x.set_si(6);
  y.set_si(2);
  if (y.nz_p()) {
    z.divexact(x,y); if (z.cmp_si(3)) printf(" divexact failed");
    x.set_si(-55);
    y.set_si(17);
    z.fdiv_q(x,y);
    z.fdiv_r(x,y);
    fdiv_qr(x,z,x,y); if (z.nz_p()) printf(" fdiv_qr.r failed");
    z.addmul(x,y); if (z.cmp_si(-55)) printf(" fdiv_qr.q failed");
  }
  if (K > 1) {
    x.set_si(P*P+P+1);
    if (fdiv_qr_ui(y,z,x,P) != 1 || z.cmp_si(1)) printf(" fdiv_qr_ui.r failed");
    z.mul_si(y,P); if (z.cmp_si(P*P+P)) printf(" fdiv_qr.ui.q failed");
    y.set_si(P);
    shdiv_qr(x,y,x,y); if (y.cmp_si(1)) printf(" shdiv_qr.r failed");
    z.mul_si(x,P); if (z.cmp_si(P*P+P)) printf(" shdiv_qr.q failed");
    x.set_si(7*P+1);
    if (shdiv_qr_ui(x,y,x,P) != 1) printf(" shdiv_qr_ui failed");
    z.mul_si(x,P); if (z.cmp_si(7*P)) printf(" shdiv_qr_ui.q failed");
    if (y.cmp_si(1)) printf(" shdiv_qr_ui.r failed");
  }
  x.set_si(-17);
  y.inv(x); y.mul(y,x); if (y.cmp_si(1)) printf(" inv or mul failed");
  z.mul_si(x,-2); if (z.cmp_si(34)) printf(" mul_si failed");
  z.set_si(2);
  y.submul(y,z); if (y.cmp_si(-1)) printf(" submul failed");
  y.sub(y,y); if (y.nz_p()) printf(" sub failed");
  if (K > 1) {
    x.set_si(17*P);
    if (y.val(x) != 1) printf(" val.v failed");
    y.mul_si(y,P); if (y.cmp_si(17*P)) printf(" val.q failed");
  }
  if (K > 2) {
    x.set_si(7*P*P);
    if (y.val(x) != 2) printf(" val.v failed");
    y.mul_si(y,P*P); if (y.cmp_si(7*P*P)) printf(" val.q failed");
  }

  // some harder tests
  {
    integer<P,K> data[100];

    for (int i = 0; i < 25; i++)
      data[i].set_si(12-i);
    for (unsigned i = 25; i < 50; i++) {
      data[i].set_si(1+P*i);
      data[i].inv(data[i]);
    }
    for (unsigned i = 50; i < 100; i++)
      data[i].fdiv_q(data[i-50], data[19]); // divide by 7

    for (int i = 0; i < 25; i++)
      if (data[i].cmp_si(12-i))
	printf(" set/cmp failed at %u", i);
      
    for (unsigned i = 0; i < 100; i++)
      for (unsigned j = 0; j < 100; j++) {
	integer<P,K> s, t;
	s.add(data[i], data[j]);
	t.add(data[j], data[i]);
	if (s != t) printf( " add failed at (%u,%u)", i, j);
	s -= data[i];
	if (s != data[j]) printf( " -= failed at (%u,%u)", i, j);
      }

    for (unsigned i = 0; i < 100; i++)
      for (unsigned j = 0; j < 100; j++) {
	integer<P,K> g, s, t, u, a;
	if (data[j].z_p())
	  continue;
	gcdext(g, s, t, data[i], data[j]);

	u.mul(t, data[j]);
	u.addmul(s, data[i]);
	if (g != u) printf(" gcdext failed at (%u,%u)", i, j);

	unit_annihilator(u, a, g);
	if (u != 1) printf(" unit_annihilator.u failed at (%u,%u)", i, j);
	a *= g;
	if (!a.z_p()) printf(" unit_annihilator.a failed at (%u,%u)", i, j);
      }
  }

  {
    x.set_si(2);
    y.set_si(-5);
    x += {y,x};
    (x -= {y,y}) -= y;
    if (x.cmp_si(-28)) printf(" += {,} failed");
  }
  
  printf("\n");
}

template<unsigned K> void test0() {
  integer<0,K> x, y, z;

  x.init(); y.init(); z.init();
  
  printf("%s: size=%ld...", x.COEFF_ID(), sizeof x);
  if (!std::is_trivial<decltype(x)>::value) printf(" std::is_trivial failed");
  if (!std::is_standard_layout<decltype(x)>::value) printf(" std::is_standard_layout failed");

  x.set_si(x.hash());
  x.zero();
  if (x.nz_p()) printf(" 0.nz_p() failed");
  if (!x.z_p()) printf(" 0.z_p() failed");
  y.set_si(1);
  if (!x.reduced_p(y)) printf(" 0.reduced_p(1) failed");
  x.set(y); if (x.reduced_p(y)) printf(" 1.reduced_p(1) failed");
  y.add(y,x); if (x.cmp(y) == 0) printf(" 1.cmp(2) failed");
  y.add_si(y,-3); if (y.cmp_si(-1) != 0) printf(" -1.cmp(-1) failed");
  x.addmul(x,y); if (!x.z_p()) printf(" addmul failed");
  x.set_si(6);
  y.set_si(2);
  z.divexact(x,y); if (z.cmp_si(3)) printf(" divexact failed");
  x.set_si(-55);
  y.set_si(17);
  z.fdiv_q(x,y);
  z.fdiv_r(x,y);
  fdiv_qr(x,z,x,y); if (!z.reduced_p(y)) printf(" fdiv_qr.r failed");
  z.addmul(x,y); if (z.cmp_si(-55)) printf(" fdiv_qr.q failed");

  x.set_si(17*17+17+1);
  if (fdiv_qr_ui(y,z,x,17) != 1 || z.cmp_si(1)) printf(" fdiv_qr_ui.r failed");
  if (y.cmp_si(17+1)) printf(" fdiv_qr_ui.q failed");
  y.set_si(2);
  y.submul(y,y); if (y.cmp_si(-2)) printf(" submul failed");
  y.sub(y,y); if (y.nz_p()) printf(" sub failed");

  // some harder tests
  {
    integer<0,K> data[100];

    for (int i = 0; i < 100; i++) data[i].init();
    
    for (int i = 0; i < 25; i++)
      data[i].set_si(12-i);
    for (unsigned i = 25; i < 50; i++) {
      data[i].set_si(3);
      for (unsigned j = 0; j < i-25; j++)
	data[i].mul_si(data[i], 3);
    }
    for (unsigned i = 50; i < 100; i++)
      data[i].fdiv_q(data[i-50], data[19]); // divide by 7

    for (int i = 0; i < 25; i++)
      if (data[i].cmp_si(12-i))
	printf(" set/cmp failed at %u", i);
      
    for (unsigned i = 1; i < 100; i++)
      for (unsigned j = 24; j < 100; j++) {
	integer<0,K> s, t;
	s.init(); t.init();
	s.add(data[i], data[j]);
	t.add(data[j], data[i]);
	if (s != t) printf( " add failed at (%u,%u)", i, j);
	s -= data[i];
	if (s != data[j]) printf( " -= failed at (%u,%u)", i, j);
	s.clear(); t.clear();
      }

    for (unsigned i = 0; i < 100; i++)
      for (unsigned j = 0; j < 100; j++) {
	integer<0,K> g, s, t, u, a;
	g.init(); s.init(); t.init(); u.init(); a.init();
	
	if (data[j].z_p())
	  continue;
	gcdext(g, s, t, data[i], data[j]);

	try {
	  u.mul(t, data[j]);
	  u.addmul(s, data[i]);
	  if (g != u) printf(" gcdext failed at (%u,%u)", i, j);
	} catch(...) {
	  printf(" overflow in checking gcdext at (%u,%u)", i, j);
	}
	
	unit_annihilator(u, a, data[j]);
	if (u.sgn() * data[j].sgn() != 1) printf(" unit_annihilator.u failed at (%u,%u)", i, j);
	a *= data[j];
	if (!a.z_p()) printf(" unit_annihilator.a failed at (%u,%u)", i, j);

	g.clear(); s.clear(); t.clear(); u.clear(); a.clear();	
      }
    for (int i = 0; i < 100; i++) data[i].clear();
  }

  {
    x.set_si(2);
    y.set_si(-5);
    x += {y,x};
    (x -= {y,y}) -= y;
    if (x.cmp_si(-28)) printf(" += {,} failed");
  }

  x.clear(); y.clear(); z.clear();
  
  printf("\n");  
}

int main(int argc, char *argv[]) {
#if 1
  testP<2,1>();
  testP<2,5>();
  testP<2,63>();
  testP<2,64>();
  testP<2,1000>();
#endif
#if 1
  testP<3,1>();
  testP<3,2>();
  testP<3,5>();
  testP<3,40>();
  testP<3,1000>();
#endif
#if 1
  testP<5,1>();
  testP<5,27>();
  testP<5,100>();
#endif
#if 1
  testP<65521,2>();
  testP<65521,10>();
  testP<65521,100>();
#endif

  test0<UINT_MAX>();
  test0<1>();
  test0<10>();

  return 0;
}
