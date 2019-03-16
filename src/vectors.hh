/****************************************************************
 * vectors.hh
 * various vector formats:
 * - sparsevec: a list of pairs {index,data}, terminated by index=-1U

 * - hollowvec: a list of data, with pointers and bits to keep track
     of which entries were allocated already
 ****************************************************************/

/* in each of these vector formats, we
   - supply enumerators
   - assume given a type T with function is_zero(T&) and set_zero(T&)
 */

#include <stdlib.h>
#include <stdexcept>
#include <vector>
#include <iterator>

/****************************************************************
   sparsevec<T>: just a pointer to { k: unsigned; d: T }
   terminated by index = eol.

   API:
   ****************************************************************
   sparsevec<T,U> v;

   T is a type.
   U is a class with methods init(T&), clear(T&), set(T&, const T&), setzero(T&), nz_p(T&),
   which defaults to the standard arithmetic operations: nop, nop, x=y, x=0, x!=0

   sparsevec(slot *): creates a new sparsevec out of a pointer
   sparsevec(s): creates a new sparsevec with given size

   explicit creation/destruction, so sparsevecs are POD, and can be passed
   in registers (they're just a pointer to the first entry)
   ****************************************************************
   eol == marker for the end of list
   allocated() == (pointer != nullptr)
   noalloc(): set point to nullptr
   empty() == list non empty
   size() == list size
   clear(): empty list
   truncate(s): set size to s
   window(s) == subvector starting at element #s
   operator==
   alloc(s): set maxlength to s (not counting eol marker). The first s entries are created with U::init
   free(s): free vector of maxlength s. The first s entries are freed with U::clear
   free(): free vector's size worth of entries
   resize(olds=size(),news): semantically the same as free+alloc.
   &operator[](k) == k'th slot
   copy(v)

   begin(), end(), front(), back(): iterators (see below)

   Big hack: end() is not a pointer to the next-to-last entry of the vector,
   but rather a virtual, nullptr end marker. Two iterators are deemed == if
   they either point to the same place or one of them is nullptr.
   ****************************************************************
   iterators to sparsevec:

   operator ++, --, *, ->, !=
   atend() == whether iterator reached end
   tail() == sparsevec starting at current iterator position
   markend(): put an eol marker at current position
   ****************************************************************
   */

template <typename T> struct defaultsparseops {
  static void init(T &) { }
  static void clear(T &) { }
  static void set(T &x, const T &y) { x = y; }
  static void setzero(T &x) { x = 0; }
  static bool nz_p(const T &x) { return x != 0; }
};

template <typename T, class U = defaultsparseops<T>> struct sparsevec {
  typedef unsigned key;
  typedef std::pair<key,T> slot;
private:
  slot *p;
public:
  static const key eol = -1;

  // these are not default initializers, because we want a POD
  static sparsevec bad() {
    sparsevec r;
    r.p = (slot *)0xff00ff00ff00ffLL;
    return r;
  }
  
  static sparsevec null() {
    sparsevec r;
    r.p = nullptr;
    return r;
  }
  
  constexpr bool allocated() const { return p != nullptr; }
  constexpr bool empty() const { return p == nullptr || p->first == eol; }
  inline void clear() { p->first = eol; }
  inline void truncate(size_t s) { p[s].first = eol; }
  inline sparsevec window(size_t s) const {
    sparsevec r;
    r.p = p+s;
    return r;
  }

  constexpr bool is_identical(const sparsevec &that) const { return p == that.p; }

  inline bool noalloc() { p = nullptr; return false; }
  void alloc(size_t s) {
    p = (slot *) malloc(s*sizeof(slot)+sizeof(key));
    if (p == nullptr) throw std::runtime_error("couldn't malloc() sparse vector");

    for (key k = 0; k < s; k++) U::init(p[k].second);
     /* we don't allocate the coefficient in the last position, it's
	only used for the eol marker */
    clear();
  }
  
  void free() {
    if (p == nullptr) return;
    for (auto kd : *this)
      U::clear(kd.second);
    ::free(p);
  }

  void resize(size_t olds, size_t news) {
    if (olds > news)
      for (key k = news; k < olds; k++)
	U::clear(p[k].second);

    p = (slot *) realloc ((void *)p, news*sizeof(slot)+sizeof(key));
    if (p == nullptr)
      throw std::runtime_error("couldn't realloc() sparse vector");

    if (olds < news)
      for (key k = olds; k < news; k++)
	U::init(p[k].second);
  }

  void resize(size_t news) {
    resize(size(), news);
  }
  
  slot &operator[](key k) const { return p[k]; }
  
  size_t size() const {
    size_t l = 0;
    for (auto kc __attribute__((unused)): *this)
      l++;
    return l;
  }

  class iterator {
    slot *p;
  public:
    iterator(slot *_p) : p(_p) { }
    iterator operator++() { p++; return *this; }
    iterator operator++(int) { slot *old = p; p++; return iterator(old); }
    iterator operator--() { p--; return *this; }
    iterator operator--(int) { slot *old = p; p--; return iterator(old); }
    slot &operator*() const { return *p; }
    slot *operator->() const { return p; }
    // hack: we will only compare pointers when in an automatic loop
    // "for(_ : vec)". We want the termination condition to say:
    // iter.begin() != iter.end() when first they're not the same pointer,
    // and then iter.begin()->first != eol
    bool atend() const { return p == nullptr || p->first == eol; }
    bool operator!=(const iterator &that) const { return p != that.p && (!atend() || !that.atend()); }
    bool operator==(const iterator &that) const { return !(*this != that); }
    sparsevec tail() const { return sparsevec(p); }
    void markend() { p->first = eol; }
  };
  iterator begin() const { return iterator(p); }
  iterator end() const { return iterator(nullptr); }
  slot &front() const { return p[0]; }
  slot &back() const {
    slot *q = p;
    while (q->first != eol) q++;
    return q[-1];
  }
  
  class reverse_iterator {
    slot *p;
  public:
    reverse_iterator(slot *_p) : p(_p) { }
    reverse_iterator operator++() { p--; return *this; }
    reverse_iterator operator++(int) { slot *old = p; p--; return reverse_iterator(old); }
    reverse_iterator operator--() { p++; return *this; }
    reverse_iterator operator--(int) { slot *old = p; p++; return reverse_iterator(old); }
    slot &operator*() const { return *p; }
    slot *operator->() const { return p; }
    bool operator!=(const reverse_iterator &that) const { return p != that.p; }
    bool operator==(const reverse_iterator &that) const { return !(*this != that); }
  };
  reverse_iterator rbegin() { slot *q = p; while (q->first != eol) q++; return reverse_iterator(q-1); }
  reverse_iterator rend() { return reverse_iterator(p); }
					 
  template <typename V> void copy(const V &v) {
    auto i = begin();
    for (const auto &kc : v)
      U::set(i->second, kc.second), i->first = kc.first, i++;
    i.markend();
  }

  template <typename I> void copy(I from, const I to) {
    auto i = begin();
    while (from != to)
      U::set(i->second, (*from).second), i->first = (*from).first, i++, from++;
    i.markend();
  }
  
  friend sparsevec emptyvec() { sparsevec v; v.alloc(0); return v; }
};

/****************************************************************
   hollowvec<T,U>: a vector of data, with additional information for
   fast skipping over 0's
 
   T is a type.
   U is a class with methods init(T&), clear(T&), set(T&, const T&), setzero(T&), nz_p(T&),
   which defaults to the standard arithmetic operations: nop, nop, x=y, x=0, x==0
   API:
   ****************************************************************
   alloc(size): create. size is rounded to next power of 2
   free(): free memory

   T &operator[](key k) = element k in the vector
   size() = number of non-zero elements
   clear(): empty vector
   copysorted(const sparsevec<T,U> &): load a sorted sparsevec

   begin(), end(), front(), back(): iterators
   ****************************************************************
   iterators may be accessed, compared, incremented and decremented.
   ****************************************************************
   */

//#define FOUND_A_WAY_TO_AVOID_ITERATOR_DUPLICATION

template <typename T, typename U, typename slot, typename key, typename skey, const skey nil> struct hollowvec_iterator {
  struct key_data {
    key first;
    T &second;
    const key_data* operator->() const { return this; }
  };
protected:
  slot *const p;
  skey k;
  inline skey next_key(skey k) { do k = p[k].next; while (k != nil && !U::nz_p(p[k].data)); return k; }
  inline skey prev_key(skey k) { do k = p[k].prev; while (k != nil && !U::nz_p(p[k].data)); return k; }
public:
  hollowvec_iterator(slot *const _p, skey _k) : p(_p), k(_k) { }
  void operator=(const hollowvec_iterator &that) {
    if (p != that.p)
      throw std::logic_error("assigning iterator to different vector");
    k = that.k;
  }
  key_data operator*() const { return key_data{(key)k,p[k].data}; }
  key_data operator->() const { return key_data{(key)k,p[k].data}; }
  bool operator!=(const hollowvec_iterator &that) const { return k != that.k; }
  bool operator==(const hollowvec_iterator &that) const { return k == that.k; }
  hollowvec_iterator operator++() { k = next_key(k); return *this; }
  hollowvec_iterator operator++(int) { auto old = hollowvec_iterator(p,k); ++(*this); return old; }    
  hollowvec_iterator operator--() { k = prev_key(k); return *this; }
  hollowvec_iterator operator--(int) { auto old = hollowvec_iterator(p,k); --(*this); return old; }
};

template <typename T, typename U, typename slot, typename key, typename skey, const skey nil> struct std::iterator_traits<hollowvec_iterator<T, U, slot, key, skey, nil>> {
  using difference_type = std::ptrdiff_t;
  using size_type = std::size_t;
  using value_type = typename hollowvec_iterator<T, U, slot, key, skey, nil>::key_data;
  using pointer = const typename hollowvec_iterator<T, U, slot, key, skey, nil>::key_data*;
  using reference = const typename hollowvec_iterator<T, U, slot, key, skey, nil>::key_data&;
  using iterator_category = std::random_access_iterator_tag;
};

#ifndef FOUND_A_WAY_TO_AVOID_ITERATOR_DUPLICATION // can't use std::reverse_iterator :(
template <typename T, typename U, typename slot, typename key, typename skey, const skey nil> struct hollowvec_riterator {
  struct key_data {
    key first;
    const T &second;
    const key_data* operator->() const { return this; }
  };
protected:
  slot *const p;
  skey k;
  inline skey next_key(skey k) { do k = p[k].next; while (k != nil && !U::nz_p(p[k].data)); return k; }
  inline skey prev_key(skey k) { do k = p[k].prev; while (k != nil && !U::nz_p(p[k].data)); return k; }
public:
  hollowvec_riterator(slot *const _p, skey _k) : p(_p), k(_k) { }
  void operator=(const hollowvec_riterator &that) {
    if (p != that.p)
      throw std::logic_error("assigning iterator to different vector");
    k = that.k;
  }
  key_data operator*() const { return key_data{(key)k,p[k].data}; }
  key_data operator->() const { return key_data{(key)k,p[k].data}; }
  bool operator!=(const hollowvec_riterator &that) const { return k != that.k; }
  bool operator==(const hollowvec_riterator &that) const { return k == that.k; }
  hollowvec_riterator operator++() { k = prev_key(k); return *this; }
  hollowvec_riterator operator++(int) { auto old = hollowvec_riterator(p,k); ++(*this); return old; }    
  hollowvec_riterator operator--() { k = next_key(k); return *this; }
  hollowvec_riterator operator--(int) { auto old = hollowvec_riterator(p,k); --(*this); return old; }
};

template <typename T, typename U, typename slot, typename key, typename skey, const skey nil> struct std::iterator_traits<hollowvec_riterator<T, U, slot, key, skey, nil>> {
  using difference_type = std::ptrdiff_t;
  using size_type = std::size_t;
  using value_type = typename hollowvec_iterator<T, U, slot, key, skey, nil>::key_data;
  using pointer = const typename hollowvec_iterator<T, U, slot, key, skey, nil>::key_data*;
  using reference = const typename hollowvec_iterator<T, U, slot, key, skey, nil>::key_data&;
  using iterator_category = std::random_access_iterator_tag;
};
#endif

template<typename T, class U = defaultsparseops<T>> struct hollowvec {
  typedef unsigned key;
  //!!!  struct key_data { key first; T &second; };
private:
  typedef signed skey;
  typedef unsigned herd;
  static const skey nil = -1;
  struct slot {
    T data;
    signed next:31;
    bool set:1;
    signed prev:31;
    bool herd:1;
  };
  /* implementation:
     v[k] is stored in p[k].data.
     the next stored position is in p[k].next (or nil if at end of list).
     the previous stored position is in p[k].next (or nil if at begin of list).
     p[k].set is true iff entry k is allocated.
     p[k].herd is true iff some entry in INTERVAL(k) is allocated.
     INTERVAL(k) = [k-1,k] if k odd, [k-LOW(k),k+LOW(k)[ with LOW(k) = k&-k;
     so INTERVAL(...10...0) = [...00...0,...11...1]

     p[-1] contains the pointers to first and last entry in next/prev
     p[-2] contains half the size of the vector
  */
  slot *p;
  inline herd leftherd(herd k) const { // x10^n -> x010^(n-1)
    return k-((k&-k)>>1);
  }
  inline herd rightherd(herd k) const { // x10^n -> x110^(n-1)
    return k+((k&-k)>>1);
  }
  inline herd superherd(herd k) const { // xy10^n -> x10^(n+1)
    unsigned b = k&-k;
    return (k-b) | (b << 1);
  }
  inline herd siblingherd(herd k) const { // xy10^n -> x(1-y)10^n
    return k^((k&-k)<<1);
  }
  inline herd getmsb(key k) {
    for (key t; (t = k - (k&-k)); k = t);
    return k;
  }

  inline key prevkey(key k) const { // find previous allocated key
    if ((k & 1) && p[k-1].set) // k = ...1, p[...0] not allocated
      return k-1;
    key h = k & ~1; // h = ...0
    while (h != 0) { // h = ...10...0
      herd bit = (h&-h) >> 1; // bit = ...01...0
      h -= bit; // h = ...010...0 = [...000...0,...011...1]
      if (p[h].herd) {
	while (!(h & 1)) {
	  herd h1 = rightherd(h); // h1 = ...001...0=0...001...1
	  h = (p[h1].herd ? h1 : leftherd(h));
	}
	return (p[h].set ? h : h-1);    
      }
      h -= bit; // h = ...000...0 = previous interval
    }
    return nil;
  }

  inline void markup(skey k) {    
    // mark bit and herds
    p[k].set = 1;
    for (herd h = k|1; !p[h].herd; h = superherd(h)) {
      p[h].herd = 1;
      if (h == topbit()) break;
    }
  }

  inline void unmarkup(skey k) {
    // unmark bits and herds
    p[k].set = 0;
    if (!p[k^1].set)
      for (herd h = k|1;; h = superherd(h)) {
	p[h].herd = 0;
	if (h == topbit() || p[siblingherd(h)].herd)
	  break;
      }
  }

  void markandlink(key k) {
    // find and link successor
    skey prev = prevkey(k);
    skey next = p[prev].next;
    p[k].next = next;
    p[k].prev = prev;
    p[next].prev = p[prev].next = k;
    markup(k);
    U::setzero(p[k].data);
  }

  void clear_recur(herd h) {
    if (h & 1)
      p[h].herd = p[h-1].set = p[h].set = 0;
    else if (p[h].herd) {
      p[h].herd = 0;
      clear_recur(leftherd(h));
      clear_recur(rightherd(h));
    }
  }

  herd &topbit() const { return *(herd *) (p-2); }

  inline skey next_key(skey k) const { do k = p[k].next; while (k != nil && !U::nz_p(p[k].data)); return k; }
  inline skey prev_key(skey k) const { do k = p[k].prev; while (k != nil && !U::nz_p(p[k].data)); return k; }
  
public:
  using iterator = hollowvec_iterator<T, U, slot, key, skey, nil>;
  using const_iterator = hollowvec_iterator<const T, U, const slot, key, skey, nil>;
#ifndef FOUND_A_WAY_TO_AVOID_ITERATOR_DUPLICATION
  using reverse_iterator = hollowvec_riterator<T, U, const slot, key, skey, nil>;
  using const_reverse_iterator = hollowvec_riterator<const T, U, const slot, key, skey, nil>;
#else
  using reverse_iterator = std::reverse_iterator<iterator>;
  using const_reverse_iterator = std::reverse_iterator<const_iterator>;
#endif
  
  void sanitycheck() {
    for (skey k = 0; k < (skey) topbit()<<1; k++)
      if (p[k].set && (p[p[k].next].prev != k || p[p[k].prev].next != k))
	throw std::logic_error("linked list is broken!");
  }
  
  void alloc(size_t s) {
    herd msb = getmsb(s);

    p = (slot *) malloc(((msb<<1)+2)*sizeof(slot));
    if (p == nullptr)
      throw std::runtime_error("couldn't malloc() hollow vector");
    p += 2; // we store the head and tail at position -1, and the topbit at position -2

    topbit() = msb;
    p[nil].prev = p[nil].next = nil;

    for (key k = 0; k < msb<<1; k++) {
      p[k].set = p[k].herd = 0;
      U::init(p[k].data);
    }
  }

  void free() {
    for (key k = 0; k < topbit()<<1; k++)
      U::clear(p[k].data);
    ::free(p-2);
  }

  void free(size_t size) {
    for (key k = 0; k < topbit()<<1; k++)
      U::clear(p[k].data);
    ::free(p-2);
  }

  void resize(size_t oldsize, size_t s) {
    herd msb = getmsb(s), oldtopbit = topbit();
    if (msb == oldtopbit)
      return;
    if (msb < oldtopbit) {
      // make sure that the part between msb and topbit() is empty
      if (p[nil].prev >= (signed) msb<<1)
	throw std::runtime_error("resize() attempted on hollow vector containing entries beyond new limit");
      for (key k = msb<<1; k < oldtopbit<<1; k++)
	U::clear(p[k].data);
    }
    p = (slot *) realloc(p-2, ((msb<<1)+2)*sizeof(slot));
    if (p == nullptr)
      throw std::runtime_error("couldn't realloc() hollow vector");
    p += 2;
    if (msb > oldtopbit) {
      for (key k = oldtopbit<<1; k < msb<<1; k++) {
	p[k].set = p[k].herd = 0;
	U::init(p[k].data);
      }
      if (p[oldtopbit].herd) { // array is not empty
	for (herd h = msb; h != oldtopbit; h >>= 1)
	  p[h].herd = 1;
      }
    }
    topbit() = msb;
  }

  inline T &operator[](key k) {
    if (__builtin_expect(!p[k].set,0)) markandlink(k);
    return p[k].data;
  }

  const T &operator[](key k) const {
    if (__builtin_expect(!p[k].set,0))
      throw std::logic_error("accessing unbound entry in const vector");
    return p[k].data;
  }
  
  size_t size() const { // number of allocated elements
    size_t l = 0;
    for (auto kc __attribute__((unused)): *this)
      l++;
    return l;
  }

  bool empty() const { // are all elements 0?
    for (const auto &kc __attribute__((unused)): *this)
      return false;
    return true;
  }
  
  size_t erase(skey k) {    
    // remove element from linked list
    if (!p[k].set)
      return 0;
    
    p[p[k].prev].next = p[k].next;
    p[p[k].next].prev = p[k].prev;

    // clear bit and herds
    unmarkup(k);

    return 1;
  }

  void clear() { // empty container
#if 0
    clear_recur(topbit());
#else
    for (skey k = p[nil].next; k != nil; k = p[k].next)
      unmarkup(k);
#endif
    p[nil].next = p[nil].prev = nil;
  }

  template <typename V> void copy(const V &v) { // load a sorted vector
    clear_recur(topbit());
    skey prev = nil;
    for (const auto &kc : v) {
      skey k = kc.first;
      if (k <= prev)
	throw std::invalid_argument("sparsevec must be sorted");
      U::set(p[k].data, kc.second);
      markup(k);
      p[prev].next = k;
      p[k].prev = prev;
      prev = k;
    }
    p[prev].next = nil;
    p[nil].prev = prev;
  }

  sparsevec<T,U> getsparse() {
    sparsevec<T,U> v;
    v.alloc(size());
    v.copy(*this);
    return v;
  }
  
  iterator begin() { return ++end(); }
  const_iterator begin() const { return ++end(); }
  const_iterator cbegin() const { return ++end(); }
  iterator end() { return iterator(p,nil); }
  const_iterator end() const { return const_iterator(p,nil); }
  const_iterator cend() const { return const_iterator(p,nil); }
  //!!!  key_data &front() const { key k = next_key(nil); return key_data{k,p[k].data}; }
  //!!!key_data &back() { key k = prev_key(nil); return {k,p[k].data}; }
  iterator lower_bound(key k) {
    if (p[k].set && U::nz_p(p[k].data))
      return iterator(p,k);
    else
      return ++iterator(p,prevkey(k));
  }
  const_iterator lower_bound(key k) const {
    if (p[k].set && U::nz_p(p[k].data))
      return iterator(p,k);
    else
      return ++iterator(p,prevkey(k));
  }
  iterator upper_bound(key k) {
    if (p[k].set)
      return ++iterator(p,k);
    else
      return ++iterator(p,prevkey(k));
  }
  const_iterator upper_bound(key k) const {
    if (p[k].set)
      return ++const_iterator(p,k);
    else
      return ++const_iterator(p,prevkey(k));
  }
#ifdef FOUND_A_WAY_TO_AVOID_ITERATOR_DUPLICATION
  reverse_iterator rbegin() { return reverse_iterator{end()}; }
  reverse_iterator rend() { return reverse_iterator{begin()}; }
  const_reverse_iterator rbegin() const { return const_reverse_iterator{end()}; }
  const_reverse_iterator rend() const { return const_reverse_iterator{begin()}; }
  const_reverse_iterator crbegin() const { return rbegin(); }
  const_reverse_iterator crend() const { return rend(); }
#else
  reverse_iterator rbegin() { return ++rend(); }
  reverse_iterator rend() { return reverse_iterator(p,nil); }
  const_reverse_iterator rbegin() const { return ++rend(); }
  const_reverse_iterator rend() const { return const_reverse_iterator(p,nil); }
  const_reverse_iterator crbegin() const { return rbegin(); }
  const_reverse_iterator crend() const { return rend(); }
#endif

  bool is_identical(const hollowvec &that) const { return p == that.p; }
};

/****************************************************************
 * a primitive supply of vectors.
 *
 * sometimes it's useful to have a large collection of hollow vectors,
 * ready to be filled in and discarded. We don't want to malloc() and
 * free() them each time when they can perfectly well be reused.
 ****************************************************************
 */
template <typename T> class vec_supply : public std::vector<T> {
  unsigned vecsize, pos;
public:
  vec_supply() : pos(0) { };
  ~vec_supply() noexcept(false) {
    if (pos != 0)
      throw std::logic_error("cannot ~(): stack is not empty");
    for (auto &p : *this)
      p.free(vecsize);
  }
  void setsize(size_t s) {
    for (auto &p : *this)
      p.resize(vecsize, s);
    vecsize = s;
  }
  T &fresh() {
    if (pos == this->size()) {
      T v;
      v.alloc(vecsize);
      this->push_back(v);
    }
    return (*this)[pos++];
  }
      
  void release(const T &v) {
    if (pos-- == 0)
      throw std::logic_error("cannot pop(): stack is already empty");
    if (!(*this)[pos].is_identical(v))
      throw std::logic_error("stack is popped out of order");
    (*this)[pos].clear();
  }
};

/****************************************************************
 * a primitive stack of (key,T) pairs.
 * like std::vector, but with allocation and deallocation of T.
 ****************************************************************/

template <typename T, class U = defaultsparseops<T>> class T_stack {
public:  typedef unsigned key;
  typedef std::pair<key,T> slot;
  typedef typename std::vector<slot>::iterator iterator;
  typedef typename std::vector<slot>::const_iterator const_iterator;
  typedef unsigned watermark_t;
private:
  std::vector<slot> data;
  watermark_t watermark;
public:
  std::vector<slot> raw() { return data; }
  void push(const slot &kx) {
    if (watermark == data.size()) {
      T newx;
      U::init(newx);
      slot s{kx.first,newx};
      U::set(s.second,kx.second);
      data.push_back(s);
    } else
      data[watermark].first = kx.first, U::set(data[watermark].second, kx.second);
    watermark++;
  }
  void push(key k) {
    if (watermark == data.size()) {
      T newx;
      U::init(newx);
      data.push_back({k,newx});
    } else
      data[watermark].first = k;
    watermark++;
  }
  slot &pop() {
    if (watermark == 0)
      throw std::logic_error("T_stack: pop() on empty stack");
    return data[--watermark];
  }
  const slot &peek() const {
    if (watermark == 0)
      throw std::logic_error("T_stack: top() on empty stack");
    return data[watermark-1];
  }
  watermark_t highwatermark() const { return watermark; }
  T_stack() : watermark(0) { }
  ~T_stack() {
    for (auto &kc : data)
      U::clear(kc.second);
  }
};
