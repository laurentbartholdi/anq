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

#include <stdexcept>
#include <vector>

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
  static const key eol = -1;
public:
  sparsevec() = default;
  explicit sparsevec(slot *newp) : p(newp) { }
  explicit sparsevec(size_t s) { alloc(s); }
  
  bool allocated() const { return p != nullptr; }
  bool empty() const { return p == nullptr || p->first == eol; }
  void clear() { p->first = eol; }
  void truncate(size_t s) { p[s].first = eol; }
  sparsevec window(size_t s) const { return sparsevec(p+s); }
  bool operator==(const sparsevec &that) const { return p == that.p; }
  bool operator!=(const sparsevec &that) const { return p != that.p; }
  
  bool noalloc() { p = nullptr; return false; }
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
    iterator() = default;
    iterator(slot *newp) : p(newp) { }
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
  iterator front() const { return begin(); }

  iterator back() const {
    slot *q = p;
    while (q->first != eol) q++;
    return iterator(q-1);
  }

  template <typename V> void copy(const V &v) {
    auto i = begin();
    for (auto kc: v)
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
template<typename T, class U = defaultsparseops<T>> struct hollowvec {
  typedef unsigned key;
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
  inline herd leftherd(herd k) const { return k-((k&-k)>>1); } // x10^n -> x010^(n-1)
  inline herd rightherd(herd k) const { return k+((k&-k)>>1); } // x10^n -> x110^(n-1)
  inline herd superherd(herd k) const { // xy10^n -> x10^(n+1)
    unsigned b = k&-k;
    return (k-b) | (b << 1);
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

  void markup(skey k) {    
    // find and link successor
    skey prev = prevkey(k);
    skey next = p[prev].next;
    p[k].next = next;
    p[k].prev = prev;
    p[next].prev = p[prev].next = k;
    // mark bit and herds
    p[k].set = 1;
    for (herd h = k|1; !p[h].herd; h = superherd(h)) {
      p[h].herd = 1;
      if (h == topbit()) break;
    }
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

  class iterator {
    slot *const p;
    skey k;
    struct key_data {
      key first;
      T &second;
      key_data* operator->() { return this; }
    };
    inline skey next_key(skey k) { do k = p[k].next; while (k != nil && !U::nz_p(p[k].data)); return k; }
    inline skey prev_key(skey k) { do k = p[k].prev; while (k != nil && !U::nz_p(p[k].data)); return k; }
  public:
    iterator() = default;
    iterator(slot *const _p, skey _k) : p(_p), k(_k) { }
    void operator=(const iterator &that) {
      if (p != that.p)
	throw std::logic_error("assigning iterator to different vector");
      k = that.k;
    }
    key_data operator*() const { return key_data{(key)k,p[k].data}; }
    key_data operator->() const { return key_data{(key)k,p[k].data}; }
    iterator operator++() { k = next_key(k); return *this; }
    iterator operator++(int) { auto old = iterator(p,k); ++(*this); return old; }    
    iterator operator--() { k = prev_key(k); return *this; }
    iterator operator--(int) { auto old = iterator(p,k); --(*this); return old; }
    bool operator!=(const iterator &that) const { return k != that.k; }
    bool operator==(const iterator &that) const { return k == that.k; }
  };
  herd &topbit() const { return *(herd *) (p-2); }
public:
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
U::setzero(p[k].data); p[k].next = p[k].prev = 0;
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
    herd msb = getmsb(s);
    if (msb == topbit())
      return;
    if (msb < topbit()) {
      // make sure that the part between msb and topbit() is empty
      if (p[nil].prev >= (signed) msb<<1)
	throw std::runtime_error("resize() attempted on hollow vector containing entries beyond new limit");
      for (key k = msb<<1; k < topbit()<<1; k++)
	U::clear(p[k].data);
    }
    p = (slot *) realloc(p-2, ((msb<<1)+2)*sizeof(slot));
    if (p == nullptr)
      throw std::runtime_error("couldn't realloc() hollow vector");
    p += 2;
    if (msb > topbit()) {
      for (key k = topbit()<<1; k < msb<<1; k++) {
	p[k].set = p[k].herd = 0;
	U::init(p[k].data);
U::setzero(p[k].data); p[k].next = p[k].prev = 0;
      }
      if (p[topbit()].herd) { // array is not empty
	for (herd h = msb; h != topbit(); h >>= 1)
	  p[h].herd = 1;
      }
      topbit() = msb;
    }
  }
     
  T &operator[](key k) {
    if (__builtin_expect(!p[k].set,0)) {
      markup(k);
      U::setzero(p[k].data);
    }
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
    for (auto kc : *this)
      if (U::nz_p(kc.second)) return false;
    return true;
  }
  
  void clear() { // empty container
    clear_recur(topbit());
    p[nil].next = p[nil].prev = nil;
  }

  template <typename V> void copy(const V &v) {
    clear_recur(topbit());
    for (auto kc : v)
      coeff_set((*this)[kc.first], kc.second);
  }
  
  template <typename V> void copysorted(const V &v) { // load a sorted vector
    clear_recur(topbit());
    skey prev = nil;
    for (auto kc : v) {
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
  
  iterator begin() const { return ++end(); }
  iterator end() const { return iterator(p,nil); }
  iterator front() const { return begin(); }
  iterator back() const { return --end(); }
  iterator lower_bound(key k) {
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
  
  bool operator==(const hollowvec &that) const { return p == that.p; }
  bool operator!=(const hollowvec &that) const { return p != that.p; }
};

/****************************************************************
 * a primitive stack of vectors.
 *
 * sometimes it's useful to have a large collection of hollow vectors,
 * ready to be filled in and discarded. We don't want to malloc() and
 * free() them each time when they can perfectly well be reused.
 ****************************************************************
 */
template <typename T> class stack {
  std::vector<T> data;
  unsigned pos, vecsize;
public:
  stack() : pos(0) { };
  ~stack() noexcept(false) {
    if (pos != 0)
      throw std::logic_error("stack is not empty on free");
    for (unsigned i = 0; i < data.size(); i++)
      data[i].free(vecsize);
  }
  void setsize(size_t s) {
    for (unsigned i = 0; i < data.size(); i++) {
      //      data[i].free(vecsize);
      //data[i].alloc(s);
      data[i].resize(vecsize, s);
    }
    vecsize = s;
  }
  T &fresh() {
    if (pos == data.size()) {
      T v;
      v.alloc(vecsize);
      data.push_back(v);
    } else
      data[pos].clear();
    return data[pos++];
  }
  void pop() {
    if (pos-- == 0)
      throw std::logic_error("stack is already empty");
  }

  void pop(T &v) {
    pop();
    if (data[pos] != v)
      throw std::logic_error("stack is popped out of order");
  }
};
