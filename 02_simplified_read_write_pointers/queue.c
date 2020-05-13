#include <stdlib.h>

struct queue {
  char *buffer; //< [ 0 1 2 3 4 5 ... (N-1) ]
  char *wptr;
  char *rptr;
  size_t N;
//implicitly M=1
  size_t K;
};

/*@
fixpoint list<t> rotate_left<t>(int n, list<t> xs) {
  return append(drop(n, xs), take(n, xs));
}

// Simple lemmas can be proven by Verifast directly
lemma_auto void rotate_length<t>(int n, list<t> xs)
  requires 0 <= n && n <= length(xs);
  ensures length(rotate_left(n, xs)) == length(xs);
{}

lemma void take_length_eq<t>(int k, list<t> xs, list<t> ys)
  requires 0 <= k && k <= length(xs) && take(k, xs) == ys;
  ensures length(ys) == k;
{}

// Following lemmas (unproven in Verifast) are straightforward identities for mod
lemma_auto void mod_same(int n);
  requires 0 < n;
  ensures n % n == 0;

lemma void mod_plus_one(int x, int y, int n);
  requires 0 < n && x == (y % n);
  ensures ((x+1) % n) == ((y+1) % n);

lemma void mod_plus_distr(int x, int y, int n);
  requires 0 < n;
  ensures ((x % n) + y) % n == (x + y) % n;

lemma_auto void mod_range(int x, int n);
  requires 0 < n;
  ensures 0 <= (x % n) && (x % n) < n;
  
lemma void mod_in_range(int x, int n);
  requires 0 < n && 0 <= x && x < n;
  ensures ((x % n) == x);

// !!!Following lemmas are unproven in Verifast. We prove them separately in Coq!!!
lemma void enq_lemma<t>(int k, int i, list<t> xs, list<t> ys, t z);
  requires 0 < length(xs) && k < length(xs) && i < length(xs) && take(k, rotate_left(i, xs)) == ys;
  ensures take(k+1, rotate_left(i, update((i+k)%length(xs), z, xs))) == append(ys, cons(z, nil));
  
lemma void deq_lemma<t>(int k, int i, list<t> xs, list<t> ys, t z);
  requires 0 < k && k <= length(xs) && i < length(xs) && take(k, rotate_left(i, xs)) == ys && z == head(ys);
  ensures take(k-1, rotate_left((i+1)%length(xs), xs)) == tail(ys);

lemma void deq_value_lemma<t>(int k, int i, list<t> xs, list<t> ys);
  requires 0 < k && k <= length(ys) && take(k, rotate_left(i, xs)) == ys;
  ensures nth(i, xs) == head(ys);

lemma void split_element(char *buffer, size_t N, size_t i);
  requires chars(buffer, N, ?elements) &*& i < N;
  ensures
    chars(buffer, i, take(i, elements)) &*&
    character(buffer + i, nth(i, elements)) &*&
    chars(buffer + (i + 1), (N-1-i), drop(i+1, elements));
    
lemma void join_element(char *buffer, size_t N, size_t i);
  requires
    chars(buffer, i, ?prefix) &*&
    character(buffer + i, ?element) &*&
    chars(buffer + (i + 1), (N-1-i), ?suffix);  
  ensures chars(buffer, N, append(prefix, cons(element, suffix)));

lemma void combine_list_no_change<t>(list<t>prefix, t x, list<t>suffix, size_t i, list<t> xs);
  requires i < length(xs) && prefix == take(i, xs) && x == nth(i, xs) && suffix == drop(i+1, xs);
  ensures xs == append(prefix, cons(x, suffix));

lemma void combine_list_update<t>(list<t>prefix, t x, list<t>suffix, size_t i, list<t> xs);
  requires i < length(xs) && prefix == take(i, xs) && suffix == drop(i+1, xs);
  ensures update(i, x, xs) == append(prefix, cons(x, suffix));

predicate queue(struct queue *q, size_t W, size_t R, size_t N, size_t K, list<char> abs) =
  malloc_block_queue(q) &*&
  q->buffer |-> ?buffer &*&
  q->wptr |-> ?wptr &*&
  q->rptr |-> ?rptr &*&
  wptr == buffer + W &*&
  rptr == buffer + R &*&
  q->N |-> N &*&
  q->K |-> K &*&
  0 <= W &*& W < N &*&
  0 <= R &*& R < N &*&
  0 < N &*&
  0 <= K &*& K <= N &*&
  W == (R + 1 + K) % N &*&
  chars(buffer, N, ?contents) &*&
  take(K, rotate_left((R+1)%N, contents)) == abs &*&
  malloc_block(buffer, N);
@*/

struct queue *create_queue(size_t N)
  //@ requires 0 < N;
  //@ ensures queue(result, 0, (N-1), N, 0, nil);
{
  struct queue *q = malloc(sizeof(struct queue));
  char *buffer = malloc(N);
  if (!q || !buffer) abort();
  q->buffer = buffer;
  q->wptr = buffer;
  q->rptr = buffer + (N-1);
  q->N = N;
  q->K = 0;
  //@close queue(q, 0, (N-1), N, 0, nil);
  return q;
}

bool deq(struct queue *q, char *x)
  //@ requires queue(q, ?W, ?R, ?N, ?K, ?abs) &*& character(x, ?xold);
  /*@ ensures
        result != (K == 0) &*&
        (result ? queue(q, W, (R+1)%N, N, (K-1), tail(abs)) : queue(q, W, R, N, K, abs)) &*&
        character(x, ?xnew) &*& xnew == (result ? head(abs) : xold); @*/
{
  //@open queue(q, W, R, N, K, abs);
  if (q->K == 0) {
    //@close queue(q, W, R, N, K, abs);
    return false;
  }
  //@assert q->buffer |-> ?buffer;
  //@assert chars(buffer, N, ?contents);
  //@assert q->rptr == buffer + R;
  q->rptr++;
  //@assert q->rptr == buffer + R + 1;
  if (q->buffer + q->N <= q->rptr) {
    q->rptr = q->buffer;
    //@assert q->rptr == buffer + ((R+1) % N);
  } else {
    //@mod_in_range((R+1), N);
    //@assert q->rptr == buffer + ((R+1) % N);
  }
  //@assert q->rptr == buffer + ((R+1) % N);
  //@split_element(buffer, N, (R+1)%N);
  //@assert chars(buffer, (R+1)%N, ?prefix);
  //@assert character(buffer + (R+1)%N, ?element);
  //@assert chars(buffer + ((R+1)%N + 1), (N-1-(R+1)%N), ?suffix);
  *x = *(q->rptr);
  q->K--;
  //@mod_plus_distr(R+1, K, N);
  //@assert 0 < K && K <= N;
  //@length_take(K, contents);
  //@take_length_eq(K, rotate_left((R+1)%N, contents), abs);
  //@assert abs == cons(?z, _);
  //@deq_lemma(K, (R+1)%N, contents, abs, z);
  //@join_element(buffer, N, (R+1)%N);
  //@combine_list_no_change(prefix, element, suffix, (R+1)%N, contents);
  //@close queue(q, W, (R+1)%N, N, (K-1), tail(abs));
  //@deq_value_lemma(K, (R+1)%N, contents, abs);
  return true;
}

bool enq(struct queue *q, char x)
  //@ requires queue(q, ?W, ?R, ?N, ?K, ?abs);
  //@ ensures result != (K == N) &*& result ? queue(q, (W+1)%N, R, N, (K+1), append(abs, cons(x, nil))) : queue(q, W, R, N, K, abs);
{
  //@open queue(q, W, R, N, K, abs);
  if (q->K == q->N) {
    //@close queue(q, W, R, N, K, abs);
    return false;
  }
  //@assert q->buffer |-> ?buffer;
  //@assert chars(buffer, N, ?contents);
  //@assert take(K, rotate_left((R+1)%N, contents)) == abs;
  //@split_element(buffer, N, W);
  //@assert chars(buffer, W, ?prefix);
  //@assert character(buffer + W, _);
  //@assert chars(buffer + (W + 1), (N-1-W), ?suffix);
  *(q->wptr) = x;
  //@assert q->wptr == buffer + W;
  q->wptr++;
  //@assert q->wptr == buffer + W + 1;
  if (q->buffer + q->N <= q->wptr) {
    //@assert W == (N-1);
    q->wptr = q->buffer;
    //@assert q->wptr == buffer;
    //@assert q->wptr == buffer + ((W + 1) % N);
  } else {
    //@assert (W+1) < N;
    //@assert q->wptr == buffer + W + 1;
    //@mod_in_range((W+1), N);
    //@assert q->wptr == buffer + ((W + 1) % N);
  }
  //@assert(q->wptr == buffer + (W + 1)%N);
  q->K++;
  //@enq_lemma(K, (R+1)%N, contents, abs, x);
  //@mod_plus_distr(R+1, K, N);
  //@assert(take(K+1, rotate_left((R+1)%N, update(W, x, contents))) == append(abs, cons(x, nil)));
  //@assert W == (R + 1 + K) % N;
  //@mod_plus_one(W, R + 1 + K, N);
  //@assert((W+1)%N == ((R + 1) + (K + 1)) % N);
  //@join_element(buffer, N, W);
  //@combine_list_update(prefix, x, suffix, W, contents);
  //@close queue(q, (W+1)%N, R, N, (K+1), append(abs, cons(x, nil)));
  return true;
}

int main()
  //@requires true;
  //@ensures true;
{
  struct queue *q = create_queue(8);
  //@assert queue(q, /*W*/0, /*R*/7, /*N*/8, /*K*/0, /*abs*/nil);
  bool result = enq(q, 'a'); assert result;
  //@assert queue(q, /*W*/1, /*R*/7, /*N*/8, /*K*/1, /*abs*/cons('a', nil));
  result = enq(q, 'b'); assert result;
  //@assert queue(q, /*W*/2, /*R*/7, /*N*/8, /*K*/2, /*abs*/cons('a', cons('b', nil)));
  result = enq(q, 'c'); assert result;
  //@assert queue(q, /*W*/3, /*R*/7, /*N*/8, /*K*/3, /*abs*/cons('a', cons('b', cons('c', nil))));
  
  char *c = malloc(1);
  if (!c) abort();
  *c = 'z';
  result = deq(q, c); assert result;
  //@assert queue(q, /*W*/3, /*R*/0, /*N*/8, /*K*/2, /*abs*/cons('b', cons('c', nil)));
  //@assert character(c, 'a');
  result = deq(q, c); assert result;
  //@assert queue(q, /*W*/3, /*R*/1, /*N*/8, /*K*/1, /*abs*/cons('c', nil));
  return 0;
  //@leak queue(q, _, _, _, _, _);
  //@leak malloc_block(c, _);
  //@leak character(c, _);
}
