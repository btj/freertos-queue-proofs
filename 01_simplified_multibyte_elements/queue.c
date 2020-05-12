#include <stdlib.h>
#include <string.h>

struct queue {
  char *buffer; //< [ 0 1 2 3 4 5 ... (NM-1) ] (logically N elements of M bytes)
  size_t W;
  size_t R;
  size_t N;
  size_t M;
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

predicate buffer(char *buffer, size_t N, size_t M; list<list<char> > elements) =
    N == 0 ?
        elements == nil
    :
        chars(buffer, M, ?x) &*& buffer(buffer + M, N - 1, M, ?xs) &*& elements == cons(x, xs);

lemma void combine_list_no_change<t>(list<t>prefix, t x, list<t>suffix, size_t i, list<t> xs);
  requires i < length(xs) && prefix == take(i, xs) && x == nth(i, xs) && suffix == drop(i+1, xs);
  ensures xs == append(prefix, cons(x, suffix));

lemma void combine_list_update<t>(list<t>prefix, t x, list<t>suffix, size_t i, list<t> xs);
  requires i < length(xs) && prefix == take(i, xs) && suffix == drop(i+1, xs);
  ensures update(i, x, xs) == append(prefix, cons(x, suffix));

lemma void buffer_from_chars(char *buffer, size_t N, size_t M);
  requires chars(buffer, N*M, ?abs);
  ensures exists<list<list<char> > >(?elements) &*& buffer(buffer, N, M, elements) &*& length(elements) == N;

lemma void split_element<t>(char *buffer, size_t N, size_t M, size_t i);
  requires buffer(buffer, N, M, ?elements) &*& i < N;
  ensures
    buffer(buffer,               i * M,       M, take(i, elements)) &*&
    chars( buffer + i * M,       M,              nth(i, elements)) &*&
    buffer(buffer + (i + 1) * M, (N-1-i) * M, M, drop(i+1, elements));
    
lemma void join_element(char *buffer, size_t N, size_t M, size_t i);
  requires
    buffer(buffer,               i * M,       M, ?prefix) &*&
    chars( buffer + i * M,       M,              ?element) &*&
    buffer(buffer + (i + 1) * M, (N-1-i) * M, M, ?suffix);
  ensures buffer(buffer, N, M, append(prefix, cons(element, suffix)));

predicate queue(struct queue *q, size_t W, size_t R, size_t N, size_t M, size_t K, list<list<char> > abs) =
  malloc_block_queue(q) &*&
  q->buffer |-> ?buffer &*&
  q->W |-> W &*&
  q->R |-> R &*&
  q->N |-> N &*&
  q->K |-> K &*&
  q->M |-> M &*&
  0 <= W &*& W < N &*&
  0 <= R &*& R < N &*&
  0 < N &*& 0 < M &*&
  0 <= K &*& K <= N &*&
  W == (R + 1 + K) % N &*&
  buffer(buffer, N, M, ?contents) &*&
  length(contents) == N &*&
  take(K, rotate_left((R+1)%N, contents)) == abs &*&
  malloc_block(buffer, N*M);
@*/

struct queue *create_queue(size_t N, size_t M)
  //@ requires 0 < N &*& 0 < M;
  //@ ensures queue(result, 0, (N-1), N, M, 0, nil);
{
  struct queue *q = malloc(sizeof(struct queue));
  char *buffer = malloc(N*M);
  if (!q || !buffer) abort();
  q->buffer = buffer;
  q->W = 0;
  q->R = (N-1);
  q->N = N;
  q->M = M;
  q->K = 0;
  //@buffer_from_chars(buffer, N, M);
  //@assert buffer(buffer, N, M, ?elements);
  //@close queue(q, 0, (N-1), N, M, 0, nil);
  return q;
}

bool deq(struct queue *q, char *x)
  //@ requires queue(q, ?W, ?R, ?N, ?M, ?K, ?abs) &*& chars(x, M, ?xold);
  /*@ ensures
        result != (K == 0) &*&
        (result ? queue(q, W, (R+1)%N, N, M, (K-1), tail(abs))
                : queue(q, W, R,       N, M, K,     abs)) &*&
        chars(x, M, ?xnew) &*& xnew == (result ? head(abs) : xold);
  @*/
{
  //@open queue(q, W, R, N, M, K, abs);
  if (q->K == 0) {
    //@close queue(q, W, R, N, M, K, abs);
    return false;
  }
  //@assert q->buffer |-> ?buffer;
  //@assert buffer(buffer, N, M, ?contents);
  q->R = (q->R + 1) % q->N;
  //@split_element(buffer, N, M, (R+1)%N);
  //@assert buffer(buffer                , (R+1)%N * M, M, ?prefix);
  //@assert chars( buffer + ((R+1)%N) * M, M, ?element);
  //@assert buffer(buffer + ((R+1)%N + 1) * M, (N-1-(R+1)%N) * M, M, ?suffix);
  memcpy(x, q->buffer + (q->R * q->M), q->M);
  q->K--;
  //@combine_list_no_change(prefix, element, suffix, (R+1)%N, contents);
  //@mod_plus_distr(R+1, K, N);
  //@assert 0 < K && K <= N;
  //@length_take(K, contents);
  //@take_length_eq(K, rotate_left((R+1)%N, contents), abs);
  //@assert abs == cons(?z, _);
  //@deq_lemma(K, (R+1)%N, contents, abs, z);
  //@join_element(buffer, N, M, (R+1)%N);
  //@close queue(q, W, (R+1)%N, N, M, (K-1), tail(abs));
  //@deq_value_lemma(K, (R+1)%N, contents, abs);
  //@assert z == element;
  return true;
}


bool enq(struct queue *q, char *x)
  //@ requires queue(q, ?W, ?R, ?N, ?M, ?K, ?abs) &*& chars(x, M, ?val);
  /*@ ensures
        chars(x, M, val) &*&
        result != (K == N) &*&
        result ? queue(q, (W+1)%N, R, N, M, (K+1), append(abs, cons(val, nil)))
               : queue(q, W,       R, N, M, K,     abs);
  @*/
{
  //@open queue(q, W, R, N, M, K, abs);
  if (q->K == q->N) {
    //@close queue(q, W, R, N, M, K, abs);
    return false;
  }
  //@assert q->buffer |-> ?buffer;
  //@assert buffer(buffer, N, M, ?contents);
  //@assert take(K, rotate_left((R+1)%N, contents)) == abs;
  //@split_element(buffer, N, M, W);
  //@assert buffer(buffer                , W * M, M, ?prefix);
  //@assert chars( buffer + (W * M), M, ?element);
  //@assert buffer(buffer + (W + 1) * M, (N-1-W) * M, M, ?suffix);
  memcpy(q->buffer + (q->W * q->M), x, q->M);
  q->W = (q->W + 1) % q->N;
  //@assert q->W == (W + 1)%N;
  q->K++;
  //@enq_lemma(K, (R+1)%N, contents, abs, val);
  //@mod_plus_distr(R+1, K, N);
  //@assert W == (R + 1 + K) % N;
  //@mod_plus_one(W, R + 1 + K, N);
  //@assert((W+1)%N == ((R + 1) + (K + 1)) % N);
  //@join_element(buffer, N, M, W);
  //@assert(take(K+1, rotate_left((R+1)%N, update(W, val, contents))) == append(abs, cons(val, nil)));
  //@combine_list_update(prefix, val, suffix, W, contents);
  //@close queue(q, (W+1)%N, R, N, M, (K+1), append(abs, cons(val, nil)));
  return true;
}

/*@
fixpoint list<t> singleton<t>(t x) {
  return cons(x, nil);
}
@*/

int main()
  //@requires true;
  //@ensures true;
{
  char x;
  struct queue *q = create_queue(8, 1);
  //@assert queue(q, /*W*/0, /*R*/7, /*N*/8, /*M*/1, /*K*/0, /*abs*/nil);
  x = 'a'; bool result = enq(q, &x); assert result;
  //@assert queue(q, /*W*/1, /*R*/7, /*N*/8, /*M*/1, /*K*/1, /*abs*/cons(singleton('a'), nil));
  x = 'b'; result = enq(q, &x); assert result;
  //@assert queue(q, /*W*/2, /*R*/7, /*N*/8, /*M*/1, /*K*/2, /*abs*/cons(singleton('a'), cons(singleton('b'), nil)));
  x = 'c'; result = enq(q, &x); assert result;
  //@assert queue(q, /*W*/3, /*R*/7, /*N*/8, /*M*/1, /*K*/3, /*abs*/cons(singleton('a'), cons(singleton('b'), cons(singleton('c'), nil))));
  
  char *c = malloc(1);
  if (!c) abort();
  *c = 'z';
  result = deq(q, c); assert result;
  //@assert queue(q, /*W*/3, /*R*/0, /*N*/8, /*M*/1, /*K*/2, /*abs*/cons(singleton('b'), cons(singleton('c'), nil)));
  //@assert character(c, 'a');
  result = deq(q, c); assert result;
  //@assert queue(q, /*W*/3, /*R*/1, /*N*/8, /*M*/1, /*K*/1, /*abs*/cons(singleton('c'), nil));
  //@assert character(c, 'b');
  return 0;
  //@leak queue(q, _, _, _, _, _, _);
  //@leak malloc_block(c, _);
  //@leak character(c, _);
}
