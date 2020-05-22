#include <stdlib.h>
//@ #include <listex.gh>

struct queue {
  char *buffer; //< [ 0 1 2 3 4 5 ... (N-1) ]
  size_t W;
  size_t R;
  size_t N;
//implicitly M=1
  size_t K;
};

/*@
fixpoint list<t> rotate_left<t>(int n, list<t> xs) {
  return append(drop(n, xs), take(n, xs));
}

lemma_auto void rotate_length<t>(int n, list<t> xs)
  requires 0 <= n && n <= length(xs);
  ensures length(rotate_left(n, xs)) == length(xs);
{}

lemma void take_length_eq<t>(int k, list<t> xs, list<t> ys)
  requires 0 <= k && k <= length(xs) && take(k, xs) == ys;
  ensures length(ys) == k;
{}

lemma_auto void mod_same(int n)
  requires 0 < n;
  ensures n % n == 0;
{
  div_rem_nonneg(n, n);
  if (n / n < 1) {} else if (n / n > 1) {
    mul_mono_l(2, n/n, n);
  } else {}
}

lemma void mod_lt(int x, int n)
  requires 0 <= x && x < n;
  ensures x % n == x;
{
  div_rem_nonneg(x, n);
  if (x / n > 0) {
    mul_mono_l(1, x / n, n);
  } else {
  }
}

lemma void note(bool b)
  requires b;
  ensures b;
{}

lemma void mod_plus_one(int x, int y, int n)
  requires 0 <= y && 0 < n && x == (y % n);
  ensures ((x+1) % n) == ((y+1) % n);
{
  div_rem_nonneg(y, n);
  div_rem_nonneg(y+1, n);
  div_rem_nonneg(y%n+1, n);
  if (y%n+1 < n) {
    mod_lt(y%n+1, n);
    assert y%n == y - y/n*n;
    assert (y+1)%n == y + 1 - (y + 1)/n*n;
    if ((y+1)/n > y/n) {
      mul_mono_l(y/n + 1, (y+1)/n, n);
    } else if ((y+1)/n < y/n) {
      mul_mono_l((y+1)/n + 1, y/n, n);
    }
    assert y - (y+1)/n*n == y - y/n*n;
    assert y+1 - (y+1)/n*n == y - y/n*n + 1;
    assert (y+1)%n == y%n + 1;
  } else {
    assert y%n+1 == n;
    assert (y%n+1)%n == 0;
    if (y/n + 1 < (y+1)/n) {
      mul_mono_l(y/n + 2, (y+1)/n, n);
    } else if (y/n + 1 > (y+1)/n) {
      mul_mono_l((y+1)/n, y/n, n);
    }
    assert (y+1)/n == y/n + 1;
    note((y+1)/n*n == (y/n + 1)*n);
    assert (y+1)%n == 0;
  }
  assert (y%n+1)%n == (y+1)%n;
}

lemma void mod_mul(int x, int n, int y)
  requires 0 < n && 0 <= x && 0 <= y;
  ensures (x*n + y)%n == y%n;
{
  mul_mono_l(0, x, n);
  div_rem_nonneg(x*n+y, n);
  div_rem_nonneg(y, n);
  
  if ((x*n+y)/n > x + y/n) {
    mul_mono_l(x + y/n + 1, (x*n+y)/n, n);
  } else if ((x*n+y)/n < x + y/n) {
    mul_mono_l((x*n+y)/n + 1, x + y/n, n);
  }
  note((x*n + y)/n == x + y/n);
  note((x*n + y)/n*n == (x + y/n)*n);
}

lemma void mod_plus_distr(int x, int y, int n)
  requires 0 < n && 0 <= x && 0 <= y;
  ensures ((x % n) + y) % n == (x + y) % n;
{
  div_rem_nonneg(x, n);
  div_rem_nonneg(x%n+y, n);
  div_rem_nonneg(x+y, n);
  
  assert x == x/n*n + x%n;
  mod_mul(x/n, n, x%n + y);
}

lemma_auto void mod_range(int x, int n)
  requires 0 <= x && 0 < n;
  ensures 0 <= (x % n) && (x % n) < n;
{
  div_rem_nonneg(x, n);
}

lemma void drop_update_le<t>(int i, int j, t x, list<t> xs)
  requires 0 <= i && i <= j && j < length(xs);
  ensures drop(i, update(j, x, xs)) == update(j - i, x, drop(i, xs));
{
  switch (xs) {
  case nil:
  case cons(x0, xs0):
    if (i == 0) {
    } else {
      drop_update_le(i - 1, j - 1, x, xs0);
    }
  }
}

lemma void drop_update_ge<t>(int i, int j, t x, list<t> xs)
  requires 0 <= j && j < i && i < length(xs);
  ensures drop(i, update(j, x, xs)) == drop(i, xs);
{
  switch (xs) {
  case nil:
  case cons(x0, xs0):
    if (j == 0) {
    } else {
      drop_update_ge(i - 1, j - 1, x, xs0);
    }
  }
}

lemma void take_update_le<t>(int i, int j, t x, list<t> xs)
  requires 0 <= i && i <= j;
  ensures take(i, update(j, x, xs)) == take(i, xs);
{
  switch (xs) {
  case nil:
  case cons(x0, xs0):
    if (i == 0) {
    } else {
      take_update_le(i - 1, j - 1, x, xs0);
    }
  }
}

lemma void take_update_ge<t>(int i, int j, t x, list<t> xs)
  requires 0 <= j && j < i && i <= length(xs);
  ensures take(i, update(j, x, xs)) == update(j, x, take(i, xs));
{
  switch (xs) {
  case nil:
  case cons(x0, xs0):
    if (j == 0) {
    } else {
      take_update_ge(i - 1, j - 1, x, xs0);
    }
  }
}

lemma void update_eq_append<t>(int i, t x, list<t> xs)
  requires 0 <= i && i < length(xs);
  ensures update(i, x, xs) == append(take(i, xs), cons(x, drop(i + 1, xs)));
{
  switch (xs) {
  case nil:
  case cons(x0, xs0):
    if (i == 0) {
    } else {
      update_eq_append(i - 1, x, xs0);
    }
  }
}

lemma void take_append_ge<t>(int n, list<t> xs, list<t> ys)
  requires length(xs) <= n;
  ensures take(n, append(xs, ys)) == append(xs, take(n - length(xs), ys));
{
  switch (xs) {
  case nil:
  case cons(x0, xs0):
    take_append_ge(n - 1, xs0, ys);
  }
}

lemma void take_take<t>(int m, int n, list<t> xs)
  requires 0 <= m && m <= n && n <= length(xs);
  ensures take(m, take(n, xs)) == take(m, xs);
{
  switch (xs) {
  case nil:
  case cons(x0, xs0):
    if (m == 0) {} else {
      take_take(m - 1, n - 1, xs0);
    }
  }
}

lemma void mod_in_range(int x, int n);
  requires 0 < n && 0 <= x && x < n;
  ensures ((x % n) == x);

lemma_auto void mod_mod(int x, int n);
  requires true;
  ensures (x % n) % n == (x % n);

lemma void mod_plus(int x, int y, int n);
  requires true;
  ensures (x + y) % n == ((x % n) + (y % n)) % n;

lemma void enq_lemma<t>(int k, int i, list<t> xs, list<t> ys, t z)
  requires 0 <= k && 0 <= i && 0 < length(xs) && k < length(xs) && i < length(xs) && take(k, rotate_left(i, xs)) == ys;
  ensures take(k+1, rotate_left(i, update((i+k)%length(xs), z, xs))) == append(ys, cons(z, nil));
{
  int j = (i+k)%length(xs);
  assert take(k, append(drop(i, xs), take(i, xs))) == ys;
  if (i + k < length(xs)) {
    mod_lt(i + k, length(xs));
    assert j == i + k;
    drop_update_le(i, i + k, z, xs);
    assert drop(i, update(i + k, z, xs)) == update(k, z, drop(i, xs));
    take_update_le(i, i + k, z, xs);
    assert take(i, update(i + k, z, xs)) == take(i, xs);
    take_append(k+1, update(k, z, drop(i, xs)), take(i, xs));
    assert take(k+1, append(update(k, z, drop(i, xs)), take(i, xs))) == take(k+1, update(k, z, drop(i, xs)));
    update_eq_append(k, z, drop(i, xs));
    assert update(k, z, drop(i, xs)) == append(take(k, drop(i, xs)), cons(z, drop(k + 1, drop(i, xs))));
    take_append_ge(k+1, take(k, drop(i, xs)), cons(z, drop(k + 1, drop(i, xs))));
    assert take(k+1, append(take(k, drop(i, xs)), cons(z, drop(k + 1, drop(i, xs))))) ==
           append(take(k, drop(i, xs)), {z});
    take_append(k, drop(i, xs), take(i, xs));
    assert take(k+1, append(take(k, drop(i, xs)), cons(z, drop(k + 1, drop(i, xs))))) ==
           append(take(k, append(drop(i, xs), take(i, xs))), {z});
    assert take(k+1, update(k, z, drop(i, xs))) ==
           append(take(k, append(drop(i, xs), take(i, xs))), {z});
    assert take(k+1, append(update(k, z, drop(i, xs)), take(i, xs))) ==
           append(take(k, append(drop(i, xs), take(i, xs))), {z});
    assert take(k+1, append(drop(i, update(i + k, z, xs)), take(i, update(i + k, z, xs)))) ==
           append(take(k, append(drop(i, xs), take(i, xs))), {z});
    
  } else {
    assert i + k < 2 * length(xs);
    div_rem_nonneg(i + k, length(xs));
    if ((i + k) / length(xs) > 1) {
      mul_mono_l(2, (i + k) / length(xs), length(xs));
    } else if ((i + k) / length(xs) < 1) {
      mul_mono_l((i + k) / length(xs), 0, length(xs));
    }
    assert j == i + k - length(xs);
    assert j < i;
    drop_update_ge(i, j, z, xs);
    assert drop(i, update(j, z, xs)) == drop(i, xs);
    take_update_ge(i, j, z, xs);
    assert update(j, z, take(i, xs)) == take(i, update(j, z, xs));
    take_append_ge(k+1, drop(i, xs), take(i, update(j, z, xs)));
    assert take(k+1, append(drop(i, update(j, z, xs)), take(i, update(j, z, xs)))) ==
           append(drop(i, xs), take(j+1, update(j, z, take(i, xs))));
    update_eq_append(j, z, take(i, xs));
    assert update(j, z, take(i, xs)) == append(take(j, take(i, xs)), cons(z, drop(j + 1, take(i, xs))));
    take_take(j, i, xs);
    assert update(j, z, take(i, xs)) == append(take(j, xs), cons(z, drop(j+1, take(i, xs))));
    take_append_ge(j+1, take(j, xs), cons(z, drop(j+1, take(i, xs))));
    assert append(drop(i, xs), take(j+1, update(j, z, take(i, xs)))) ==
           append(drop(i, xs), append(take(j, xs), {z}));
    take_append_ge(k, drop(i, xs), take(i, xs));
    append_assoc(drop(i, xs), take(j, xs), {z});
    assert append(drop(i, xs), append(take(j, xs), {z})) ==
           append(take(k, append(drop(i, xs), take(i, xs))), {z});
    assert append(drop(i, xs), take(j+1, update(j, z, take(i, xs)))) ==
           append(take(k, append(drop(i, xs), take(i, xs))), {z});
  }
  assert take(k+1, append(drop(i, update(j, z, xs)), take(i, update(j, z, xs)))) ==
         append(take(k, append(drop(i, xs), take(i, xs))), {z});
  assert take(k+1, append(drop(i, update(j, z, xs)), take(i, update(j, z, xs)))) == append(ys, {z});
}

// Following lemma (unproven in Verifast)
lemma void front_enq_lemma<t>(int k, int i, list<t> xs, list<t> ys, t z);
  requires 0 < length(xs) && k < length(xs) && i < length(xs) && take(k, rotate_left((i+1)%length(xs), xs)) == ys;
  ensures take(k+1, rotate_left(i, update(i, z, xs))) == cons(z, ys);

lemma void deq_lemma<t>(int k, int i, list<t> xs, list<t> ys, t z)
  requires 0 < k && k <= length(xs) && 0 <= i && i < length(xs) && take(k, rotate_left(i, xs)) == ys && z == head(ys);
  ensures take(k-1, rotate_left((i+1)%length(xs), xs)) == tail(ys);
{
  int j = (i+1)%length(xs);
  drop_n_plus_one(i, xs);
  assert tail(take(k, append(drop(i, xs), take(i, xs)))) == take(k-1, append(drop(i+1, xs), take(i, xs)));
  if (i+1 < length(xs)) {
    mod_lt(i+1, length(xs));
    assert j == i+1;
    if (k-1 <= length(xs)-j) {
      take_append(k-1, drop(j, xs), take(j, xs));
      take_append(k-1, drop(j, xs), take(i, xs));
    } else {
      assert k+i > length(xs);
      take_append_ge(k-1, drop(j, xs), take(j, xs));
      take_append_ge(k-1, drop(j, xs), take(i, xs));
      assert k-1-(length(xs)-j) == k+i-length(xs);
      assert k+i-length(xs) <= i;
      take_take(k+i-length(xs), j, xs);
      take_take(k+i-length(xs), i, xs);
      assert take(k+i-length(xs), take(j, xs)) == take(k+i-length(xs), take(i, xs));
    }
  } else {
    assert i+1 == length(xs);
    assert (i+1)%length(xs) == 0;
    assert j == 0;
    assert append(drop(j, xs), take(j, xs)) == xs;
    assert append(drop(i+1, xs), take(i, xs)) == take(i, xs);
    take_append_ge(k-1, drop(i+1, xs), take(i, xs));
    take_take(k-1, i, xs);
  }
  assert take(k-1, append(drop(j, xs), take(j, xs))) == take(k-1, append(drop(i+1, xs), take(i, xs)));
  assert take(k-1, append(drop(j, xs), take(j, xs))) == tail(take(k, append(drop(i, xs), take(i, xs))));
}

lemma void deq_value_lemma<t>(int k, int i, list<t> xs, list<t> ys)
  requires 0 < k && k <= length(ys) && 0 <= i && i < length(xs) && take(k, rotate_left(i, xs)) == ys;
  ensures nth(i, xs) == head(ys);
{
  drop_n_plus_one(i, xs);
  assert nth(i, xs) == head(take(k, append(drop(i, xs), take(i, xs))));
}

predicate queue(struct queue *q, size_t W, size_t R, size_t N, size_t K; list<char> abs) =
  malloc_block_queue(q) &*&
  q->buffer |-> ?buffer &*&
  q->W |-> W &*&
  q->R |-> R &*&
  q->N |-> N &*&
  q->K |-> K &*&
  0 <= W &*& W < N &*&
  0 <= R &*& R < N &*&
  0 < N &*&
  0 <= K &*& K <= N &*&
  W == (R + 1 + K) % N &*&
  chars(buffer, N, ?contents) &*&
  abs == take(K, rotate_left((R+1)%N, contents)) &*&
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
  q->W = 0;
  q->R = (N-1);
  q->N = N;
  q->K = 0;
  return q;
}

bool deq(struct queue *q, char *x)
  //@ requires queue(q, ?W, ?R, ?N, ?K, ?abs) &*& character(x, ?xold);
  /*@ ensures
        result != (K == 0) &*&
        (result ? queue(q, W, (R+1)%N, N, (K-1), tail(abs)) : queue(q, W, R, N, K, abs)) &*&
        character(x, ?xnew) &*& xnew == (result ? head(abs) : xold); @*/
{
  if (q->K == 0) {
    return false;
  }
  //@assert q->buffer |-> ?buffer;
  //@assert chars(buffer, N, ?contents);
  q->R = (q->R + 1) % q->N;
  *x = q->buffer[q->R];
  q->K--;
  //@mod_plus_distr(R+1, K, N);
  //@length_take(K, contents);
  //@take_length_eq(K, rotate_left((R+1)%N, contents), abs);
  //@deq_lemma(K, (R+1)%N, contents, abs, head(abs));
  //@deq_value_lemma(K, (R+1)%N, contents, abs);
  return true;
}

bool enq_to_front(struct queue *q, char x)
  //@ requires queue(q, ?W, ?R, ?N, ?K, ?abs);
  //@ ensures result != (K == N) &*& result ? queue(q, W, (R == 0 ? (N-1) : (R-1)), N, (K+1), cons(x, abs)) : queue(q, W, R, N, K, abs);
{
  if (q->K == q->N) {
    return false;
  }
  //@assert q->buffer |-> ?buffer;
  //@assert chars(buffer, N, ?contents);
  //@assert W == (R + 1 + K) % N;
  q->buffer[q->R] = x;
  q->R = (q->R == 0 ? (q->N - 1) : (q->R - 1));
  //@if (0 < R)  { assert q->R == (R-1); assert W == ((R - 1) + 1 + (K + 1)) % N; }
  /*@if (0 == R) { assert q->R == (N-1); mod_plus((N-1) + 1, K + 1, N); }
  @*/
  //@assert W == ((R == 0 ? (N-1) : (R-1)) +1 + (K+1)) % N;
  q->K++;
  //@front_enq_lemma(K, R, contents, abs, x);
  /*@if (0 < R)  {
      assert cons(x,abs) == take(K+1, rotate_left(R, update(R, x, contents)));
      mod_in_range(R, N);
      assert ((R-1) + 1) % N == R;
    } @*/
  //@if (0 == R) { assert cons(x,abs) == take(K+1, rotate_left(0, update(0, x, contents))); }
  //@close queue(q, W, (R == 0 ? (N-1) : (R-1)), N, (K+1), cons(x, abs));
  return true;
}

bool enq(struct queue *q, char x)
  //@ requires queue(q, ?W, ?R, ?N, ?K, ?abs);
  //@ ensures result != (K == N) &*& result ? queue(q, (W+1)%N, R, N, (K+1), append(abs, cons(x, nil))) : queue(q, W, R, N, K, abs);
{
  if (q->K == q->N) {
    return false;
  }
  //@assert q->buffer |-> ?buffer;
  //@assert chars(buffer, N, ?contents);
  q->buffer[q->W] = x;
  q->W = (q->W + 1) % q->N;
  q->K++;
  //@enq_lemma(K, (R+1)%N, contents, abs, x);
  //@mod_plus_distr(R+1, K, N);
  //@mod_plus_one(W, R + 1 + K, N);
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

  result = enq_to_front(q, 'd'); assert result;
  //@assert queue(q, /*W*/3, /*R*/0, /*N*/8, /*K*/2, /*abs*/cons('d', cons('c', nil)));
  result = deq(q, c); assert result;
  //@assert queue(q, /*W*/3, /*R*/_, /*N*/8, /*K*/1, /*abs*/cons('c', nil));
  //@assert character(c, 'd');

  return 0;
  //@leak queue(q, _, _, _, _, _);
  //@leak malloc_block(c, _);
  //@leak character(c, _);
}
