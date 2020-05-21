#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef size_t TickType_t;
typedef size_t UBaseType_t;
typedef ssize_t BaseType_t;
#define pdPASS 1
#define pdTRUE 1
#define pdFALSE 0

typedef struct QueuePointers {
  int8_t *pcTail; /*< Points to the byte at the end of the queue storage area.
                     Once more byte is allocated than necessary to store the
                     queue items, this is used as a marker. */
  int8_t *pcReadFrom; /*< Points to the last place that a queued item was read
                         from when the structure is used as a queue. */
} QueuePointers_t;

typedef struct SemaphoreData {
  int8_t *dummy1;
  int8_t *dummy2;
} SemaphoreData_t;

struct fake_union_t {
  QueuePointers_t xQueue;
  SemaphoreData_t xSemaphore;
};

// TODO: realistic list struct
typedef struct xLIST {
  int x;
} List_t;

typedef struct QueueDefinition /* The old naming convention is used to prevent
                                  breaking kernel aware debuggers. */
{
  int8_t *pcHead;    /*< Points to the beginning of the queue storage area. */
  int8_t *pcWriteTo; /*< Points to the free next place in the storage area. */

  struct fake_union_t u;

  List_t xTasksWaitingToSend; /*< List of tasks that are blocked waiting to post
                                 onto this queue.  Stored in priority order. */
  List_t
      xTasksWaitingToReceive; /*< List of tasks that are blocked waiting to read
                                 from this queue.  Stored in priority order. */

  volatile UBaseType_t
      uxMessagesWaiting; /*< The number of items currently in the queue. */
  UBaseType_t uxLength;  /*< The length of the queue defined as the number of
                            items it will hold, not the number of bytes. */
  UBaseType_t
      uxItemSize; /*< The size of each items that the queue will hold. */

  volatile int8_t
      cRxLock; /*< Stores the number of items received from the queue (removed
                  from the queue) while the queue was locked.  Set to
                  queueUNLOCKED when the queue is not locked. */
  volatile int8_t
      cTxLock; /*< Stores the number of items transmitted to the queue (added to
                  the queue) while the queue was locked.  Set to queueUNLOCKED
                  when the queue is not locked. */
} xQUEUE;

typedef xQUEUE Queue_t;

typedef struct QueueDefinition * QueueHandle_t;

/*@
fixpoint list<t> rotate<t>(int n, list<t> xs) {
  return append(drop(n, xs), take(n, xs));
}

predicate queue_init1(QueueHandle_t q) =
  malloc_block_QueueDefinition(q) &*&
  q->pcHead |-> _ &*&
  q->pcWriteTo |-> _ &*&
  q->u.xQueue.pcTail |-> _ &*&
  q->u.xQueue.pcReadFrom |-> _ &*&
  q->xTasksWaitingToSend.x |-> _ &*&    //< TODO: list shape
  q->xTasksWaitingToReceive.x |-> _ &*&
  q->uxItemSize |-> _ &*&
  q->uxLength |-> _ &*&
  q->uxMessagesWaiting |-> _ &*&
  q->cRxLock |-> _ &*&
  q->cTxLock |-> _ &*&
  struct_QueuePointers_padding(&q->u.xQueue) &*&
  struct_SemaphoreData_padding(&q->u.xSemaphore) &*&
  struct_fake_union_t_padding(&q->u) &*&
  struct_xLIST_padding(&q->xTasksWaitingToSend) &*&
  struct_xLIST_padding(&q->xTasksWaitingToReceive) &*&
  q->u.xSemaphore.dummy1 |-> _ &*&
  q->u.xSemaphore.dummy2 |-> _ &*&
  true
  ;

predicate queue_init2(QueueHandle_t q, size_t N, size_t M) =
  malloc_block_QueueDefinition(q) &*&
  q->pcHead |-> ?Start &*&
  q->pcWriteTo |-> _ &*&
  q->u.xQueue.pcTail |-> _ &*&
  q->u.xQueue.pcReadFrom |-> _ &*&
  q->xTasksWaitingToSend.x |-> _ &*&    //< TODO: list shape
  q->xTasksWaitingToReceive.x |-> _ &*&
  q->uxItemSize |-> M &*&
  q->uxLength |-> N &*&
  q->uxMessagesWaiting |-> _ &*&
  q->cRxLock |-> _ &*&
  q->cTxLock |-> _ &*&
  struct_QueuePointers_padding(&q->u.xQueue) &*&
  struct_SemaphoreData_padding(&q->u.xSemaphore) &*&
  struct_fake_union_t_padding(&q->u) &*&
  struct_xLIST_padding(&q->xTasksWaitingToSend) &*&
  struct_xLIST_padding(&q->xTasksWaitingToReceive) &*&
  q->u.xSemaphore.dummy1 |-> _ &*&
  q->u.xSemaphore.dummy2 |-> _ &*&
  /* new constraints */
  0 < N &*&
  chars(Start, (N*M), _) &*&
  malloc_block(Start, N*M) &*&
  true
  ;

predicate buffer(char *buffer, size_t N, size_t M; list<list<char> > elements) =
    N == 0 ?
        elements == nil
    :
        chars(buffer, M, ?x) &*& buffer(buffer + M, N - 1, M, ?xs) &*& elements == cons(x, xs);

predicate queue(QueueHandle_t q, size_t N, size_t M, size_t W, size_t R, size_t K; list<list<char> >abs) =
  malloc_block_QueueDefinition(q) &*&
  q->pcHead |-> ?Start &*&
  q->pcWriteTo |-> ?WPtr &*&
  q->u.xQueue.pcTail |-> ?End &*&
  q->u.xQueue.pcReadFrom |-> ?RPtr &*&
  q->xTasksWaitingToSend.x |-> _ &*&    //< TODO: list shape
  q->xTasksWaitingToReceive.x |-> _ &*&
  q->uxItemSize |-> M &*&
  q->uxLength |-> N &*&
  q->uxMessagesWaiting |-> K &*&
  q->cRxLock |-> ?rxLock &*&
  q->cTxLock |-> ?txLock &*&
  struct_QueuePointers_padding(&q->u.xQueue) &*&
  struct_SemaphoreData_padding(&q->u.xSemaphore) &*&
  struct_fake_union_t_padding(&q->u) &*&
  struct_xLIST_padding(&q->xTasksWaitingToSend) &*&
  struct_xLIST_padding(&q->xTasksWaitingToReceive) &*&
  q->u.xSemaphore.dummy1 |-> _ &*&
  q->u.xSemaphore.dummy2 |-> _ &*&
  /* new constraints */
  0 < N &*&
  0 < M &*&
  0 <= W &*& W < N &*&
  0 <= R &*& R < N &*&
  0 <= K &*& K <= N &*&
  W == (R + 1 + K) % N &*&
  (-1) <= rxLock &*&
  (-1) <= txLock &*&
  WPtr == Start + (W*M) &*&
  RPtr == Start + (R*M) &*&
  End == Start + (N*M) &*&
  buffer(Start, N, M, ?contents) &*&
  length(contents) == N &*&
  abs == take(K, rotate((R+1)%N, contents)) &*&
  malloc_block(Start, N*M) &*&
  true
  ;

predicate mutex(QueueHandle_t q, size_t N, size_t K) =
  malloc_block_QueueDefinition(q) &*&
  q->pcHead |-> ?Start &*&
  q->pcWriteTo |-> ?WPtr &*&
  q->u.xQueue.pcTail |-> ?End &*&
  q->u.xQueue.pcReadFrom |-> ?RPtr &*&
  q->xTasksWaitingToSend.x |-> ?SendList &*&
  q->xTasksWaitingToReceive.x |-> ?RecvList &*&
  q->uxItemSize |-> 0 &*&
  q->uxLength |-> N &*&
  q->uxMessagesWaiting |-> K &*&
  q->cRxLock |-> ?rxLock &*&
  q->cTxLock |-> ?txLock &*&
  0 < N &*&
  0 <= K &*& K <= N &*&
  (-1) <= rxLock &*&
  (-1) <= txLock &*&
  WPtr == Start &*&
  RPtr == Start &*&
  End == Start &*&
  malloc_block(Start, 0) &*&
  chars(Start, 0, _) &*&
  struct_QueuePointers_padding(&q->u.xQueue) &*&
  struct_SemaphoreData_padding(&q->u.xSemaphore) &*&
  struct_fake_union_t_padding(&q->u) &*&
  struct_xLIST_padding(&q->xTasksWaitingToSend) &*&
  struct_xLIST_padding(&q->xTasksWaitingToReceive) &*&
  q->u.xSemaphore.dummy1 |-> _ &*&
  q->u.xSemaphore.dummy2 |-> _ &*&
  true
  ;

lemma_auto void mod_same(int n);
  requires 0 < n;
  ensures n % n == 0;

lemma_auto void mod_range(int x, int n);
  requires 0 < n;
  ensures 0 <= (x % n) && (x % n) < n;
  
lemma void mod_in_range(int x, int n);
  requires 0 < n && 0 <= x && x < n;
  ensures ((x % n) == x);

lemma void mod_plus_distr(int x, int y, int n);
  requires 0 < n;
  ensures ((x % n) + y) % n == (x + y) % n;

lemma_auto void rotate_length<t>(int n, list<t> xs)
  requires 0 <= n && n <= length(xs);
  ensures length(rotate(n, xs)) == length(xs);
{}

lemma void take_length_eq<t>(int k, list<t> xs, list<t> ys)
  requires 0 <= k && k <= length(xs) && take(k, xs) == ys;
  ensures length(ys) == k;
{}

lemma void buffer_from_chars(char *buffer, size_t N, size_t M);
  requires chars(buffer, N*M, _);
  ensures exists<list<list<char> > >(?elements) &*& buffer(buffer, N, M, elements) &*& length(elements) == N;
  
lemma void split_element<t>(char *buffer, size_t N, size_t M, size_t i);
  requires buffer(buffer, N, M, ?elements) &*& i < N;
  ensures
    buffer(buffer, i, M, take(i, elements)) &*&
    chars(buffer + i * M, M, nth(i, elements)) &*&
    buffer(buffer + (i + 1) * M, (N-1-i), M, drop(i+1, elements));
    
lemma void join_element(char *buffer, size_t N, size_t M, size_t i);
  requires
    buffer(buffer, i, M, ?prefix) &*&
    chars(buffer + i * M, M, ?element) &*&
    buffer(buffer + (i + 1) * M, (N-1-i), M, ?suffix);
  ensures buffer(buffer, N, M, append(prefix, cons(element, suffix)));
  
lemma void enq_lemma<t>(int k, int i, list<t> xs, list<t> ys, t z);
  requires 0 < length(xs) && k < length(xs) && i < length(xs) && take(k, rotate(i, xs)) == ys;
  ensures take(k+1, rotate(i, update((i+k)%length(xs), z, xs))) == append(ys, cons(z, nil));
  
lemma void combine_list_update<t>(list<t>prefix, t x, list<t>suffix, size_t i, list<t> xs);
  requires i < length(xs) && prefix == take(i, xs) && suffix == drop(i+1, xs);
  ensures update(i, x, xs) == append(prefix, cons(x, suffix));
  
fixpoint list<t> singleton<t>(t x) {
  return cons(x, nil);
}
@*/

#define pvPortMalloc malloc
#define pvPortFree free
#define configASSERT(x) { if (!(x)) { abort(); } }
#define traceQUEUE_CREATE_FAILED(x)
#define traceQUEUE_CREATE(x)
#define mtCOVERAGE_TEST_MARKER()

// TODO: model criticals with mutex
#define taskENTER_CRITICAL()
#define taskEXIT_CRITICAL()
#define portYIELD_WITHIN_API()

BaseType_t listLIST_IS_EMPTY(List_t *list);
  //@requires true;
  //@ensures true;
  
BaseType_t xTaskRemoveFromEventList(List_t *list);
  //@requires true;
  //@ensures true;
  
BaseType_t vListInitialise(List_t *list);
  //@requires true;
  //@ensures true;

#define queueSEND_TO_BACK 1

static BaseType_t prvCopyDataToQueue(Queue_t *const pxQueue,
                                     const void *pvItemToQueue,
                                     const BaseType_t xPosition)
  //@requires queue(pxQueue, ?N, ?M, ?W, ?R, ?K, ?abs) &*& K < N &*& chars(pvItemToQueue, M, ?x) &*& xPosition == queueSEND_TO_BACK;
  //@ensures queue(pxQueue, N, M, (W+1)%N, R, (K+1), append(abs, singleton(x))) &*& chars(pvItemToQueue, M, x);
{
  BaseType_t xReturn = pdFALSE;
  UBaseType_t uxMessagesWaiting;

  /* This function is called from a critical section. */

  uxMessagesWaiting = pxQueue->uxMessagesWaiting;
  //@assert pxQueue->pcHead |-> ?buffer;
  //@assert buffer(buffer, N, M, ?contents);
  //@assert take(K, rotate((R+1)%N, contents)) == abs;
  if (pxQueue->uxItemSize == /*(UBaseType_t)*/0) {
    //@assert false; //< this case is unreachable for queues
    {
      if (pxQueue->pcHead == NULL) {
        /* The mutex is no longer being held. */
        xReturn = xTaskPriorityDisinherit(pxQueue->u.xSemaphore.xMutexHolder);
        pxQueue->u.xSemaphore.xMutexHolder = NULL;
      } else {
        mtCOVERAGE_TEST_MARKER();
      }
    }

  } else if (xPosition == queueSEND_TO_BACK) {
    //@split_element(buffer, N, M, W);
    //@assert buffer(buffer, W, M, ?prefix);
    //@assert chars(buffer + W * M, M, _);
    //@assert buffer(buffer + (W + 1) * M, (N-1-W), M, ?suffix);
    memcpy(
        (void *)pxQueue->pcWriteTo, pvItemToQueue,
        (size_t)pxQueue
            ->uxItemSize); /*lint !e961 !e418 !e9087 MISRA exception as the
                              casts are only redundant for some ports, plus
                              previous logic ensures a null pointer can only be
                              passed to memcpy() if the copy size is 0.  Cast to
                              void required by function signature and safe as no
                              alignment requirement and copy length specified in
                              bytes. */
    //@join_element(buffer, N, M, W);
    //@combine_list_update(prefix, x, suffix, W, contents);
    //@ assert pxQueue->pcWriteTo == buffer + (W * M);
    pxQueue->pcWriteTo +=
        pxQueue->uxItemSize; /*lint !e9016 Pointer arithmetic on char types ok,
                                especially in this use case where it is the
                                clearest way of conveying intent. */
    //@ assert pxQueue->pcWriteTo == buffer + (W * M) + M;
    //@ assert pxQueue->pcWriteTo == buffer + (W + 1) * M;
    if (pxQueue->pcWriteTo >=
        pxQueue->u.xQueue
            .pcTail) /*lint !e946 MISRA exception justified as comparison of
                        pointers is the cleanest solution. */
    {
      //@ assume( W == (N-1) );
      pxQueue->pcWriteTo = pxQueue->pcHead;
      //@ assert pxQueue->pcWriteTo == buffer;
      //@ assert pxQueue->pcWriteTo == buffer + ((W + 1) % N) * M;
    } else {
      //@ assume( (W+1) < N );
      //@ mod_in_range((W+1), N);
      //@ assert pxQueue->pcWriteTo == buffer + ((W + 1) * M);
      //@ assume(pxQueue->pcWriteTo == buffer + (((W + 1) % N) * M));
      mtCOVERAGE_TEST_MARKER();
    }
    //@ assert(pxQueue->pcWriteTo == buffer + (((W + 1) % N) * M));
  } else {
    memcpy(
        (void *)pxQueue->u.xQueue.pcReadFrom, pvItemToQueue,
        (size_t)pxQueue
            ->uxItemSize); /*lint !e961 !e9087 !e418 MISRA exception as the
                              casts are only redundant for some ports.  Cast to
                              void required by function signature and safe as no
                              alignment requirement and copy length specified in
                              bytes.  Assert checks null pointer only used when
                              length is 0. */
    pxQueue->u.xQueue.pcReadFrom -= pxQueue->uxItemSize;
    if (pxQueue->u.xQueue.pcReadFrom <
        pxQueue->pcHead) /*lint !e946 MISRA exception justified as comparison of
                            pointers is the cleanest solution. */
    {
      pxQueue->u.xQueue.pcReadFrom =
          (pxQueue->u.xQueue.pcTail - pxQueue->uxItemSize);
    } else {
      mtCOVERAGE_TEST_MARKER();
    }

    if (xPosition == queueOVERWRITE) {
      if (uxMessagesWaiting > /*(UBaseType_t)*/0) {
        /* An item is not being added but overwritten, so subtract
                                    one from the recorded number of items in the
           queue so when one is added again below the number of recorded items
           remains correct. */
        --uxMessagesWaiting;
      } else {
        mtCOVERAGE_TEST_MARKER();
      }
    } else {
      mtCOVERAGE_TEST_MARKER();
    }
  }

  pxQueue->uxMessagesWaiting = uxMessagesWaiting + /*(UBaseType_t)*/1;
  //@enq_lemma(K, (R+1)%N, contents, abs, x);
  //@assume( (W+1)%N == (R + 1 + (K+1)) % N );
  //@assert W == (R + 1 + K) % N;
  ////@mod_plus_one(W, R + 1 + K, N);
  //@assert((W+1)%N == ((R + 1) + (K + 1)) % N);
  //@mod_plus_distr(R+1, K, N);
  //@assert(take(K+1, rotate((R+1)%N, update(W, x, contents))) == append(abs, cons(x, nil)));
  //@close queue(pxQueue, N, M, (W+1)%N, R, (K+1), append(abs, cons(x, nil)));
  return xReturn;

}
