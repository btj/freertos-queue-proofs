#include <stdlib.h>
#include <stdint.h>

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
  requires 0 <= x && 0 < n;
  ensures 0 <= (x % n) && (x % n) < n;

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

BaseType_t xQueueGenericReset(QueueHandle_t xQueue, BaseType_t xNewQueue)
  //@requires queue_init2(xQueue, ?N, ?M);
  //@ensures 0 == M ? mutex(xQueue, N, /*K*/0) : queue(xQueue, N, M, /*W*/0, /*R*/(N-1), /*K*/0, nil);
{
  Queue_t *pxQueue = xQueue;

  configASSERT(pxQueue);

  taskENTER_CRITICAL();
  {
    //@open queue_init2(xQueue, N, M);
    pxQueue->u.xQueue.pcTail =
        pxQueue->pcHead +
        (pxQueue->uxLength *
         pxQueue->uxItemSize); /*lint !e9016 Pointer arithmetic allowed on char
                                  types, especially when it assists conveying
                                  intent. */
    pxQueue->uxMessagesWaiting = (UBaseType_t)0U;
    pxQueue->pcWriteTo = pxQueue->pcHead;
    pxQueue->u.xQueue.pcReadFrom =
        pxQueue->pcHead +
        ((pxQueue->uxLength - 1U) *
         pxQueue->uxItemSize); /*lint !e9016 Pointer arithmetic allowed on char
                                  types, especially when it assists conveying
                                  intent. */
    pxQueue->cRxLock = ((int8_t)-1);
    pxQueue->cTxLock = ((int8_t)-1);

    if (xNewQueue == pdFALSE) {
      /* If there are tasks blocked waiting to read from the queue, then
                           the tasks will remain blocked as after this function
         exits the queue will still be empty.  If there are tasks blocked
         waiting to write to the queue, then one should be unblocked as after
         this function exits it will be possible to write to it. */
      if (listLIST_IS_EMPTY(&(pxQueue->xTasksWaitingToSend)) == pdFALSE) {
        if (xTaskRemoveFromEventList(&(pxQueue->xTasksWaitingToSend)) !=
            pdFALSE) {
          portYIELD_WITHIN_API();
        } else {
          mtCOVERAGE_TEST_MARKER();
        }
      } else {
        mtCOVERAGE_TEST_MARKER();
      }
    } else {
      /* Ensure the event queues start in the correct state. */
      vListInitialise(&(pxQueue->xTasksWaitingToSend));
      vListInitialise(&(pxQueue->xTasksWaitingToReceive));
    }
    /*@
    if (M == 0) { close mutex(pxQueue, N, 0); }
    else { buffer_from_chars(pxQueue->pcHead, N, M); }
    @*/
  }
  taskEXIT_CRITICAL();

  /* A value is returned for calling semantic consistency with previous
         versions. */
  return pdPASS;
}

static void prvInitialiseNewQueue(const UBaseType_t uxQueueLength,
                                  const UBaseType_t uxItemSize,
                                  int8_t *pucQueueStorage,
                                  const uint8_t ucQueueType,
                                  Queue_t *pxNewQueue)
  /*@requires
    queue_init1(pxNewQueue) &*&
    0 < uxQueueLength &*& 0 < uxItemSize &*&
    malloc_block(pucQueueStorage, uxQueueLength * uxItemSize) &*&
    chars(pucQueueStorage, uxQueueLength * uxItemSize,_);
  @*/
  //@ensures queue(pxNewQueue, /*N*/uxQueueLength, /*M*/uxItemSize, /*W*/0, /*R*/(uxQueueLength-1), /*K*/0, /*abs*/nil);
{
  //(void)ucQueueType;
  //@open queue_init1(pxNewQueue);
  if (uxItemSize == (UBaseType_t)0) {
    /* No RAM was allocated for the queue storage area, but PC head cannot
                  be set to NULL because NULL is used as a key to say the queue
       is used as a mutex.  Therefore just set pcHead to point to the queue as a
       benign value that is known to be within the memory map. */
    pxNewQueue->pcHead = (int8_t *)pxNewQueue;
  } else {
    /* Set the head to the start of the queue storage area. */
    pxNewQueue->pcHead = (int8_t *)pucQueueStorage;
  }

  /* Initialise the queue members as described where the queue type is
         defined. */
  pxNewQueue->uxLength = uxQueueLength;
  pxNewQueue->uxItemSize = uxItemSize;
  //@close queue_init2(pxNewQueue, uxQueueLength, uxItemSize);
  xQueueGenericReset(pxNewQueue, pdTRUE);
  traceQUEUE_CREATE(pxNewQueue);
}

QueueHandle_t xQueueGenericCreate(const UBaseType_t uxQueueLength,
                                  const UBaseType_t uxItemSize,
                                  const uint8_t ucQueueType)
  //@requires 0 < uxItemSize;
  /*@ensures
    result == NULL
      ? true
      : queue(result, uxQueueLength, uxItemSize, 0, (uxQueueLength-1), 0, nil);
  @*/
{
  Queue_t *pxNewQueue;
  size_t xQueueSizeInBytes;
  int8_t *pucQueueStorage;

  configASSERT(uxQueueLength > (UBaseType_t)0);

  xQueueSizeInBytes = (size_t)(
      uxQueueLength * uxItemSize);
  pxNewQueue = (Queue_t *)pvPortMalloc(sizeof(Queue_t));

  if (pxNewQueue != NULL) {
    pucQueueStorage = (int8_t *)pvPortMalloc(xQueueSizeInBytes);
    if (pucQueueStorage == NULL) {
        pvPortFree(pxNewQueue);
        pxNewQueue = NULL;
    } else {
        //@close queue_init1(pxNewQueue);
        prvInitialiseNewQueue(uxQueueLength, uxItemSize, pucQueueStorage, ucQueueType, pxNewQueue);
    }
  } else {
    traceQUEUE_CREATE_FAILED(ucQueueType);
    mtCOVERAGE_TEST_MARKER();
  }

  return pxNewQueue;
}
