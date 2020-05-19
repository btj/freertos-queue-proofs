#define VERIFAST 1

#define PRIVILEGED_FUNCTION
#include <stdint.h>
#include <stdlib.h>

typedef size_t TickType_t;
typedef size_t UBaseType_t;
typedef ssize_t BaseType_t;

// Stubbed-out types
struct list_t {
  int x;
};

typedef struct list_t List_t;

typedef int TaskHandle_t;

#if 1
/*
 * FreeRTOS Kernel V10.3.1
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * http://www.FreeRTOS.org
 * http://aws.amazon.com/freertos
 *
 * 1 tab == 4 spaces!
 */

/* Defining MPU_WRAPPERS_INCLUDED_FROM_API_FILE prevents task.h from redefining
all the API functions to use the MPU wrappers.  That should only be done when
task.h is included from an application file. */

/* Lint e9021, e961 and e750 are suppressed as a MISRA exception justified
because the MPU ports require MPU_WRAPPERS_INCLUDED_FROM_API_FILE to be defined
for the header files above, but not in this file, in order to generate the
correct privileged Vs unprivileged linkage and placement. */

/* Constants used with the cRxLock and cTxLock structure members. */

/* When the Queue_t structure is used to represent a base queue its pcHead and
pcTail members are used as pointers into the queue storage area.  When the
Queue_t structure is used to represent a mutex pcHead and pcTail pointers are
not necessary, and the pcHead pointer is set to NULL to indicate that the
structure instead holds a pointer to the mutex holder (if any).  Map alternative
names to the pcHead and structure member to ensure the readability of the code
is maintained.  The QueuePointers_t and SemaphoreData_t types are used to form
a union as their usage is mutually exclusive dependent on what the queue is
being used for. */

typedef struct QueuePointers {
  int8_t *pcTail; /*< Points to the byte at the end of the queue storage area.
                     Once more byte is allocated than necessary to store the
                     queue items, this is used as a marker. */
  int8_t *pcReadFrom; /*< Points to the last place that a queued item was read
                         from when the structure is used as a queue. */
} QueuePointers_t;

typedef struct SemaphoreData {
  TaskHandle_t xMutexHolder; /*< The handle of the task that holds the mutex. */
  UBaseType_t
      uxRecursiveCallCount; /*< Maintains a count of the number of times a
                               recursive mutex has been recursively 'taken' when
                               the structure is used as a mutex. */
} SemaphoreData_t;

/* Semaphores do not actually store or copy data, so have an item size of
zero. */
/*
 * Definition of the queue used by the scheduler.
 * Items are queued by copy, not reference.  See the following link for the
 * rationale: https://www.freertos.org/Embedded-RTOS-Queues.html
 */
#ifdef VERIFAST
struct u_t {
    QueuePointers_t xQueue; /*< Data required exclusively when this structure is
                               used as a queue. */
    SemaphoreData_t xSemaphore; /*< Data required exclusively when this
                                   structure is used as a semaphore. */
};
#endif
 
typedef struct QueueDefinition /* The old naming convention is used to prevent
                                  breaking kernel aware debuggers. */
{
  int8_t *pcHead;    /*< Points to the beginning of the queue storage area. */
  int8_t *pcWriteTo; /*< Points to the free next place in the storage area. */

#ifdef VERIFAST
  struct u_t u;
#else
  union {
    QueuePointers_t xQueue; /*< Data required exclusively when this structure is
                               used as a queue. */
    SemaphoreData_t xSemaphore; /*< Data required exclusively when this
                                   structure is used as a semaphore. */
  } u;
#endif

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

/* The old xQUEUE name is maintained above then typedefed to the new Queue_t
name below to enable the use of older kernel aware debuggers. */
typedef xQUEUE Queue_t;

typedef Queue_t *QueueHandle_t;

/*-----------------------------------------------------------*/

/*
 * The queue registry is just a means for kernel aware debuggers to locate
 * queue structures.  It has no other purpose so is an optional component.
 */
/*
 * Unlocks a queue locked by a call to prvLockQueue.  Locking a queue does not
 * prevent an ISR from adding or removing items to the queue, but does prevent
 * an ISR from removing tasks from the queue event lists.  If an ISR finds a
 * queue is locked it will instead increment the appropriate queue lock count
 * to indicate that a task may require unblocking.  When the queue in unlocked
 * these lock counts are inspected, and the appropriate action taken.
 */
static void prvUnlockQueue(Queue_t *const pxQueue) PRIVILEGED_FUNCTION;

/*
 * Uses a critical section to determine if there is any data in a queue.
 *
 * @return pdTRUE if the queue contains no items, otherwise pdFALSE.
 */
static BaseType_t prvIsQueueEmpty(const Queue_t *pxQueue) PRIVILEGED_FUNCTION;

/*
 * Uses a critical section to determine if there is any space in a queue.
 *
 * @return pdTRUE if there is no space, otherwise pdFALSE;
 */
static BaseType_t prvIsQueueFull(const Queue_t *pxQueue) PRIVILEGED_FUNCTION;

/*
 * Copies an item into the queue, either at the front of the queue or the
 * back of the queue.
 */
static BaseType_t
prvCopyDataToQueue(Queue_t *const pxQueue, const void *pvItemToQueue,
                   const BaseType_t xPosition) PRIVILEGED_FUNCTION;

/*
 * Copies an item out of a queue.
 */
static void prvCopyDataFromQueue(Queue_t *const pxQueue,
                                 void *const pvBuffer) PRIVILEGED_FUNCTION;
/*
 * Called after a Queue_t structure has been allocated either statically or
 * dynamically to fill in the structure's members.
 */
static void prvInitialiseNewQueue(const UBaseType_t uxQueueLength,
                                  const UBaseType_t uxItemSize,
                                  uint8_t *pucQueueStorage,
                                  const uint8_t ucQueueType,
                                  Queue_t *pxNewQueue) PRIVILEGED_FUNCTION;

/*
 * Mutexes are a special type of queue.  When a mutex is created, first the
 * queue is created, then prvInitialiseMutex() is called to configure the queue
 * as a mutex.
 */

static void prvInitialiseMutex(Queue_t *pxNewQueue) PRIVILEGED_FUNCTION;

/*
 * If a task waiting for a mutex causes the mutex holder to inherit a
 * priority, but the waiting task times out, then the holder should
 * disinherit the priority - but only down to the highest priority of any
 * other tasks that are waiting for the same mutex.  This function returns
 * that priority.
 */
static UBaseType_t prvGetDisinheritPriorityAfterTimeout(
    const Queue_t *const pxQueue) PRIVILEGED_FUNCTION;

/*-----------------------------------------------------------*/

/*
 * Macro to mark a queue as locked.  Locking a queue prevents an ISR from
 * accessing the queue event lists.
 */
/*-----------------------------------------------------------*/

BaseType_t xQueueGenericReset(QueueHandle_t xQueue, BaseType_t xNewQueue) {
#ifdef VERIFAST
  Queue_t *pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  configASSERT(pxQueue);

  taskENTER_CRITICAL();
  {
    pxQueue->u.xQueue.pcTail =
        pxQueue->pcHead +
        (pxQueue->uxLength *
         pxQueue->uxItemSize); /*lint !e9016 Pointer arithmetic allowed on char
                                  types, especially when it assists conveying
                                  intent. */
#ifdef VERIFAST
    pxQueue->uxMessagesWaiting = 0;
#else
    pxQueue->uxMessagesWaiting = (UBaseType_t)0U;
#endif
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
  }
  taskEXIT_CRITICAL();

  /* A value is returned for calling semantic consistency with previous
         versions. */
  return pdPASS;
}
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/

QueueHandle_t xQueueGenericCreate(const UBaseType_t uxQueueLength,
                                  const UBaseType_t uxItemSize,
                                  const uint8_t ucQueueType) {
  Queue_t *pxNewQueue;
  size_t xQueueSizeInBytes;
  uint8_t *pucQueueStorage;

#ifndef VERIFAST
  configASSERT(uxQueueLength > (UBaseType_t)0);
#endif

  /* Allocate enough space to hold the maximum number of items that
                can be in the queue at any time.  It is valid for uxItemSize to
     be zero in the case the queue is used as a semaphore. */
  xQueueSizeInBytes = (size_t)(
      uxQueueLength * uxItemSize); /*lint !e961 MISRA exception as the casts are
                                      only redundant for some ports. */

  /* Allocate the queue and storage area.  Justification for MISRA
                deviation as follows:  pvPortMalloc() always ensures returned
     memory blocks are aligned per the requirements of the MCU stack.  In this
     case pvPortMalloc() must return a pointer that is guaranteed to meet the
                alignment requirements of the Queue_t structure - which in this
     case is an int8_t *.  Therefore, whenever the stack alignment requirements
                are greater than or equal to the pointer to char requirements
     the cast is safe.  In other cases alignment requirements are not strict
     (one or two bytes). */
  pxNewQueue = (Queue_t *)pvPortMalloc(
      sizeof(Queue_t) +
      xQueueSizeInBytes); /*lint !e9087 !e9079 see comment above. */

  if (pxNewQueue != NULL) {
    /* Jump past the queue structure to find the location of the queue
                         storage area. */
#ifdef VERIFAST
    pucQueueStorage = pxNewQueue;
#else
    pucQueueStorage = (uint8_t *)pxNewQueue;
#endif
    pucQueueStorage +=
        sizeof(Queue_t); /*lint !e9016 Pointer arithmetic allowed on char types,
                            especially when it assists conveying intent. */
    prvInitialiseNewQueue(uxQueueLength, uxItemSize, pucQueueStorage,
                          ucQueueType, pxNewQueue);
  } else {
    traceQUEUE_CREATE_FAILED(ucQueueType);
    mtCOVERAGE_TEST_MARKER();
  }

  return pxNewQueue;
}

/*-----------------------------------------------------------*/

static void prvInitialiseNewQueue(const UBaseType_t uxQueueLength,
                                  const UBaseType_t uxItemSize,
                                  uint8_t *pucQueueStorage,
                                  const uint8_t ucQueueType,
                                  Queue_t *pxNewQueue) {
  /* Remove compiler warnings about unused parameters should
         configUSE_TRACE_FACILITY not be set to 1. */
  (void)ucQueueType;

  if (uxItemSize == /*(UBaseType_t)*/0) {
    /* No RAM was allocated for the queue storage area, but PC head cannot
                  be set to NULL because NULL is used as a key to say the queue
       is used as a mutex.  Therefore just set pcHead to point to the queue as a
       benign value that is known to be within the memory map. */
    pxNewQueue->pcHead = /*(int8_t *)*/pxNewQueue;
  } else {
    /* Set the head to the start of the queue storage area. */
    pxNewQueue->pcHead = /*(int8_t *)*/pucQueueStorage;
  }

  /* Initialise the queue members as described where the queue type is
         defined. */
  pxNewQueue->uxLength = uxQueueLength;
  pxNewQueue->uxItemSize = uxItemSize;
  (void)xQueueGenericReset(pxNewQueue, pdTRUE);
  traceQUEUE_CREATE(pxNewQueue);
}
/*-----------------------------------------------------------*/

static void prvInitialiseMutex(Queue_t *pxNewQueue) {
  if (pxNewQueue != NULL) {
    /* The queue create function will set all the queue structure members
                         correctly for a generic queue, but this function is
       creating a mutex.  Overwrite those members that need to be set
       differently - in particular the information required for priority
       inheritance. */
    pxNewQueue->u.xSemaphore.xMutexHolder = NULL;
    pxNewQueue->pcHead = NULL;

    /* In case this is a recursive mutex. */
    pxNewQueue->u.xSemaphore.uxRecursiveCallCount = 0;

    traceCREATE_MUTEX(pxNewQueue);

    /* Start with the semaphore in the expected state. */
    (void)xQueueGenericSend(pxNewQueue, NULL, /*(TickType_t)*/0U,
                            queueSEND_TO_BACK);
  } else {
    traceCREATE_MUTEX_FAILED();
  }
}

/*-----------------------------------------------------------*/

QueueHandle_t xQueueCreateMutex(const uint8_t ucQueueType) {
  QueueHandle_t xNewQueue;
  const UBaseType_t uxMutexLength = /*(UBaseType_t)*/1,
                    uxMutexSize = /*(UBaseType_t)*/0;

  xNewQueue = xQueueGenericCreate(uxMutexLength, uxMutexSize, ucQueueType);
  prvInitialiseMutex((Queue_t *)xNewQueue);

  return xNewQueue;
}

/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/

BaseType_t xQueueGenericSend(QueueHandle_t xQueue,
                             const void *const pvItemToQueue,
                             TickType_t xTicksToWait,
                             const BaseType_t xCopyPosition) {
  BaseType_t xEntryTimeSet = pdFALSE, xYieldRequired;
  TimeOut_t xTimeOut;
#ifdef VERIFAST
  Queue_t * pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  configASSERT(pxQueue);
  configASSERT(
      !((pvItemToQueue == NULL) && (pxQueue->uxItemSize != /*(UBaseType_t)*/0U)));
  configASSERT(
      !((xCopyPosition == queueOVERWRITE) && (pxQueue->uxLength != 1)));

  /*lint -save -e904 This function relaxes the coding standard somewhat to
         allow return statements within the function itself.  This is done in
     the interest of execution time efficiency. */
  for (;;) {
    taskENTER_CRITICAL();
    {
      /* Is there room on the queue now?  The running task must be the
                           highest priority task wanting to access the queue. If
         the head item in the queue is to be overwritten then it does not matter
         if the queue is full. */
      if ((pxQueue->uxMessagesWaiting < pxQueue->uxLength) ||
          (xCopyPosition == queueOVERWRITE)) {
        traceQUEUE_SEND(pxQueue);
        {
          xYieldRequired =
              prvCopyDataToQueue(pxQueue, pvItemToQueue, xCopyPosition);

          /* If there was a task waiting for data to arrive on the
                                             queue then unblock it now. */
          if (listLIST_IS_EMPTY(&(pxQueue->xTasksWaitingToReceive)) ==
              pdFALSE) {
            if (xTaskRemoveFromEventList(&(pxQueue->xTasksWaitingToReceive)) !=
                pdFALSE) {
              /* The unblocked task has a priority higher than
                                                               our own so yield
                 immediately.  Yes it is ok to do this from within the critical
                 section - the kernel takes care of that. */
              portYIELD_WITHIN_API();
            } else {
              mtCOVERAGE_TEST_MARKER();
            }
          } else if (xYieldRequired != pdFALSE) {
            /* This path is a special case that will only get
                                                      executed if the task was
               holding multiple mutexes and the mutexes were given back in an
               order that is different to that in which they were taken. */
            portYIELD_WITHIN_API();
          } else {
            mtCOVERAGE_TEST_MARKER();
          }
        }

        taskEXIT_CRITICAL();
        return pdPASS;
      } else {
        if (xTicksToWait == /*(TickType_t)*/0) {
          /* The queue was full and no block time is specified (or
                                             the block time has expired) so
             leave now. */
          taskEXIT_CRITICAL();

          /* Return to the original privilege level before exiting
                                             the function. */
          traceQUEUE_SEND_FAILED(pxQueue);
          return errQUEUE_FULL;
        } else if (xEntryTimeSet == pdFALSE) {
          /* The queue was full and a block time was specified so
                                             configure the timeout structure. */
          vTaskInternalSetTimeOutState(&xTimeOut);
          xEntryTimeSet = pdTRUE;
        } else {
          /* Entry time was already set. */
          mtCOVERAGE_TEST_MARKER();
        }
      }
    }
    taskEXIT_CRITICAL();

    /* Interrupts and other tasks can send to and receive from the queue
                  now the critical section has been exited. */

    vTaskSuspendAll();
    taskENTER_CRITICAL();
    {
      if ((pxQueue)->cRxLock == ((int8_t)-1)) {
        (pxQueue)->cRxLock = (/*(int8_t)*/0);
      }
      if ((pxQueue)->cTxLock == ((int8_t)-1)) {
        (pxQueue)->cTxLock = (/*(int8_t)*/0);
      }
    }
    taskEXIT_CRITICAL();

    /* Update the timeout state to see if it has expired yet. */
    if (xTaskCheckForTimeOut(&xTimeOut, &xTicksToWait) == pdFALSE) {
      if (prvIsQueueFull(pxQueue) != pdFALSE) {
        traceBLOCKING_ON_QUEUE_SEND(pxQueue);
        vTaskPlaceOnEventList(&(pxQueue->xTasksWaitingToSend), xTicksToWait);

        /* Unlocking the queue means queue events can effect the
                                    event list.  It is possible that interrupts
           occurring now remove this task from the event list again - but as the
                                    scheduler is suspended the task will go onto
           the pending ready last instead of the actual ready list. */
        prvUnlockQueue(pxQueue);

        /* Resuming the scheduler will move tasks from the pending
                                    ready list into the ready list - so it is
           feasible that this task is already in a ready list before it yields -
           in which case the yield will not cause a context switch unless there
                                    is also a higher priority task in the
           pending ready list. */
        if (xTaskResumeAll() == pdFALSE) {
          portYIELD_WITHIN_API();
        }
      } else {
        /* Try again. */
        prvUnlockQueue(pxQueue);
        (void)xTaskResumeAll();
      }
    } else {
      /* The timeout has expired. */
      prvUnlockQueue(pxQueue);
      (void)xTaskResumeAll();

      traceQUEUE_SEND_FAILED(pxQueue);
      return errQUEUE_FULL;
    }
  } /*lint -restore */
}
/*-----------------------------------------------------------*/

BaseType_t xQueueGenericSendFromISR(QueueHandle_t xQueue,
                                    const void *const pvItemToQueue,
                                    BaseType_t *const pxHigherPriorityTaskWoken,
                                    const BaseType_t xCopyPosition) {
  BaseType_t xReturn;
  UBaseType_t uxSavedInterruptStatus;
#ifdef VERIFAST
  Queue_t * pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  configASSERT(pxQueue);
  configASSERT(
      !((pvItemToQueue == NULL) && (pxQueue->uxItemSize != /*(UBaseType_t)*/0U)));
  configASSERT(
      !((xCopyPosition == queueOVERWRITE) && (pxQueue->uxLength != 1)));

  /* RTOS ports that support interrupt nesting have the concept of a maximum
         system call (or maximum API call) interrupt priority.  Interrupts that
     are above the maximum system call priority are kept permanently enabled,
     even when the RTOS kernel is in a critical section, but cannot make any
     calls to FreeRTOS API functions.  If configASSERT() is defined in
     FreeRTOSConfig.h then portASSERT_IF_INTERRUPT_PRIORITY_INVALID() will
     result in an assertion failure if a FreeRTOS API function is called from an
     interrupt that has been assigned a priority above the configured maximum
     system call priority. Only FreeRTOS functions that end in FromISR can be
     called from interrupts that have been assigned a priority at or (logically)
     below the maximum
         system call	interrupt priority.  FreeRTOS maintains a separate
     interrupt safe API to ensure interrupt entry is as fast and as simple as
     possible. More information (albeit Cortex-M specific) is provided on the
     following link: http://www.freertos.org/RTOS-Cortex-M3-M4.html */
  portASSERT_IF_INTERRUPT_PRIORITY_INVALID();

  /* Similar to xQueueGenericSend, except without blocking if there is no room
         in the queue.  Also don't directly wake a task that was blocked on a
     queue read, instead return a flag to say whether a context switch is
     required or not (i.e. has a task with a higher priority than us been woken
     by this post). */
  uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR();
  {
    if ((pxQueue->uxMessagesWaiting < pxQueue->uxLength) ||
        (xCopyPosition == queueOVERWRITE)) {
      const int8_t cTxLock = pxQueue->cTxLock;
      const UBaseType_t uxPreviousMessagesWaiting = pxQueue->uxMessagesWaiting;

      traceQUEUE_SEND_FROM_ISR(pxQueue);

      /* Semaphores use xQueueGiveFromISR(), so pxQueue will not be a
                           semaphore or mutex.  That means prvCopyDataToQueue()
         cannot result in a task disinheriting a priority and
         prvCopyDataToQueue() can be called here even though the disinherit
         function does not check if
                           the scheduler is suspended before accessing the ready
         lists. */
      (void)prvCopyDataToQueue(pxQueue, pvItemToQueue, xCopyPosition);

      /* The event list is not altered if the queue is locked.  This will
                           be done when the queue is unlocked later. */
      if (cTxLock == ((int8_t)-1/*queueUNLOCKED*/)) {
        {
          if (listLIST_IS_EMPTY(&(pxQueue->xTasksWaitingToReceive)) ==
              pdFALSE) {
            if (xTaskRemoveFromEventList(&(pxQueue->xTasksWaitingToReceive)) !=
                pdFALSE) {
              /* The task waiting has a higher priority so record that a
                                                               context	switch is
                 required. */
              if (pxHigherPriorityTaskWoken != NULL) {
                *pxHigherPriorityTaskWoken = pdTRUE;
              } else {
                mtCOVERAGE_TEST_MARKER();
              }
            } else {
              mtCOVERAGE_TEST_MARKER();
            }
          } else {
            mtCOVERAGE_TEST_MARKER();
          }

          /* Not used in this path. */
          (void)uxPreviousMessagesWaiting;
        }

      } else if (cTxLock == 127) {
        return error;
      } else { /*queue is locked */
        /* Increment the lock count so the task that unlocks the queue
                                    knows that data was posted while it was
           locked. */
        pxQueue->cTxLock = (int8_t)(cTxLock + 1);
      }

      xReturn = pdPASS;
    } else {
      traceQUEUE_SEND_FROM_ISR_FAILED(pxQueue);
      xReturn = errQUEUE_FULL;
    }
  }
  portCLEAR_INTERRUPT_MASK_FROM_ISR(uxSavedInterruptStatus);

  return xReturn;
}
/*-----------------------------------------------------------*/

BaseType_t xQueueGiveFromISR(QueueHandle_t xQueue,
                             BaseType_t *const pxHigherPriorityTaskWoken) {
  BaseType_t xReturn;
  UBaseType_t uxSavedInterruptStatus;
#ifdef VERIFAST
  Queue_t * pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  /* Similar to xQueueGenericSendFromISR() but used with semaphores where the
         item size is 0.  Don't directly wake a task that was blocked on a queue
         read, instead return a flag to say whether a context switch is required
     or not (i.e. has a task with a higher priority than us been woken by this
         post). */

  configASSERT(pxQueue);

  /* xQueueGenericSendFromISR() should be used instead of xQueueGiveFromISR()
         if the item size is not 0. */
  configASSERT(pxQueue->uxItemSize == 0);

  /* Normally a mutex would not be given from an interrupt, especially if
         there is a mutex holder, as priority inheritance makes no sense for an
         interrupts, only tasks. */
  configASSERT(!((pxQueue->pcHead == NULL) &&
                 (pxQueue->u.xSemaphore.xMutexHolder != NULL)));

  /* RTOS ports that support interrupt nesting have the concept of a maximum
         system call (or maximum API call) interrupt priority.  Interrupts that
     are above the maximum system call priority are kept permanently enabled,
     even when the RTOS kernel is in a critical section, but cannot make any
     calls to FreeRTOS API functions.  If configASSERT() is defined in
     FreeRTOSConfig.h then portASSERT_IF_INTERRUPT_PRIORITY_INVALID() will
     result in an assertion failure if a FreeRTOS API function is called from an
     interrupt that has been assigned a priority above the configured maximum
     system call priority. Only FreeRTOS functions that end in FromISR can be
     called from interrupts that have been assigned a priority at or (logically)
     below the maximum
         system call	interrupt priority.  FreeRTOS maintains a separate
     interrupt safe API to ensure interrupt entry is as fast and as simple as
     possible. More information (albeit Cortex-M specific) is provided on the
     following link: http://www.freertos.org/RTOS-Cortex-M3-M4.html */
  portASSERT_IF_INTERRUPT_PRIORITY_INVALID();

  uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR();
  {
    const UBaseType_t uxMessagesWaiting = pxQueue->uxMessagesWaiting;

    /* When the queue is used to implement a semaphore no data is ever
                  moved through the queue but it is still valid to see if the
       queue 'has space'. */
    if (uxMessagesWaiting < pxQueue->uxLength) {
      const int8_t cTxLock = pxQueue->cTxLock;

      traceQUEUE_SEND_FROM_ISR(pxQueue);

      /* A task can only have an inherited priority if it is a mutex
                           holder - and if there is a mutex holder then the
         mutex cannot be given from an ISR.  As this is the ISR version of the
         function it can be assumed there is no mutex holder and no need to
         determine if priority disinheritance is needed.  Simply increase the
         count of messages (semaphores) available. */
      pxQueue->uxMessagesWaiting = uxMessagesWaiting + 1;

      /* The event list is not altered if the queue is locked.  This will
                           be done when the queue is unlocked later. */
      if (cTxLock == ((int8_t)-1)) {
        {
          if (listLIST_IS_EMPTY(&(pxQueue->xTasksWaitingToReceive)) ==
              pdFALSE) {
            if (xTaskRemoveFromEventList(&(pxQueue->xTasksWaitingToReceive)) !=
                pdFALSE) {
              /* The task waiting has a higher priority so record that a
                                                               context	switch is
                 required. */
              if (pxHigherPriorityTaskWoken != NULL) {
                *pxHigherPriorityTaskWoken = pdTRUE;
              } else {
                mtCOVERAGE_TEST_MARKER();
              }
            } else {
              mtCOVERAGE_TEST_MARKER();
            }
          } else {
            mtCOVERAGE_TEST_MARKER();
          }
        }

      } else {
        /* Increment the lock count so the task that unlocks the queue
                                    knows that data was posted while it was
           locked. */
        pxQueue->cTxLock = (int8_t)(cTxLock + 1);
      }

      xReturn = pdPASS;
    } else {
      traceQUEUE_SEND_FROM_ISR_FAILED(pxQueue);
      xReturn = errQUEUE_FULL;
    }
  }
  portCLEAR_INTERRUPT_MASK_FROM_ISR(uxSavedInterruptStatus);

  return xReturn;
}
/*-----------------------------------------------------------*/

BaseType_t xQueueReceive(QueueHandle_t xQueue, void *const pvBuffer,
                         TickType_t xTicksToWait) {
  BaseType_t xEntryTimeSet = pdFALSE;
  TimeOut_t xTimeOut;
#ifdef VERIFAST
  Queue_t * pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  /* Check the pointer is not NULL. */
  configASSERT((pxQueue));

  /* The buffer into which data is received can only be NULL if the data size
         is zero (so no data is copied into the buffer). */
  configASSERT(
      !(((pvBuffer) == NULL) && ((pxQueue)->uxItemSize != /*(UBaseType_t)*/0U)));

  /* Cannot block if the scheduler is suspended. */

  /*lint -save -e904  This function relaxes the coding standard somewhat to
         allow return statements within the function itself.  This is done in
     the interest of execution time efficiency. */
  for (;;) {
    taskENTER_CRITICAL();
    {
      const UBaseType_t uxMessagesWaiting = pxQueue->uxMessagesWaiting;

      /* Is there data in the queue now?  To be running the calling task
                           must be the highest priority task wanting to access
         the queue. */
      if (uxMessagesWaiting > /*(UBaseType_t)*/0) {
        /* Data available, remove one item. */
        prvCopyDataFromQueue(pxQueue, pvBuffer);
        traceQUEUE_RECEIVE(pxQueue);
        pxQueue->uxMessagesWaiting = uxMessagesWaiting - /*(UBaseType_t)*/1;

        /* There is now space in the queue, were any tasks waiting to
                                    post to the queue?  If so, unblock the
           highest priority waiting task. */
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

        taskEXIT_CRITICAL();
        return pdPASS;
      } else {
        if (xTicksToWait == /*(TickType_t)*/0) {
          /* The queue was empty and no block time is specified (or
                                             the block time has expired) so
             leave now. */
          taskEXIT_CRITICAL();
          traceQUEUE_RECEIVE_FAILED(pxQueue);
          return errQUEUE_EMPTY;
        } else if (xEntryTimeSet == pdFALSE) {
          /* The queue was empty and a block time was specified so
                                             configure the timeout structure. */
          vTaskInternalSetTimeOutState(&xTimeOut);
          xEntryTimeSet = pdTRUE;
        } else {
          /* Entry time was already set. */
          mtCOVERAGE_TEST_MARKER();
        }
      }
    }
    taskEXIT_CRITICAL();

    /* Interrupts and other tasks can send to and receive from the queue
                  now the critical section has been exited. */

    vTaskSuspendAll();
    taskENTER_CRITICAL();
    {//0 = unlocked
     //1 = locked
     //2
      if ((pxQueue)->cRxLock == ((int8_t)queueUNLOCKED)) {
        (pxQueue)->cRxLock = ((int8_t)queueLOCKED);
      }
      if ((pxQueue)->cTxLock == ((int8_t)queueUNLOCKED)) {
        (pxQueue)->cTxLock = ((int8_t)queueLOCKED);
      }
    }
    taskEXIT_CRITICAL();

    /* Update the timeout state to see if it has expired yet. */
    if (xTaskCheckForTimeOut(&xTimeOut, &xTicksToWait) == pdFALSE) {
      /* The timeout has not expired.  If the queue is still empty place
                           the task on the list of tasks waiting to receive from
         the queue. */
      if (prvIsQueueEmpty(pxQueue) != pdFALSE) {
        traceBLOCKING_ON_QUEUE_RECEIVE(pxQueue);
        vTaskPlaceOnEventList(&(pxQueue->xTasksWaitingToReceive), xTicksToWait);
        prvUnlockQueue(pxQueue);
        if (xTaskResumeAll() == pdFALSE) {
          portYIELD_WITHIN_API();
        } else {
          mtCOVERAGE_TEST_MARKER();
        }
      } else {
        /* The queue contains data again.  Loop back to try and read the
                                    data. */
        prvUnlockQueue(pxQueue);
        (void)xTaskResumeAll();
      }
    } else {
      /* Timed out.  If there is no data in the queue exit, otherwise loop
                           back and attempt to read the data. */
      prvUnlockQueue(pxQueue);
      (void)xTaskResumeAll();

      if (prvIsQueueEmpty(pxQueue) != pdFALSE) {
        traceQUEUE_RECEIVE_FAILED(pxQueue);
        return errQUEUE_EMPTY;
      } else {
        mtCOVERAGE_TEST_MARKER();
      }
    }
  } /*lint -restore */
}
/*-----------------------------------------------------------*/

BaseType_t xQueueSemaphoreTake(QueueHandle_t xQueue, TickType_t xTicksToWait) {
  BaseType_t xEntryTimeSet = pdFALSE;
  TimeOut_t xTimeOut;
#ifdef VERIFAST
  Queue_t * pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  BaseType_t xInheritanceOccurred = pdFALSE;

  /* Check the queue pointer is not NULL. */
  configASSERT((pxQueue));

  /* Check this really is a semaphore, in which case the item size will be
         0. */
  configASSERT(pxQueue->uxItemSize == 0);

  /* Cannot block if the scheduler is suspended. */

  /*lint -save -e904 This function relaxes the coding standard somewhat to allow
     return statements within the function itself.  This is done in the interest
         of execution time efficiency. */
  for (;;) {
    taskENTER_CRITICAL();
    {
      /* Semaphores are queues with an item size of 0, and where the
                           number of messages in the queue is the semaphore's
         count value. */
      const UBaseType_t uxSemaphoreCount = pxQueue->uxMessagesWaiting;

      /* Is there data in the queue now?  To be running the calling task
                           must be the highest priority task wanting to access
         the queue. */
      if (uxSemaphoreCount > /*(UBaseType_t)*/0) {
        traceQUEUE_RECEIVE(pxQueue);

        /* Semaphores are queues with a data size of zero and where the
                                    messages waiting is the semaphore's count.
           Reduce the count. */
        pxQueue->uxMessagesWaiting = uxSemaphoreCount - /*(UBaseType_t)*/1;

        {
          if (pxQueue->pcHead == NULL) {
            /* Record the information required to implement
                                                      priority inheritance
               should it become necessary. */
            pxQueue->u.xSemaphore.xMutexHolder =
                pvTaskIncrementMutexHeldCount();
          } else {
            mtCOVERAGE_TEST_MARKER();
          }
        }

        /* Check to see if other tasks are blocked waiting to give the
                                    semaphore, and if so, unblock the highest
           priority such task. */
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

        taskEXIT_CRITICAL();
        return pdPASS;
      } else {
        if (xTicksToWait == /*(TickType_t)*/0) {
          /* For inheritance to have occurred there must have been an
                                             initial timeout, and an adjusted
             timeout cannot become 0, as if it were 0 the function would have
             exited. */

          { configASSERT(xInheritanceOccurred == pdFALSE); }

          /* The semaphore count was 0 and no block time is specified
                                             (or the block time has expired) so
             exit now. */
          taskEXIT_CRITICAL();
          traceQUEUE_RECEIVE_FAILED(pxQueue);
          return errQUEUE_EMPTY;
        } else if (xEntryTimeSet == pdFALSE) {
          /* The semaphore count was 0 and a block time was specified
                                             so configure the timeout structure
             ready to block. */
          vTaskInternalSetTimeOutState(&xTimeOut);
          xEntryTimeSet = pdTRUE;
        } else {
          /* Entry time was already set. */
          mtCOVERAGE_TEST_MARKER();
        }
      }
    }
    taskEXIT_CRITICAL();

    /* Interrupts and other tasks can give to and take from the semaphore
                  now the critical section has been exited. */

    vTaskSuspendAll();
    taskENTER_CRITICAL();
    {
      if ((pxQueue)->cRxLock == ((int8_t)-1)) {
        (pxQueue)->cRxLock = (/*(int8_t)*/0);
      }
      if ((pxQueue)->cTxLock == ((int8_t)-1)) {
        (pxQueue)->cTxLock = (/*(int8_t)*/0);
      }
    }
    taskEXIT_CRITICAL();

    /* Update the timeout state to see if it has expired yet. */
    if (xTaskCheckForTimeOut(&xTimeOut, &xTicksToWait) == pdFALSE) {
      /* A block time is specified and not expired.  If the semaphore
                           count is 0 then enter the Blocked state to wait for a
         semaphore to become available.  As semaphores are implemented with
         queues the
                           queue being empty is equivalent to the semaphore
         count being 0. */
      if (prvIsQueueEmpty(pxQueue) != pdFALSE) {
        traceBLOCKING_ON_QUEUE_RECEIVE(pxQueue);

        {
          if (pxQueue->pcHead == NULL) {
            taskENTER_CRITICAL();
            {
              xInheritanceOccurred =
                  xTaskPriorityInherit(pxQueue->u.xSemaphore.xMutexHolder);
            }
            taskEXIT_CRITICAL();
          } else {
            mtCOVERAGE_TEST_MARKER();
          }
        }

        vTaskPlaceOnEventList(&(pxQueue->xTasksWaitingToReceive), xTicksToWait);
        prvUnlockQueue(pxQueue);
        if (xTaskResumeAll() == pdFALSE) {
          portYIELD_WITHIN_API();
        } else {
          mtCOVERAGE_TEST_MARKER();
        }
      } else {
        /* There was no timeout and the semaphore count was not 0, so
                                    attempt to take the semaphore again. */
        prvUnlockQueue(pxQueue);
        (void)xTaskResumeAll();
      }
    } else {
      /* Timed out. */
      prvUnlockQueue(pxQueue);
      (void)xTaskResumeAll();

      /* If the semaphore count is 0 exit now as the timeout has
                           expired.  Otherwise return to attempt to take the
         semaphore that is known to be available.  As semaphores are implemented
         by queues the queue being empty is equivalent to the semaphore count
         being 0. */
      if (prvIsQueueEmpty(pxQueue) != pdFALSE) {

        {
          /* xInheritanceOccurred could only have be set if
                                             pxQueue->uxQueueType ==
             queueQUEUE_IS_MUTEX so no need to test the mutex type again to
             check it is actually a mutex. */
          if (xInheritanceOccurred != pdFALSE) {
            taskENTER_CRITICAL();
            {
              UBaseType_t uxHighestWaitingPriority;

              /* This task blocking on the mutex caused another
                                                               task to inherit
                 this task's priority.  Now this task has timed out the priority
                 should be disinherited again, but only as low as the next
                 highest priority task that is waiting for the same mutex. */
              uxHighestWaitingPriority =
                  prvGetDisinheritPriorityAfterTimeout(pxQueue);
              vTaskPriorityDisinheritAfterTimeout(
                  pxQueue->u.xSemaphore.xMutexHolder, uxHighestWaitingPriority);
            }
            taskEXIT_CRITICAL();
          }
        }

        traceQUEUE_RECEIVE_FAILED(pxQueue);
        return errQUEUE_EMPTY;
      } else {
        mtCOVERAGE_TEST_MARKER();
      }
    }
  } /*lint -restore */
}
/*-----------------------------------------------------------*/

BaseType_t xQueuePeek(QueueHandle_t xQueue, void *const pvBuffer,
                      TickType_t xTicksToWait) {
  BaseType_t xEntryTimeSet = pdFALSE;
  TimeOut_t xTimeOut;
  int8_t *pcOriginalReadPosition;
#ifdef VERIFAST
  Queue_t * pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  /* Check the pointer is not NULL. */
  configASSERT((pxQueue));

  /* The buffer into which data is received can only be NULL if the data size
         is zero (so no data is copied into the buffer. */
  configASSERT(
      !(((pvBuffer) == NULL) && ((pxQueue)->uxItemSize != /*(UBaseType_t)*/0U)));

  /* Cannot block if the scheduler is suspended. */

  /*lint -save -e904  This function relaxes the coding standard somewhat to
         allow return statements within the function itself.  This is done in
     the interest of execution time efficiency. */
  for (;;) {
    taskENTER_CRITICAL();
    {
      const UBaseType_t uxMessagesWaiting = pxQueue->uxMessagesWaiting;

      /* Is there data in the queue now?  To be running the calling task
                           must be the highest priority task wanting to access
         the queue. */
      if (uxMessagesWaiting > /*(UBaseType_t)*/0) {
        /* Remember the read position so it can be reset after the data
                                    is read from the queue as this function is
           only peeking the data, not removing it. */
        pcOriginalReadPosition = pxQueue->u.xQueue.pcReadFrom;

        prvCopyDataFromQueue(pxQueue, pvBuffer);
        traceQUEUE_PEEK(pxQueue);

        /* The data is not being removed, so reset the read pointer. */
        pxQueue->u.xQueue.pcReadFrom = pcOriginalReadPosition;

        /* The data is being left in the queue, so see if there are
                                    any other tasks waiting for the data. */
        if (listLIST_IS_EMPTY(&(pxQueue->xTasksWaitingToReceive)) == pdFALSE) {
          if (xTaskRemoveFromEventList(&(pxQueue->xTasksWaitingToReceive)) !=
              pdFALSE) {
            /* The task waiting has a higher priority than this task. */
            portYIELD_WITHIN_API();
          } else {
            mtCOVERAGE_TEST_MARKER();
          }
        } else {
          mtCOVERAGE_TEST_MARKER();
        }

        taskEXIT_CRITICAL();
        return pdPASS;
      } else {
        if (xTicksToWait == /*(TickType_t)*/0) {
          /* The queue was empty and no block time is specified (or
                                             the block time has expired) so
             leave now. */
          taskEXIT_CRITICAL();
          traceQUEUE_PEEK_FAILED(pxQueue);
          return errQUEUE_EMPTY;
        } else if (xEntryTimeSet == pdFALSE) {
          /* The queue was empty and a block time was specified so
                                             configure the timeout structure
             ready to enter the blocked state. */
          vTaskInternalSetTimeOutState(&xTimeOut);
          xEntryTimeSet = pdTRUE;
        } else {
          /* Entry time was already set. */
          mtCOVERAGE_TEST_MARKER();
        }
      }
    }
    taskEXIT_CRITICAL();

    /* Interrupts and other tasks can send to and receive from the queue
                  now the critical section has been exited. */

    vTaskSuspendAll();
    taskENTER_CRITICAL();
    {
      if ((pxQueue)->cRxLock == ((int8_t)-1)) {
        (pxQueue)->cRxLock = (/*(int8_t)*/0);
      }
      if ((pxQueue)->cTxLock == ((int8_t)-1)) {
        (pxQueue)->cTxLock = (/*(int8_t)*/0);
      }
    }
    taskEXIT_CRITICAL();

    /* Update the timeout state to see if it has expired yet. */
    if (xTaskCheckForTimeOut(&xTimeOut, &xTicksToWait) == pdFALSE) {
      /* Timeout has not expired yet, check to see if there is data in the
                           queue now, and if not enter the Blocked state to wait
         for data. */
      if (prvIsQueueEmpty(pxQueue) != pdFALSE) {
        traceBLOCKING_ON_QUEUE_PEEK(pxQueue);
        vTaskPlaceOnEventList(&(pxQueue->xTasksWaitingToReceive), xTicksToWait);
        prvUnlockQueue(pxQueue);
        if (xTaskResumeAll() == pdFALSE) {
          portYIELD_WITHIN_API();
        } else {
          mtCOVERAGE_TEST_MARKER();
        }
      } else {
        /* There is data in the queue now, so don't enter the blocked
                                    state, instead return to try and obtain the
           data. */
        prvUnlockQueue(pxQueue);
        (void)xTaskResumeAll();
      }
    } else {
      /* The timeout has expired.  If there is still no data in the queue
                           exit, otherwise go back and try to read the data
         again. */
      prvUnlockQueue(pxQueue);
      (void)xTaskResumeAll();

      if (prvIsQueueEmpty(pxQueue) != pdFALSE) {
        traceQUEUE_PEEK_FAILED(pxQueue);
        return errQUEUE_EMPTY;
      } else {
        mtCOVERAGE_TEST_MARKER();
      }
    }
  } /*lint -restore */
}
/*-----------------------------------------------------------*/

BaseType_t xQueueReceiveFromISR(QueueHandle_t xQueue, void *const pvBuffer,
                                BaseType_t *const pxHigherPriorityTaskWoken) {
  BaseType_t xReturn;
  UBaseType_t uxSavedInterruptStatus;
#ifdef VERIFAST
  Queue_t * pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  configASSERT(pxQueue);
  configASSERT(
      !((pvBuffer == NULL) && (pxQueue->uxItemSize != /*(UBaseType_t)*/0U)));

  /* RTOS ports that support interrupt nesting have the concept of a maximum
         system call (or maximum API call) interrupt priority.  Interrupts that
     are above the maximum system call priority are kept permanently enabled,
     even when the RTOS kernel is in a critical section, but cannot make any
     calls to FreeRTOS API functions.  If configASSERT() is defined in
     FreeRTOSConfig.h then portASSERT_IF_INTERRUPT_PRIORITY_INVALID() will
     result in an assertion failure if a FreeRTOS API function is called from an
     interrupt that has been assigned a priority above the configured maximum
     system call priority. Only FreeRTOS functions that end in FromISR can be
     called from interrupts that have been assigned a priority at or (logically)
     below the maximum
         system call	interrupt priority.  FreeRTOS maintains a separate
     interrupt safe API to ensure interrupt entry is as fast and as simple as
     possible. More information (albeit Cortex-M specific) is provided on the
     following link: http://www.freertos.org/RTOS-Cortex-M3-M4.html */
  portASSERT_IF_INTERRUPT_PRIORITY_INVALID();

  uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR();
  {
    const UBaseType_t uxMessagesWaiting = pxQueue->uxMessagesWaiting;

    /* Cannot block in an ISR, so check there is data available. */
    if (uxMessagesWaiting > /*(UBaseType_t)*/0) {
      const int8_t cRxLock = pxQueue->cRxLock;

      traceQUEUE_RECEIVE_FROM_ISR(pxQueue);

      prvCopyDataFromQueue(pxQueue, pvBuffer);
      pxQueue->uxMessagesWaiting = uxMessagesWaiting - /*(UBaseType_t)*/1;

      /* If the queue is locked the event list will not be modified.
                           Instead update the lock count so the task that
         unlocks the queue will know that an ISR has removed data while the
         queue was locked. */
      if (cRxLock == ((int8_t)-1)) {
        if (listLIST_IS_EMPTY(&(pxQueue->xTasksWaitingToSend)) == pdFALSE) {
          if (xTaskRemoveFromEventList(&(pxQueue->xTasksWaitingToSend)) !=
              pdFALSE) {
            /* The task waiting has a higher priority than us so
                                                      force a context switch. */
            if (pxHigherPriorityTaskWoken != NULL) {
              *pxHigherPriorityTaskWoken = pdTRUE;
            } else {
              mtCOVERAGE_TEST_MARKER();
            }
          } else {
            mtCOVERAGE_TEST_MARKER();
          }
        } else {
          mtCOVERAGE_TEST_MARKER();
        }
      } else {
        /* Increment the lock count so the task that unlocks the queue
                                    knows that data was removed while it was
           locked. */
        pxQueue->cRxLock = (int8_t)(cRxLock + 1);
      }

      xReturn = pdPASS;
    } else {
      xReturn = pdFAIL;
      traceQUEUE_RECEIVE_FROM_ISR_FAILED(pxQueue);
    }
  }
  portCLEAR_INTERRUPT_MASK_FROM_ISR(uxSavedInterruptStatus);

  return xReturn;
}
/*-----------------------------------------------------------*/

BaseType_t xQueuePeekFromISR(QueueHandle_t xQueue, void *const pvBuffer) {
  BaseType_t xReturn;
  UBaseType_t uxSavedInterruptStatus;
  int8_t *pcOriginalReadPosition;
#ifdef VERIFAST
  Queue_t * pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  configASSERT(pxQueue);
  configASSERT(
      !((pvBuffer == NULL) && (pxQueue->uxItemSize != /*(UBaseType_t)*/0U)));
  configASSERT(pxQueue->uxItemSize != 0); /* Can't peek a semaphore. */

  /* RTOS ports that support interrupt nesting have the concept of a maximum
         system call (or maximum API call) interrupt priority.  Interrupts that
     are above the maximum system call priority are kept permanently enabled,
     even when the RTOS kernel is in a critical section, but cannot make any
     calls to FreeRTOS API functions.  If configASSERT() is defined in
     FreeRTOSConfig.h then portASSERT_IF_INTERRUPT_PRIORITY_INVALID() will
     result in an assertion failure if a FreeRTOS API function is called from an
     interrupt that has been assigned a priority above the configured maximum
     system call priority. Only FreeRTOS functions that end in FromISR can be
     called from interrupts that have been assigned a priority at or (logically)
     below the maximum
         system call	interrupt priority.  FreeRTOS maintains a separate
     interrupt safe API to ensure interrupt entry is as fast and as simple as
     possible. More information (albeit Cortex-M specific) is provided on the
     following link: http://www.freertos.org/RTOS-Cortex-M3-M4.html */
  portASSERT_IF_INTERRUPT_PRIORITY_INVALID();

  uxSavedInterruptStatus = portSET_INTERRUPT_MASK_FROM_ISR();
  {
    /* Cannot block in an ISR, so check there is data available. */
    if (pxQueue->uxMessagesWaiting > /*(UBaseType_t)*/0) {
      traceQUEUE_PEEK_FROM_ISR(pxQueue);

      /* Remember the read position so it can be reset as nothing is
                           actually being removed from the queue. */
      pcOriginalReadPosition = pxQueue->u.xQueue.pcReadFrom;
      prvCopyDataFromQueue(pxQueue, pvBuffer);
      pxQueue->u.xQueue.pcReadFrom = pcOriginalReadPosition;

      xReturn = pdPASS;
    } else {
      xReturn = pdFAIL;
      traceQUEUE_PEEK_FROM_ISR_FAILED(pxQueue);
    }
  }
  portCLEAR_INTERRUPT_MASK_FROM_ISR(uxSavedInterruptStatus);

  return xReturn;
}
/*-----------------------------------------------------------*/

UBaseType_t uxQueueMessagesWaiting(const QueueHandle_t xQueue) {
  UBaseType_t uxReturn;

  configASSERT(xQueue);

  taskENTER_CRITICAL();
  { uxReturn = ((Queue_t *)xQueue)->uxMessagesWaiting; }
  taskEXIT_CRITICAL();

  return uxReturn;
} /*lint !e818 Pointer cannot be declared const as xQueue is a typedef not
     pointer. */
/*-----------------------------------------------------------*/

UBaseType_t uxQueueSpacesAvailable(const QueueHandle_t xQueue) {
  UBaseType_t uxReturn;
#ifdef VERIFAST
  Queue_t * pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  configASSERT(pxQueue);

  taskENTER_CRITICAL();
  { uxReturn = pxQueue->uxLength - pxQueue->uxMessagesWaiting; }
  taskEXIT_CRITICAL();

  return uxReturn;
} /*lint !e818 Pointer cannot be declared const as xQueue is a typedef not
     pointer. */
/*-----------------------------------------------------------*/

UBaseType_t uxQueueMessagesWaitingFromISR(const QueueHandle_t xQueue) {
  UBaseType_t uxReturn;
#ifdef VERIFAST
  Queue_t * pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  configASSERT(pxQueue);
  taskENTER_CRITICAL_FROM_ISR();
  uxReturn = pxQueue->uxMessagesWaiting;
  taskEXIT_CRITICAL_FROM_ISR();

  return uxReturn;
} /*lint !e818 Pointer cannot be declared const as xQueue is a typedef not
     pointer. */
/*-----------------------------------------------------------*/

void vQueueDelete(QueueHandle_t xQueue) {
#ifdef VERIFAST
  Queue_t * pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  configASSERT(pxQueue);
  traceQUEUE_DELETE(pxQueue);
  {
    /* The queue can only have been allocated dynamically - free it
                  again. */
    vPortFree(pxQueue);
  }
}
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/

static UBaseType_t
prvGetDisinheritPriorityAfterTimeout(const Queue_t *const pxQueue) {
  UBaseType_t uxHighestPriorityOfWaitingTasks;

  /* If a task waiting for a mutex causes the mutex holder to inherit a
                priority, but the waiting task times out, then the holder should
                disinherit the priority - but only down to the highest priority
     of any other tasks that are waiting for the same mutex.  For this purpose,
                return the priority of the highest priority task that is waiting
     for the mutex. */
  if (listCURRENT_LIST_LENGTH(&(pxQueue->xTasksWaitingToReceive)) > 0U) {
    uxHighestPriorityOfWaitingTasks =
        (UBaseType_t)configMAX_PRIORITIES -
        (UBaseType_t)listGET_ITEM_VALUE_OF_HEAD_ENTRY(
            &(pxQueue->xTasksWaitingToReceive));
  } else {
    uxHighestPriorityOfWaitingTasks = tskIDLE_PRIORITY;
  }

  return uxHighestPriorityOfWaitingTasks;
}

/*-----------------------------------------------------------*/

static BaseType_t prvCopyDataToQueue(Queue_t *const pxQueue,
                                     const void *pvItemToQueue,
                                     const BaseType_t xPosition) {
  BaseType_t xReturn = pdFALSE;
  UBaseType_t uxMessagesWaiting;

  /* This function is called from a critical section. */

  uxMessagesWaiting = pxQueue->uxMessagesWaiting;

  if (pxQueue->uxItemSize == /*(UBaseType_t)*/0) {

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
    (void)memcpy(
        (void *)pxQueue->pcWriteTo, pvItemToQueue,
        (size_t)pxQueue
            ->uxItemSize); /*lint !e961 !e418 !e9087 MISRA exception as the
                              casts are only redundant for some ports, plus
                              previous logic ensures a null pointer can only be
                              passed to memcpy() if the copy size is 0.  Cast to
                              void required by function signature and safe as no
                              alignment requirement and copy length specified in
                              bytes. */
    pxQueue->pcWriteTo +=
        pxQueue->uxItemSize; /*lint !e9016 Pointer arithmetic on char types ok,
                                especially in this use case where it is the
                                clearest way of conveying intent. */
    if (pxQueue->pcWriteTo >=
        pxQueue->u.xQueue
            .pcTail) /*lint !e946 MISRA exception justified as comparison of
                        pointers is the cleanest solution. */
    {
      pxQueue->pcWriteTo = pxQueue->pcHead;
    } else {
      mtCOVERAGE_TEST_MARKER();
    }
  } else {
    (void)memcpy(
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

  return xReturn;
}
/*-----------------------------------------------------------*/

static void prvCopyDataFromQueue(Queue_t *const pxQueue, void *const pvBuffer) {
  if (pxQueue->uxItemSize != /*(UBaseType_t)*/0) {
    pxQueue->u.xQueue.pcReadFrom +=
        pxQueue->uxItemSize; /*lint !e9016 Pointer arithmetic on char types ok,
                                especially in this use case where it is the
                                clearest way of conveying intent. */
    if (pxQueue->u.xQueue.pcReadFrom >=
        pxQueue->u.xQueue
            .pcTail) /*lint !e946 MISRA exception justified as use of the
                        relational operator is the cleanest solutions. */
    {
      pxQueue->u.xQueue.pcReadFrom = pxQueue->pcHead;
    } else {
      mtCOVERAGE_TEST_MARKER();
    }
    (void)memcpy(
        (void *)pvBuffer, (void *)pxQueue->u.xQueue.pcReadFrom,
        (size_t)pxQueue
            ->uxItemSize); /*lint !e961 !e418 !e9087 MISRA exception as the
                              casts are only redundant for some ports.  Also
                              previous logic ensures a null pointer can only be
                              passed to memcpy() when the count is 0.  Cast to
                              void required by function signature and safe as no
                              alignment requirement and copy length specified in
                              bytes. */
  }
}
/*-----------------------------------------------------------*/

static void prvUnlockQueue(Queue_t *const pxQueue) {
  /* THIS FUNCTION MUST BE CALLED WITH THE SCHEDULER SUSPENDED. */

  /* The lock counts contains the number of extra data items placed or
         removed from the queue while the queue was locked.  When a queue is
         locked items can be added or removed, but the event lists cannot be
         updated. */
  taskENTER_CRITICAL();
  {
    int8_t cTxLock = pxQueue->cTxLock;

    /* See if data was added to the queue while it was locked. */
    while (cTxLock > (/*(int8_t)*/0)) {
      /* Data was posted while the queue was locked.  Are any tasks
                           blocked waiting for data to become available? */
      {
        /* Tasks that are removed from the event list will get added to
                                    the pending ready list as the scheduler is
           still suspended. */
        if (listLIST_IS_EMPTY(&(pxQueue->xTasksWaitingToReceive)) == pdFALSE) {
          if (xTaskRemoveFromEventList(&(pxQueue->xTasksWaitingToReceive)) !=
              pdFALSE) {
            /* The task waiting has a higher priority so record that
                                                      a context switch is
               required. */
            vTaskMissedYield();
          } else {
            mtCOVERAGE_TEST_MARKER();
          }
        } else {
          break;
        }
      }

      --cTxLock;
    }

    pxQueue->cTxLock = ((int8_t)-1);
  }
  taskEXIT_CRITICAL();

  /* Do the same for the Rx lock. */
  taskENTER_CRITICAL();
  {
    int8_t cRxLock = pxQueue->cRxLock;

    while (cRxLock > (/*(int8_t)*/0)) {
      if (listLIST_IS_EMPTY(&(pxQueue->xTasksWaitingToSend)) == pdFALSE) {
        if (xTaskRemoveFromEventList(&(pxQueue->xTasksWaitingToSend)) !=
            pdFALSE) {
          vTaskMissedYield();
        } else {
          mtCOVERAGE_TEST_MARKER();
        }

        --cRxLock;
      } else {
        break;
      }
    }

    pxQueue->cRxLock = ((int8_t)-1);
  }
  taskEXIT_CRITICAL();
}
/*-----------------------------------------------------------*/

static BaseType_t prvIsQueueEmpty(const Queue_t *pxQueue) {
  BaseType_t xReturn;

  taskENTER_CRITICAL();
  {
    if (pxQueue->uxMessagesWaiting == /*(UBaseType_t)*/0) {
      xReturn = pdTRUE;
    } else {
      xReturn = pdFALSE;
    }
  }
  taskEXIT_CRITICAL();

  return xReturn;
}
/*-----------------------------------------------------------*/

BaseType_t xQueueIsQueueEmptyFromISR(const QueueHandle_t xQueue) {
  BaseType_t xReturn;
#ifdef VERIFAST
  Queue_t * pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  configASSERT(pxQueue);
  if (pxQueue->uxMessagesWaiting == /*(UBaseType_t)*/0) {
    xReturn = pdTRUE;
  } else {
    xReturn = pdFALSE;
  }

  return xReturn;
} /*lint !e818 xQueue could not be pointer to const because it is a typedef. */
/*-----------------------------------------------------------*/

static BaseType_t prvIsQueueFull(const Queue_t *pxQueue) {
  BaseType_t xReturn;

  taskENTER_CRITICAL();
  {
    if (pxQueue->uxMessagesWaiting == pxQueue->uxLength) {
      xReturn = pdTRUE;
    } else {
      xReturn = pdFALSE;
    }
  }
  taskEXIT_CRITICAL();

  return xReturn;
}
/*-----------------------------------------------------------*/

BaseType_t xQueueIsQueueFullFromISR(const QueueHandle_t xQueue) {
  BaseType_t xReturn;
#ifdef VERIFAST
  Queue_t * pxQueue = xQueue;
#else
  Queue_t *const pxQueue = xQueue;
#endif

  configASSERT(pxQueue);
  if (pxQueue->uxMessagesWaiting == pxQueue->uxLength) {
    xReturn = pdTRUE;
  } else {
    xReturn = pdFALSE;
  }

  return xReturn;
} /*lint !e818 xQueue could not be pointer to const because it is a typedef. */
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
/*-----------------------------------------------------------*/
#endif
