Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

(*os_q.c*)
Open Scope code_scope.

Definition OSQAccept_impl := 
 Void ∗ ·OSQAccept·(⌞ptr @ OS_EVENT∗⌟)··{
        ⌞ 
          message @ Void ∗;
          pq @ OS_Q ∗ ;
          legal @ Int8u
        ⌟; 
               
          If(ptr′ ==ₑ NULL){
              RETURN 〈Void ∗〉 NULL 
          };ₛ
          ENTER_CRITICAL;ₛ
          legal′ =ᶠ OS_EventSearch(·ptr′·);ₛ
          If (legal′ ==ₑ ′0){
              EXIT_CRITICAL;ₛ
              RETURN 〈Void ∗〉 NULL 
          };ₛ
          If (ptr′→OSEventType !=ₑ ′OS_EVENT_TYPE_Q){
            EXIT_CRITICAL;ₛ
            RETURN 〈Void ∗〉 NULL 
          };ₛ
          pq′ =ₑ ptr′→OSEventPtr;ₛ
          IF (pq′→OSQEntries >ₑ ′0){
              message′ =ₑ ∗(pq′→ OSQOut);ₛ
              pq′ → OSQOut =ₑ pq′→OSQOut +ₑ ′1 ;ₛ
              −− pq′→OSQEntries;ₛ
             If (pq′→OSQOut ==ₑ pq′→OSQEnd){
                 pq′→OSQOut =ₑ pq′→OSQStart
             }
          }ELSE{
              message′ =ₑ NULL
          };ₛ
          EXIT_CRITICAL;ₛ
          RETURN  message′ 
 }· .



Definition OSQCreate_impl :=
 OS_EVENT ∗ ·OSQCreate·(⌞size @ Int16u⌟)··{
        ⌞ 
          ptr @ OS_EVENT ∗;
          pq @ OS_Q ∗;
          pqblk @ OS_Q_FREEBLK ∗;
          start @ Void ∗∗
        ⌟; 

          If ((size′ >ₑ ′OS_MAX_Q_SIZE ) ||ₑ (size′ ==ₑ ′0)){
              RETURN 〈OS_EVENT ∗〉 NULL
          };ₛ
          ENTER_CRITICAL;ₛ
          ptr′ =ₑ OSEventFreeList′;ₛ
          If (OSEventFreeList′ !=ₑ NULL){
              OSEventFreeList′ =ₑ  〈OS_EVENT ∗〉 OSEventFreeList′→OSEventListPtr
          };ₛ
          EXIT_CRITICAL;ₛ
          If (ptr′ !=ₑ NULL) {
              ENTER_CRITICAL;ₛ
              pq′ =ₑ OSQFreeList′;ₛ
              pqblk′ =ₑ OSQFreeBlk′;ₛ
              IF (pq′ !=ₑ NULL &&ₑ  pqblk′ !=ₑ NULL){
                  OSQFreeList′ =ₑ OSQFreeList′→OSQPtr;ₛ 
                  OSQFreeBlk′ =ₑ OSQFreeBlk′→nextblk;ₛ
                  pq′→qfreeblk =ₑ pqblk′;ₛ
                  start′ =ₑ pqblk′→msgqueuetbl;ₛ
                  pq′→OSQStart =ₑ start′;ₛ
                  pq′→OSQEnd =ₑ &ₐstart′[size′];ₛ
                  pq′→OSQIn =ₑ start′;ₛ 
                  pq′→OSQOut =ₑ start′;ₛ
                  pq′→OSQSize =ₑ size′;ₛ
                  pq′→OSQEntries =ₑ ′0;ₛ
                  OS_EventWaitListInit(­ptr′­);ₛ
                  ptr′→OSEventType =ₑ ′OS_EVENT_TYPE_Q;ₛ
                  ptr′→OSEventCnt =ₑ ′0;ₛ
                  ptr′→OSEventPtr =ₑ pq′;ₛ
                  ptr′→OSEventListPtr =ₑ OSEventList′;ₛ
                  OSEventList′ =ₑ ptr′;ₛ
                  EXIT_CRITICAL
              }ELSE{
                  ptr′→OSEventListPtr =ₑ 〈Void∗〉 OSEventFreeList′;ₛ
                  OSEventFreeList′ =ₑ  ptr′;ₛ
                  EXIT_CRITICAL;ₛ
                  ptr′ =ₑ NULL
              }
          };ₛ
          RETURN ptr′
 }· .

Definition OSQDel_impl := 
 Int8u ·OSQDel·(⌞ ptr @ OS_EVENT ∗⌟)··{
        ⌞ 
         tasks_waiting @ Int8u;
         pq @ OS_Q ∗;
         x @ OS_Q_FREEBLK ∗;
         legal @ Int8u
        ⌟; 
         
        If (ptr′ ==ₑ  NULL){
             RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
        ENTER_CRITICAL;ₛ
        legal′ =ᶠ OS_EventSearch(·ptr′·);ₛ
        If (legal′ ==ₑ ′0){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_PEVENT_NULL
        };ₛ 
        If (ptr′→OSEventType !=ₑ ′OS_EVENT_TYPE_Q){
            EXIT_CRITICAL;ₛ
             RETURN ′OS_ERR_EVENT_TYPE
        };ₛ  
        IF (ptr′→OSEventGrp !=ₑ ′0){
            tasks_waiting′ =ₑ ′1
        }ELSE{
            tasks_waiting′ =ₑ ′0
        };ₛ
        IF (tasks_waiting′ ==ₑ ′0){
            OS_EventRemove(­ptr′­);ₛ
            pq′ =ₑ ptr′→OSEventPtr;ₛ
            x′ =ₑ pq′→qfreeblk;ₛ
            x′→nextblk =ₑ OSQFreeBlk′;ₛ
            OSQFreeBlk′ =ₑ pq′→qfreeblk;ₛ
            pq′→OSQPtr =ₑ OSQFreeList′;ₛ
            OSQFreeList′ =ₑ pq′;ₛ
            ptr′→OSEventType =ₑ ′OS_EVENT_TYPE_UNUSED;ₛ
            ptr′→OSEventListPtr =ₑ OSEventFreeList′;ₛ
            OSEventFreeList′ =ₑ ptr′;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′OS_NO_ERR
        }ELSE{
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_TASK_WAITING
        }    
 }· . 

 
Definition OSQPend_impl :=
 Int8u ·OSQPend·(⌞ ptr @ OS_EVENT ∗; timeout @ Int16u ⌟)··{
         ⌞ 
         message @ Void∗;
         pq @ OS_Q ∗;
         legal @ Int8u
        ⌟; 

        If (ptr′ ==ₑ  NULL){
             RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
        ENTER_CRITICAL;ₛ
        legal′ =ᶠ OS_EventSearch(·ptr′·);ₛ
        If (legal′ ==ₑ ′0){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_PEVENT_NULL
        };ₛ 
        If (ptr′→OSEventType !=ₑ ′OS_EVENT_TYPE_Q){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
        If (OSTCBCur′→OSTCBPrio ==ₑ ′OS_IDLE_PRIO){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
        If ( (OSTCBCur′→OSTCBStat  !=ₑ ′OS_STAT_RDY) ||ₑ (OSTCBCur′→OSTCBDly  !=ₑ ′0)){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_PEVENT_NULL
        };ₛ     
        OSTCBCur′→OSTCBMsg =ₑ NULL;ₛ
        pq′ =ₑ ptr′→OSEventPtr;ₛ
        If (pq′→OSQEntries >ₑ ′0) {
            message′ =ₑ ∗(pq′→OSQOut);ₛ
            pq′→ OSQOut =ₑ pq′→OSQOut +ₑ ′1;ₛ
            −− pq′→OSQEntries;ₛ
            If (pq′→OSQOut ==ₑ pq′→OSQEnd){
                pq′→OSQOut =ₑ pq′→OSQStart
            };ₛ
            OSTCBCur′→OSTCBMsg =ₑ message′;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′OS_NO_ERR 
        };ₛ
        OSTCBCur′→OSTCBStat =ₑ ′OS_STAT_Q;ₛ
        OSTCBCur′→OSTCBDly =ₑ timeout′;ₛ
        OS_EventTaskWait(­ptr′­);ₛ
        EXIT_CRITICAL;ₛ
        OS_Sched(­);ₛ
        ENTER_CRITICAL;ₛ
        message′ =ₑ OSTCBCur′→OSTCBMsg;ₛ                                 
        If (message′ !=ₑ NULL){
          
            EXIT_CRITICAL;ₛ
            RETURN ′OS_NO_ERR
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′OS_TIMEOUT
  }· .


 
Definition OSQGetMsg_impl := 
 Void∗ ·OSQGetMsg·(⌞ ⌟)··{
         ⌞
           message @ Void∗
         ⌟;

         ENTER_CRITICAL;ₛ
         message′ =ₑ  OSTCBCur′→OSTCBMsg;ₛ
         OSTCBCur′→OSTCBMsg =ₑ NULL;ₛ
         EXIT_CRITICAL;ₛ
         RETURN message′ 
 }· . 


Definition OSQPost_impl :=
 Int8u ·OSQPost·(⌞ptr @ OS_EVENT∗ ;  message @ Void∗⌟)··{
        ⌞
         pq @ OS_Q∗;
         legal @ Int8u;
         x  @ Int8u
        ⌟;
        
        If (ptr′ ==ₑ NULL){
           RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
        If (message′ ==ₑ NULL){
          RETURN  ′OS_ERR_POST_NULL_PTR
        };ₛ
        ENTER_CRITICAL;ₛ
        legal′ =ᶠ OS_EventSearch(·ptr′·);ₛ
        If (legal′ ==ₑ ′0){
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_ERR_PEVENT_NULL
          };ₛ
        If (ptr′→OSEventType !=ₑ ′OS_EVENT_TYPE_Q){
            EXIT_CRITICAL;ₛ
            RETURN  ′OS_ERR_PEVENT_NULL
        };ₛ
        If (ptr′→OSEventGrp !=ₑ ′0) {
            x′ =ₑ ′OS_STAT_Q;ₛ 
            OS_EventTaskRdy(­ptr′, message′, x′­);ₛ
            EXIT_CRITICAL;ₛ
            OS_Sched(­);ₛ
            RETURN ′OS_NO_ERR 
        };ₛ
        pq′ =ₑ ptr′→OSEventPtr;ₛ
        If (pq′→OSQEntries ≥ pq′→OSQSize) {
            EXIT_CRITICAL;ₛ
            RETURN ′OS_Q_FULL
        };ₛ
        ∗(pq′→OSQIn) =ₑ message′;ₛ
        ++ (pq′→OSQIn);ₛ
        ++ (pq′→OSQEntries);ₛ
        If (pq′→OSQIn ==ₑ pq′→OSQEnd) {
            pq′→OSQIn =ₑ pq′→OSQStart
        };ₛ
        EXIT_CRITICAL;ₛ
        RETURN ′OS_NO_ERR 
 }· . 

Close Scope code_scope.
