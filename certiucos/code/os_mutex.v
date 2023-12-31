Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

(*os_mutex.c*)

Open Scope code_scope.

Definition OSMutexAccept_impl := 
 Int8u ·OSMutexAccept·(⌞ptr @ OS_EVENT∗⌟)··{
        ⌞ 
          legal @ Int8u;
          pip @ Int8u
        ⌟; 
               
          If(ptr′ ==ₑ NULL){
              RETURN ′0 
          };ₛ
          ENTER_CRITICAL;ₛ
          legal′ =ᶠ OS_EventSearch(·ptr′·);ₛ
          If (legal′ ==ₑ ′0){
              EXIT_CRITICAL;ₛ
              RETURN ′0 
          };ₛ
          If (ptr′→OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX){
            EXIT_CRITICAL;ₛ
            RETURN ′0
          };ₛ
          pip′  =ₑ 〈Int8u〉(ptr′→OSEventCnt ≫ ′8);ₛ
          If ((OSTCBCur′→OSTCBPrio <ₑ pip′) ||ₑ (OSTCBCur′→OSTCBPrio ==ₑ pip′)){
            EXIT_CRITICAL;ₛ
            RETURN ′0
          };ₛ
          If ((ptr′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8) ==ₑ ′OS_MUTEX_AVAILABLE){
            ptr′→OSEventCnt =ₑ ptr′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_UPPER_8;ₛ
            ptr′→OSEventCnt =ₑ ptr′→OSEventCnt |ₑ OSTCBCur′→OSTCBPrio;ₛ
            ptr′→OSEventPtr =ₑ OSTCBCur′;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′1 
          };ₛ
          EXIT_CRITICAL;ₛ
          RETURN ′0  
}· .

(* Definition PlaceHolder:= &ₐ OSPlaceHolder′. *)

Definition OSMutexCreate_impl := 
OS_EVENT∗ ·OSMutexCreate·(⌞prio @ Int8u⌟)··{
           ⌞ptr @ OS_EVENT∗⌟;

            If (prio′ ≥ ′OS_LOWEST_PRIO) {                         
                RETURN 〈OS_EVENT ∗〉 NULL
            };ₛ
            ENTER_CRITICAL;ₛ
            If (OSTCBPrioTbl′[prio′] !=ₑ NULL) {
                EXIT_CRITICAL;ₛ
                RETURN 〈OS_EVENT ∗〉 NULL               
            };ₛ                   
            ptr′ =ₑ OSEventFreeList′;ₛ
            If (OSEventFreeList′ !=ₑ NULL){
                OSEventFreeList′ =ₑ  〈OS_EVENT∗〉 OSEventFreeList′→OSEventListPtr
            };ₛ
            IF (ptr′ !=ₑ NULL){
                OS_EventWaitListInit(­ptr′­);ₛ  
                ptr′→OSEventType =ₑ ′OS_EVENT_TYPE_MUTEX;ₛ
                ptr′→OSEventCnt  =ₑ ((〈Int16u〉prio′) ≪ ′8) |ₑ ′OS_MUTEX_AVAILABLE;ₛ  
                ptr′→OSEventPtr  =ₑ NULL;ₛ
                ptr ′ → OSEventListPtr =ₑ OSEventList ′;ₛ
                OSTCBPrioTbl′[prio′] =ₑ 〈OS_TCB ∗〉 PlaceHolder;ₛ
                OSEventList′ =ₑ ptr′;ₛ
                EXIT_CRITICAL;ₛ
                RETURN ptr′          
            }ELSE{
                EXIT_CRITICAL;ₛ
                RETURN 〈OS_EVENT ∗〉 NULL
            }
 }·.

Definition OSMutexDel_impl := 
 Int8u ·OSMutexDel·(⌞ ptr @ OS_EVENT ∗⌟)··{
        ⌞ 
         tasks_waiting @ Int8u;
         pip @ Int8u;
         legal @ Int8u
        ⌟; 
         
        If (ptr′ ==ₑ  NULL){
             RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
        ENTER_CRITICAL;ₛ
        legal′ =ᶠ OS_EventSearch(·ptr′·);ₛ
        If (legal′ ==ₑ ′0){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_PEVENT_NO_EX
        };ₛ 
        If (ptr′→OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_EVENT_TYPE
        };ₛ  
        IF (ptr′→OSEventGrp !=ₑ ′0   ||ₑ ( ( ptr′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8  )!=ₑ  ′OS_MUTEX_AVAILABLE)){
            tasks_waiting′ =ₑ ′1
        }ELSE{
            tasks_waiting′ =ₑ ′0
        };ₛ
        IF (tasks_waiting′ ==ₑ ′0){
            pip′ =ₑ 〈Int8u〉 (ptr′→OSEventCnt ≫ ′8);ₛ
            If ( OSTCBPrioTbl′[pip′]  !=ₑ 〈OS_TCB ∗〉 PlaceHolder){
                EXIT_CRITICAL;ₛ
                RETURN ′OS_ERR_MUTEXPR_NOT_HOLDER
            };ₛ
            OS_EventRemove(­ptr′­);ₛ
            OSTCBPrioTbl′[pip′] =ₑ NULL;ₛ
            ptr′→OSEventType =ₑ ′OS_EVENT_TYPE_UNUSED;ₛ
            ptr′→OSEventListPtr =ₑ OSEventFreeList′;ₛ
            ptr′→OSEventCnt =ₑ ′0;ₛ                 
            OSEventFreeList′ =ₑ ptr′;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′OS_NO_ERR
        }ELSE{
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_TASK_WAITING
        }    
 }· .

Require Import ZArith. 

Definition OSMutexPend_impl :=
 Int8u ·OSMutexPend·(⌞ ptr @ OS_EVENT ∗; timeout @ Int16u ⌟)··{
         ⌞ 
           legal @ Int8u;
           pip @ Int8u;
           mprio @ Int8u;
           isrdy @ Int8u;
           ptcb @ (Tptr OS_TCB);
           ptr2 @ (Tptr OS_EVENT)
        ⌟; 

        If (ptr′ ==ₑ  NULL){
             RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
        ENTER_CRITICAL;ₛ
        legal′ =ᶠ OS_EventSearch(·ptr′·);ₛ
        If (legal′ ==ₑ ′0){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_PEVENT_NO_EX
        };ₛ 
        If (ptr′→OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_EVENT_TYPE
        };ₛ
        If (OSTCBCur′→OSTCBPrio ==ₑ ′OS_IDLE_PRIO){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_IDLE
        };ₛ
        If ( (OSTCBCur′→OSTCBStat !=ₑ ′OS_STAT_RDY) ||ₑ (OSTCBCur′→OSTCBDly !=ₑ ′0)){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_STAT
        };ₛ
        If (OSTCBCur′→OSTCBMsg !=ₑ NULL) {
            EXIT_CRITICAL;ₛ 
            RETURN  ′OS_ERR_PEVENT_NULL 
        };ₛ
           
        pip′  =ₑ 〈Int8u〉(ptr′→OSEventCnt ≫ ′8);ₛ
        If (OSTCBCur′→OSTCBPrio <ₑ pip′ ||ₑ (OSTCBCur′→OSTCBPrio ==ₑ pip′)){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_MUTEX_PRIO
        };ₛ
        mprio′ =ₑ 〈Int8u〉(ptr′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8);ₛ
        ptcb′  =ₑ ptr′→OSEventPtr;ₛ                                                  
       
        If (mprio′ ==ₑ ′OS_MUTEX_AVAILABLE) {
            ptr′→OSEventCnt =ₑ ptr′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_UPPER_8;ₛ
            ptr′→OSEventCnt =ₑ ptr′→OSEventCnt |ₑ OSTCBCur′→OSTCBPrio;ₛ
            ptr′→OSEventPtr =ₑ OSTCBCur′;ₛ
            EXIT_CRITICAL;ₛ
            RETURN ′OS_NO_ERR 
        };ₛ

        If(ptcb′ ==ₑ OSTCBCur′){
          EXIT_CRITICAL;ₛ
          RETURN ′OS_ERR_MUTEX_DEADLOCK
        };ₛ
        If(ptcb′→OSTCBPrio ==ₑ ′OS_IDLE_PRIO){
          EXIT_CRITICAL;ₛ
          RETURN ′OS_ERR_MUTEX_IDLE
        };ₛ
        If ( (ptcb′→OSTCBStat !=ₑ ′OS_STAT_RDY) ||ₑ (ptcb′→OSTCBDly !=ₑ ′0)){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_NEST
        };ₛ
        If(mprio′ ==ₑ (OSTCBCur′→OSTCBPrio)){
          EXIT_CRITICAL;ₛ
          RETURN ′OS_ERR_MUTEX_DEADLOCK
        };ₛ
        
        IF ((ptcb′→OSTCBPrio !=ₑ pip′) &&ₑ (mprio′ >ₑ (OSTCBCur′→OSTCBPrio))){  (*Need to promote prio of owner?*)
            If ( OSTCBPrioTbl′[pip′]  !=ₑ 〈OS_TCB ∗〉 PlaceHolder){
                EXIT_CRITICAL;ₛ
                RETURN ′OS_ERR_MUTEXPR_NOT_HOLDER
            };ₛ
           
            OSTCBPrioTbl′[ ptcb′→OSTCBPrio ] =ₑ 〈OS_TCB ∗〉 PlaceHolder;ₛ
            OSTCBPrioTbl′[pip′] =ₑ 〈OS_TCB ∗〉 ptcb′;ₛ

                OSRdyTbl′[ptcb′→OSTCBY] =ₑ OSRdyTbl′[ptcb′→OSTCBY]&ₑ(∼ptcb′→OSTCBBitX);ₛ
                If (OSRdyTbl′[ptcb′→OSTCBY] ==ₑ ′0)
                {
                    OSRdyGrp′ =ₑ OSRdyGrp′ &ₑ (∼ptcb′→OSTCBBitY)
                };ₛ  
                ptcb′→OSTCBPrio =ₑ pip′;ₛ                             (* Change owner task prio to PIP            *)
                ptcb′→OSTCBY    =ₑ ptcb′→OSTCBPrio ≫ ′3;ₛ
                ptcb′→OSTCBBitY =ₑ OSMapTbl′[ptcb′→OSTCBY];ₛ
                ptcb′→OSTCBX    =ₑ (ptcb′→OSTCBPrio) &ₑ ′7;ₛ
                ptcb′→OSTCBBitX =ₑ OSMapTbl′[ptcb′→OSTCBX];ₛ
                OSRdyGrp′ =ₑ OSRdyGrp′ |ₑ ptcb′→OSTCBBitY;ₛ     (* ... make it ready at new priority.       *)
                OSRdyTbl′[ptcb′→OSTCBY] =ₑ OSRdyTbl′[ptcb′→OSTCBY] |ₑ ptcb′→OSTCBBitX;ₛ
                 
                OSTCBCur′→OSTCBStat =ₑ ′OS_STAT_MUTEX;ₛ
                OSTCBCur′→OSTCBDly =ₑ timeout′;ₛ
                OS_EventTaskWait(­ptr′­);ₛ
                EXIT_CRITICAL;ₛ
                OS_Sched(­);ₛ
                ENTER_CRITICAL;ₛ
                If (OSTCBCur′→OSTCBMsg !=ₑ NULL){
                   EXIT_CRITICAL;ₛ
                   RETURN ′OS_NO_ERR
                };ₛ
                EXIT_CRITICAL;ₛ
                RETURN ′OS_TIMEOUT   
          
        } ELSE {
          OSTCBCur′→OSTCBStat =ₑ ′OS_STAT_MUTEX;ₛ
          OSTCBCur′→OSTCBDly =ₑ timeout′;ₛ
          OS_EventTaskWait(­ptr′­);ₛ
          EXIT_CRITICAL;ₛ
          OS_Sched(­);ₛ
          ENTER_CRITICAL;ₛ
          If (OSTCBCur′→OSTCBMsg !=ₑ NULL){
              EXIT_CRITICAL;ₛ
              RETURN ′OS_NO_ERR
          };ₛ
          EXIT_CRITICAL;ₛ
          RETURN ′OS_TIMEOUT 
        }
                   
}· .

Definition OSMutexPost_impl :=
 Int8u ·OSMutexPost·(⌞ptr @ OS_EVENT∗ ⌟)··{
        ⌞
         x @ Int8u;
         pip @ Int8u;
         prio  @ Int8u;
         legal @ Int8u
        ⌟;
        
        If (ptr′ ==ₑ NULL){
           RETURN ′OS_ERR_PEVENT_NULL
        };ₛ
        ENTER_CRITICAL;ₛ
        legal′ =ᶠ OS_EventSearch(·ptr′·);ₛ
        If (legal′ ==ₑ ′0){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_PEVENT_NO_EX
           };ₛ
        If (ptr′→OSEventType !=ₑ ′OS_EVENT_TYPE_MUTEX){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_EVENT_TYPE
        };ₛ
        
        pip′  =ₑ 〈Int8u〉(ptr′→OSEventCnt ≫ ′8);ₛ
        prio′ =ₑ 〈Int8u〉(ptr′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_LOWER_8);ₛ    
        If (OSTCBCur′ !=ₑ ptr′→OSEventPtr) {   (* See if posting task owns the MUTEX*)
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_NOT_MUTEX_OWNER
        };ₛ                                                                     
        If (OSTCBCur′→OSTCBPrio <ₑ pip′){         (**)
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_MUTEX_PRIO
        };ₛ
        legal′ =ₑ OSUnMapTbl′[ptr′→OSEventGrp];ₛ
        x′ =ₑ (legal′≪ ′3) +ₑ OSUnMapTbl′[ptr′→OSEventTbl[legal′]];ₛ
        If ( ptr′→OSEventGrp !=ₑ ′0 &&ₑ (x′ <ₑ pip′ ||ₑ  x′ ==ₑ pip′)){
            EXIT_CRITICAL;ₛ
            RETURN ′OS_ERR_MUTEX_WL_HIGHEST_PRIO
        };ₛ
        If(OSTCBCur ′ → OSTCBStat !=ₑ ′OS_STAT_RDY ||ₑ OSTCBCur ′ → OSTCBDly !=ₑ ′0){
                EXIT_CRITICAL;ₛ
                RETURN ′OS_ERR_ORIGINAL_NOT_HOLDER
        };ₛ
        If (OSTCBCur′→OSTCBPrio ==ₑ pip′) {
          (* Did we have to raise current task's priority? *)
          (* Yes, Return to original priority              *)
          (*      Remove owner from ready list at 'pip'    *)
            If ( OSTCBPrioTbl′[prio′]  !=ₑ 〈OS_TCB ∗〉 PlaceHolder){
                EXIT_CRITICAL;ₛ
                RETURN ′OS_ERR_ORIGINAL_NOT_HOLDER
               };ₛ
            
            OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ OSRdyTbl′[OSTCBCur′→OSTCBY] &ₑ (∼OSTCBCur′→OSTCBBitX);ₛ
            If ( OSRdyTbl′[OSTCBCur′→OSTCBY] ==ₑ ′0) {
                OSRdyGrp′ =ₑ OSRdyGrp′ &ₑ ∼OSTCBCur′→OSTCBBitY
            };ₛ
            OSTCBCur′→OSTCBPrio         =ₑ prio′;ₛ
            OSTCBCur′→OSTCBY            =ₑ prio′ ≫  ′3;ₛ
            OSTCBCur′→OSTCBBitY         =ₑ OSMapTbl′[OSTCBCur′→OSTCBY];ₛ
            OSTCBCur′→OSTCBX            =ₑ prio′ &ₑ ′7;ₛ
            OSTCBCur′→OSTCBBitX         =ₑ OSMapTbl′[OSTCBCur′→OSTCBX];ₛ
            OSRdyGrp′                    =ₑ OSRdyGrp′ |ₑ OSTCBCur′→OSTCBBitY;ₛ
            OSRdyTbl′[OSTCBCur′→OSTCBY] =ₑ OSRdyTbl′[OSTCBCur′→OSTCBY] |ₑ OSTCBCur′→OSTCBBitX;ₛ
            OSTCBPrioTbl′[prio′]         =ₑ 〈OS_TCB ∗〉 OSTCBCur′;ₛ
            OSTCBPrioTbl′[pip′]          =ₑ 〈OS_TCB ∗〉 PlaceHolder
        };ₛ
        If (ptr′→OSEventGrp !=ₑ ′0) {
            x′ =ₑ ′OS_STAT_MUTEX;ₛ 
            prio′ =ᶠ OS_EventTaskRdy(·ptr′, 〈Void ∗〉 ptr′, x′·);ₛ
            ptr′→OSEventCnt =ₑ ptr′→OSEventCnt &ₑ ′OS_MUTEX_KEEP_UPPER_8;ₛ  (*Save priority of mutex's new owner *)
            ptr′→OSEventCnt =ₑ ptr′→OSEventCnt |ₑ prio′;ₛ
            ptr′→OSEventPtr =ₑ OSTCBPrioTbl′[prio′];ₛ     (*Link to mutex owner's OS_TCB*)
     
            EXIT_CRITICAL;ₛ
            OS_Sched(­);ₛ
            RETURN ′OS_NO_ERR 
        };ₛ
        ptr′→OSEventCnt =ₑ ptr′→OSEventCnt |ₑ ′OS_MUTEX_AVAILABLE;ₛ (* No,  Mutex is now available   *)
        ptr′→OSEventPtr =ₑ NULL;ₛ
   
        EXIT_CRITICAL;ₛ
        RETURN ′OS_NO_ERR 
 }· . 

Close Scope code_scope.
