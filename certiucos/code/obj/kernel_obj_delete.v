
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

(* the code for the function that deletes a kernel object *)
Definition kernel_obj_delete_impl := 
OS_EVENT∗ ·kernel_obj_delete·(⌞ptr @ OS_EVENT∗⌟)··{  
           ⌞
             tasks_waiting @ Int8u; 
             x @ Int8u
           ⌟;

            ENTER_CRITICAL;ₛ  
            If (ptr′ ==ₑ NULL){
                EXIT_CRITICAL;ₛ  
                RETURN ptr′
            };ₛ
            If (ptr′→OSEventType !=ₑ ′OS_EVENT_TYPE_SEM){
                EXIT_CRITICAL;ₛ  
                RETURN ptr′
            };ₛ
            IF (ptr′→OSEventGrp !=ₑ ′0){
                tasks_waiting′ =ₑ ′1
            }ELSE{
                tasks_waiting′ =ₑ ′0
            };ₛ
            WHILE (ptr′→OSEventGrp !=ₑ ′0) { 
                x′ =ₑ ′OS_STAT_SEM;ₛ  
                OS_EventTaskRdy(­ptr′, 〈Void ∗〉NULL, x′­)
            };ₛ 
            OS_EventRemove(­ptr′­);ₛ
            ptr′→OSEventType =ₑ ′OS_EVENT_TYPE_UNUSED;ₛ
            ptr′→OSEventListPtr =ₑ OSEventFreeList′;ₛ
            OSEventFreeList′ =ₑ ptr′;ₛ     
            OSTCBCur′→__OSTskPtr =ₑ NULL;ₛ 
            EXIT_CRITICAL;ₛ  

            If (tasks_waiting′ ==ₑ ′1) { 
                OS_Sched(­)
            };ₛ  
            RETURN  NULL 
}·.

Close Scope code_scope.
