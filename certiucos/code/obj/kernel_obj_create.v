
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

(* the code for the function that creates a kernel object *) 
Definition kernel_obj_create_impl := 
OS_EVENT∗ ·kernel_obj_create·(⌞attr @ Int16u⌟)··{ 
         ⌞ptr @ OS_EVENT∗⌟;

        ENTER_CRITICAL;ₛ
        ptr′ =ₑ OSEventFreeList′;ₛ
        If (OSEventFreeList′ !=ₑ NULL){
            OSEventFreeList′ =ₑ  〈OS_EVENT∗〉 OSEventFreeList′→OSEventListPtr
        };ₛ
        If (ptr′ !=ₑ NULL) {
           ptr′→OSEventType =ₑ ′OS_EVENT_TYPE_SEM;ₛ
           ptr′→OSEventCnt =ₑ attr′;ₛ 
           ptr′→OSEventPtr =ₑ NULL;ₛ
           OS_EventWaitListInit(­ptr′­);ₛ  
           ptr′→OSEventListPtr =ₑ OSEventList′;ₛ
           OSEventList′ =ₑ ptr′;ₛ
           OSTCBCur′→__OSTskLoc =ₑ ′__Loc_objcre;ₛ   
           OSTCBCur′→__OSTskPtr =ₑ ptr′
        };ₛ 
        EXIT_CRITICAL;ₛ 
        RETURN  ptr′ 
 }·.

Close Scope code_scope.

