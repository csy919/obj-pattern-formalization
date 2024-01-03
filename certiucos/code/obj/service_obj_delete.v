
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

(* the code for the function that deletes a service object *) 
Definition service_obj_delete_impl :=
Int32 ·service_obj_delete·(⌞idx @ Int32⌟)··{
        ⌞
         p @ OS_EVENT∗
        ⌟;

        ENTER_CRITICAL;ₛ
        If (idx′ <ₑ ′0 ||ₑ idx′ ≥ ′MAX_OBJ_NUM) {
            EXIT_CRITICAL;ₛ
            RETURN  ′-1
        };ₛ
        p′ =ₑ efield (obj_arr′[idx′]) ptr;ₛ
        If (p′ ==ₑ NULL ||ₑ p′ ==ₑ 〈OS_EVENT ∗〉PlaceHolder) { 
            EXIT_CRITICAL;ₛ
            RETURN  ′-1
        };ₛ 
        efield (obj_arr′[idx′]) ptr =ₑ 〈OS_EVENT ∗〉 NULL;ₛ
        OSTCBCur′→__OSTskLoc =ₑ  ′__Loc_objdel;ₛ  
        OSTCBCur′→__OSTskPtr =ₑ  p′;ₛ
        EXIT_CRITICAL;ₛ

        kernel_obj_delete(­ p′ ­);ₛ 

        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskLoc =ₑ  ′__Loc_normal;ₛ    
        EXIT_CRITICAL;ₛ

        RETURN  ′0
}· .

Close Scope code_scope. 
