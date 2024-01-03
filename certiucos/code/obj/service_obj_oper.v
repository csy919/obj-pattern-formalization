
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

Definition PlaceHolder:= &ₐ OSPlaceHolder′.

(* the code for the function that operates on a service object *)
Definition service_obj_oper_impl :=
Int32 ·service_obj_oper·(⌞idx @ Int32⌟)··{   
        ⌞
         err @ Int32;
         p @ OS_EVENT ∗
        ⌟;

        ENTER_CRITICAL;ₛ 
        If (idx′ <ₑ ′0 ||ₑ idx′ ≥ ′MAX_OBJ_NUM){
           EXIT_CRITICAL;ₛ 
           RETURN  ′-1
        };ₛ
        p′ =ₑ efield (obj_arr′[idx′]) ptr;ₛ  
        If (p′ ==ₑ NULL ||ₑ p′ ==ₑ 〈OS_EVENT ∗〉PlaceHolder) { 
            EXIT_CRITICAL;ₛ
            RETURN ′-1
        };ₛ
        OSTCBCur′→__OSTskPtr =ₑ p′;ₛ 
        EXIT_CRITICAL;ₛ

        err′ =ᶠ kernel_obj_oper(· p′ ·);ₛ  
        
        ENTER_CRITICAL;ₛ
        OSTCBCur′→__OSTskPtr =ₑ NULL;ₛ   
        EXIT_CRITICAL;ₛ

        RETURN  err′
}· .

Close Scope code_scope.         
