
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

Definition PlaceHolder:= &ₐ OSPlaceHolder′.

(* the code for the function that creates a service object *)
Definition service_obj_create_impl :=
Int32 ·service_obj_create·(⌞katt @ Int16u ; satt @ Int32u⌟)··{  
        ⌞
         idx @ Int32;
         y @ Int8s;
         p @ OS_EVENT ∗
        ⌟;

        ENTER_CRITICAL;ₛ
        y′ =ᶠ get_free_obj_idx(·);ₛ 
        idx′ =ₑ 〈Int32〉 y′;ₛ
        If (idx′ ==ₑ ′255) {
            EXIT_CRITICAL;ₛ 
            RETURN  ′-1
        };ₛ
        efield (obj_arr′[idx′]) ptr =ₑ 〈OS_EVENT ∗〉 PlaceHolder;ₛ
        EXIT_CRITICAL;ₛ

        p′ =ᶠ kernel_obj_create(· katt′ ·);ₛ

        ENTER_CRITICAL;ₛ
        efield (obj_arr′[idx′]) ptr =ₑ  p′;ₛ
        If (p′ ==ₑ NULL) { 
            EXIT_CRITICAL;ₛ 
            RETURN  ′-1 
        };ₛ
        efield (obj_arr′[idx′]) attr =ₑ satt′;ₛ  
        OSTCBCur′→__OSTskLoc =ₑ ′__Loc_normal;ₛ  
        OSTCBCur′→__OSTskPtr =ₑ NULL;ₛ
        EXIT_CRITICAL;ₛ 

        RETURN  idx′
 }· .

Close Scope code_scope.
 
