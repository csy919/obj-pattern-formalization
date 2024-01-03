
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

(* the code for the function that gets the index for an unused service object *)
Definition get_free_obj_idx_impl := 
  Int8s ·get_free_obj_idx·(⌞⌟)··{ 
        ⌞
          i @ Int32
       ⌟;
         i′ =ₑ ′0;ₛ
         WHILE (i′ <ₑ ′MAX_OBJ_NUM) {
             If ((efield (obj_arr′[i′]) ptr) ==ₑ NULL) { 
                 RETURN 〈Int8s〉 i′
             };ₛ
              ++ i′
         };ₛ
         RETURN ′255
}· . 

Close Scope code_scope. 
