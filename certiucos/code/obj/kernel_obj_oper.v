
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

Definition kernel_obj_oper_impl :=
  Int32 ·kernel_obj_oper·(⌞ptr @ OS_EVENT∗⌟)··{ 
        ⌞⌟; 
        RETURN ′OS_NO_ERR
}·.

Close Scope code_scope.
