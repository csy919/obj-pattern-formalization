
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

(* **kernel_obj_oper** is the function that operates on a kernel object *)
(* since the operation is not a specific one, the code cannot be written *) 
(* with any potential code that reads and updates the kernel object,
     the auxliary variables need not be updated in such a function, and
     the spec. for this function can be used as a component for the spec. 
     of the corresponding service function **service_obj_oper** *) 
Definition kernel_obj_oper_impl :=
  Int32 ·kernel_obj_oper·(⌞ptr @ OS_EVENT∗⌟)··{ 
        ⌞⌟; 
        RETURN ′OS_NO_ERR
}·.

Close Scope code_scope.
