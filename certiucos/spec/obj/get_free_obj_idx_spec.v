
Require Import include_frm.
Require Import os_code_defs. 

Require Import ifun_spec.
Require Export os_inv.
Require Import List.

Require Import Maps. 

Require Import get_free_obj_idx.

Require Import obj_common.
Require Import obj_common_ext. 


Open Scope code_scope.
Open Scope int_scope.

(* pre *)

(* the pre-condition for the function **get_free_obj_idx** *) 
Definition getFreeObjIdxPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX s objvl lg', 
    Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) **
    AObjArr objvl **
     A_isr_is_prop ** <||s||> **
    [|logicl = logic_llv objvl :: logic_code s :: lg'|] ** 
    p_local OSLInv ct (logic_val (V$ 1) :: lg'). 

Theorem getFreeObjIdxPreGood (vl:vallist) ll ct:
  GoodFunAsrt (getFreeObjIdxPre' vl ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition getFreeObjIdxPre : fpre :=
  fun vl ll ct => mkfunasrt (getFreeObjIdxPreGood vl ll ct).

Open Scope int_scope.
Local Open Scope Z_scope.

(* the post-condition for the function **get_free_obj_idx** *) 
Definition getFreeObjIdxPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  (EX s objvl i lg',
    Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) **
      AObjArr objvl **
      A_isr_is_prop ** <||s||> **
      [| nth_ObjArr_free_P i objvl  |] **
      [| v = Some (V$ i)|] **
      [|logicl = logic_llv objvl :: logic_code s :: lg' |] ** p_local OSLInv ct (logic_val (V$1) :: lg')) \\// (*return i*)
    (EX s objvl lg',
      Aisr empisr ** Aie false ** Ais nil ** Acs (true :: nil) **
        AObjArr objvl **
        A_isr_is_prop ** <||s||> **
        [| ObjArr_full_P objvl |] ** 
        [| v = Some (V$ 255)|] **
        [|logicl = logic_llv objvl :: logic_code s :: lg'|] ** p_local OSLInv ct (logic_val (V$1) :: lg')). (*return 255*) 


Theorem getFreeObjIdxGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (getFreeObjIdxPost' vl v ll ct).
Proof.
  GoodFunAsrt_solver.
Qed.

Definition getFreeObjIdxPost : fpost :=
  fun vl v ll ct => mkfunasrt (getFreeObjIdxGood vl v ll ct).

Open Scope list_scope.
Local Open Scope code_scope.

Definition getFreeObjIdx_spec : fspec := (getFreeObjIdxPre,getFreeObjIdxPost,(Int8s, nil)). 

Definition new_osq_spec_list := 
  (get_free_obj_idx, getFreeObjIdx_spec) ::
  nil.  

Definition new_OS_spec :=  convert_spec new_osq_spec_list.

Close Scope list_scope.

(* modified/new in os_program.v *)

Definition new_internal_fun_list := 
  (get_free_obj_idx_impl :: nil)%list. 

Definition new_os_internal :=  convert_cfuns new_internal_fun_list. 
