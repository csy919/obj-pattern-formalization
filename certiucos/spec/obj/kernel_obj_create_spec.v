Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import kernel_obj_create.

Local Open Scope Z_scope.

Definition kobjcre_no_free (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
    | (opv, O_opt) =>
      exists n v',
        vl = ((Vint32 n) :: v' :: nil) /\
        (Z.leb (Int.unsigned n) Int16.max_unsigned) = true /\
        opv = Some Vnull /\
        (v'= Vnull /\ O_opt = Some O1  \/ v' <> Vnull /\ O_opt = None) 
  end.

Definition kobjcre_ecb_activate (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    exists n sid sls v,
      vl = ((Vint32 n) :: v :: nil) /\
      (Z.leb (Int.unsigned n) Int16.max_unsigned) = true /\
      opv = Some (Vptr sid) /\
      get O1 absecblsid = Some (absecblist sls) /\
      get sls sid = None /\
     ( v = Vptr sid /\ O_opt = Some (set O1 absecblsid (absecblist (set sls sid (abssem n, nil))))
       \/ v <> Vptr sid /\ O_opt = None)
  end.

(* the abstract program for the function **kernel_obj_create** *)
Definition kobjcre (vl: vallist) :=
  match vl with
    vn :: v' :: nil => 
    kobjcre_no_free (| vn :: v' :: nil |) ??
    kobjcre_ecb_activate (| vn :: v' :: nil |)
  | _ => ABORT 
  end. 

Require Export os_inv.
Require Import ifun_spec.

Local Open Scope list_scope.

Definition KObjCreatePre' (vl:vallist) (logicl:list logicvar) ct :=
  EX s v',
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr **
      [| logicl = logic_val v' :: logic_code s :: nil |] **
      <|| (kobjcre (vl++(v' ::nil)));; s ||> **
      p_local OSLInv ct init_lg).

Theorem KObjCreatePreGood (vl:vallist) ll ct:
  GoodFunAsrt (KObjCreatePre' vl ll ct).
Proof.
simpl.
tauto.
Qed.

Definition KObjCreatePre : fpre :=
  fun vl ll ct => mkfunasrt (KObjCreatePreGood vl ll ct).

Definition KObjCreatePost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s v' ptrv vloc, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr **
      [| logicl = logic_val v' :: logic_code s :: nil |] **
      [| v = Some v' /\ isptr v' /\ v' = ptrv /\ ptrv <> Vptr vhold_addr |] ** 
      [| v' = Vnull /\ vloc = Vint32 ($__Loc_normal) \/
          v' <> Vnull /\ vloc = Vint32 ($__Loc_objcre) |] **
      <|| s ||> ** 
      p_local OSLInv ct (logic_val (V$ 1)
                                   :: logic_val vloc 
                                   :: logic_val ptrv :: nil)).


Theorem KObjCreatePostGood (vl:vallist) (v:option val) ll ct:
  GoodFunAsrt (KObjCreatePost' vl v ll ct).
Proof.
simpl.
tauto.
Qed.

Definition KObjCreatePost : fpost :=
  fun vl v ll ct => mkfunasrt (KObjCreatePostGood vl v ll ct).

(*should be completed*)

Require Import List.
Require Import ifun_spec.

Local Open Scope code_scope.
Local Open Scope list_scope.

Definition KObjCreate_spec : fspec:= (KObjCreatePre,KObjCreatePost,(Tptr OS_EVENT, Int16u::nil)).

Definition new_osq_spec_list := 
  (((kernel_obj_create, KObjCreate_spec) :: nil) ++ osq_spec_list).


Definition new_OS_spec :=  convert_spec new_osq_spec_list.

(* Close Scope list_scope. *)

(* modified/new in os_program.v *)
Require Import os_program.

Definition new_internal_fun_list := 
  ((kernel_obj_create_impl :: nil) ++ internal_fun_list) %list. 

Definition new_os_internal :=   convert_cfuns new_internal_fun_list.
