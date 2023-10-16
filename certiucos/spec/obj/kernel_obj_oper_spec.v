Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import kernel_obj_oper.

Definition kobjoper_succ  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) =>
    exists vp verr,
    vl =  (vp:: verr :: nil) /\
    opv =  (Some (Vint32 (Int.repr OS_NO_ERR))) /\
    ((verr = (Vint32 (Int.repr OS_NO_ERR)) /\ O_opt = Some O1)
    \/ verr <> (Vint32 (Int.repr OS_NO_ERR)) /\ O_opt = None)
  end.

Definition kobjoper  (vl: vallist) :=
  match vl with
    v1 :: v2 :: nil =>
      kobjoper_succ (|vl|)
  | _ => ABORT
  end.

Require Export os_inv.
Require Import ifun_spec.

Local Open Scope list_scope.

(* Open Scope int_scope. *)

Definition KObjOperPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX s ptrv v',
  (Aie true ** Ais nil ** Acs nil ** Aisr empisr **
        [| logicl =  logic_val v' :: logic_code s :: nil |] **
        <|| (kobjoper (vl++(v' ::nil))) ;; s ||>**  
        [| nth_val 0 vl = Some ptrv |] ** 
        p_local OSLInv ct
            (logic_val (V$ 1)
                   :: logic_val (V$ __Loc_normal)
                   :: logic_val ptrv :: nil)).

Theorem KObjOperPreGood (vl:vallist) ll ct: 
  GoodFunAsrt (KObjOperPre' vl ll ct).
Proof.
  simpl.
  tauto.
Qed.

Definition KObjOperPre : fpre :=
  fun vl ll ct => mkfunasrt (KObjOperPreGood vl ll ct).

Definition KObjOperPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s ptrv v',
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr **
       [| logicl =  logic_val v' :: logic_code s :: nil |] **
       [| v = Some (Vint32 (Int.repr OS_NO_ERR)) /\ v = Some v' |] ** 
       <|| s ||> **
        [| nth_val 0 vl = Some ptrv |] ** 
       p_local OSLInv ct
                (logic_val (V$ 1)
                   :: logic_val (V$ __Loc_normal)
                   :: logic_val ptrv :: nil)).

Theorem KObjOperPostGood (vl:vallist) (v:option val) ll ct: 
  GoodFunAsrt (KObjOperPost' vl v ll ct). 
Proof.
  simpl.
  tauto.
Qed.

Definition KObjOperPost : fpost :=
  fun vl v ll ct => mkfunasrt (KObjOperPostGood vl v ll ct).

Definition KObjOper_spec : fspec :=
  (KObjOperPre, KObjOperPost, (Tint32, (Tptr OS_EVENT)::nil)).

Definition new_osq_spec_list := 
  (((kernel_obj_oper, KObjOper_spec) :: nil) ++ osq_spec_list).


Definition new_OS_spec :=  convert_spec new_osq_spec_list.


