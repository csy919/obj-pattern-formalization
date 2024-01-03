Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import kernel_obj_delete.
Require Import abs_op.

Require Import kobj_delete_pure.

(* Require Import OSQDel. 
Require Import OSQDelPure_ext. *)

Definition kobjdel_null  (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) =>
    vl =  (Vnull::nil) /\
    opv =  (Some Vnull) /\
    O_opt = Some O1
  end.

Definition kobjdel_type_err (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) =>
    exists ptr,
    vl =  ((Vptr ptr)::nil) /\  
    (
      exists els,
        get O1 absecblsid = Some (absecblist els) /\
        (~ exists n wls, get els ptr = Some (abssem n,wls)) /\  
        opv = (Some (Vptr ptr)) /\
        O_opt = Some O1
    )
  end.

Definition kobjdel_succ_nex_wait (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) => 
    exists ptr,
    vl=  ((Vptr ptr)::nil) /\
    (
      exists els els' n,
        opv = None /\
        get O1 absecblsid = Some (absecblist els) /\
        get els ptr = Some (abssem n, nil) /\
        join els' (sig ptr (abssem n, nil)) els /\
        O_opt = Some (set O1 absecblsid (absecblist els'))
    )
  end.

Definition kobjdel_succ_ex_wait (vl: vallist) (O1 : osabst) (rst : option val * option osabst):=
  match rst with
  | (opv, O_opt) => 
      exists ptr,
    vl=  ((Vptr ptr)::nil) /\
    (
      exists els els' n wls tls tls',
       opv = None /\
        get O1 absecblsid = Some (absecblist els) /\
        get els ptr = Some (abssem n, wls) /\
        wls <> nil /\
        join els' (sig ptr (abssem n, wls)) els /\
        get O1 abstcblsid = Some (abstcblist tls) /\ 
        tls' = set_tls_rdy wls tls /\
        O_opt = Some (set (set O1 absecblsid (absecblist els')) abstcblsid (abstcblist tls'))
    )
  end.

Definition kobjdel_ret (vl: vallist) (O1 : osabst) (rst : option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
    vl = nil /\
    opv = Some Vnull /\
    O_opt = Some O1
  end.  

(* the abstract program for the function **kernel_obj_delete** *) 
Definition kobjdel  (vl: vallist) :=
  match vl with
    v1 :: nil =>
      kobjdel_null (|vl|) ??
      kobjdel_type_err (|vl|) ??
      (kobjdel_succ_ex_wait (|vl|);; isched;; kobjdel_ret (|nil|) ??
        kobjdel_succ_nex_wait (|vl|);; kobjdel_ret (|nil|))   
  | _ => ABORT
  end.


Fixpoint spec_code_cons (s1:spec_code) (s2:spec_code) :=
  match s1 with
  | sp1 ?? sp2 => (spec_code_cons sp1 s2) ?? (spec_code_cons sp2 s2)
  | sp1 ;; sp2 => sp1 ;; (spec_code_cons sp2 s2)
  | _ => s1 ;; s2
  end.

Require Export os_inv.
Require Import ifun_spec.

Local Open Scope list_scope.

(* Open Scope int_scope. *)

Definition KObjDelPre' (vl:vallist) (logicl:list logicvar) ct := 
  EX s ptrv, 
  (Aie true ** Ais nil ** Acs nil ** Aisr empisr **
        [| logicl = logic_code s :: nil |] **
        <|| spec_code_cons (kobjdel vl)  s ||>**  
        [| nth_val 0 vl = Some ptrv |] ** 
        p_local OSLInv ct
            (logic_val (V$ 1)
                   :: logic_val (V$ __Loc_objdel)
                   :: logic_val ptrv :: nil)). 

Theorem KObjDelPreGood (vl:vallist) ll ct: 
  GoodFunAsrt (KObjDelPre' vl ll ct).
Proof.
  simpl.
  tauto.
Qed.

Definition KObjDelPre : fpre :=
  fun vl ll ct => mkfunasrt (KObjDelPreGood vl ll ct).

Definition KObjDelPost' (vl:vallist) (v:option val) (logicl:list logicvar) ct :=
  EX s, 
    (Aie true ** Ais nil ** Acs nil ** Aisr empisr **
       [| logicl = logic_code s :: nil |] **
       [| v = Some Vnull |] ** 
       <|| s ||> **
       p_local OSLInv ct
                (logic_val (V$ 1)
                   :: logic_val (V$ __Loc_objdel)
                   :: logic_val Vnull :: nil)).

Theorem KObjDelPostGood (vl:vallist) (v:option val) ll ct: 
  GoodFunAsrt (KObjDelPost' vl v ll ct). 
Proof.
  simpl.
  tauto.
Qed.

Definition KObjDelPost : fpost :=
  fun vl v ll ct => mkfunasrt (KObjDelPostGood vl v ll ct).

Definition KObjDel_spec : fspec :=
  (KObjDelPre, KObjDelPost, (Tptr OS_EVENT, (Tptr OS_EVENT)::nil)).

Definition new_osq_spec_list := 
  (((kernel_obj_delete, KObjDel_spec) :: nil) ++ osq_spec_list).


Definition new_OS_spec :=  convert_spec new_osq_spec_list.


