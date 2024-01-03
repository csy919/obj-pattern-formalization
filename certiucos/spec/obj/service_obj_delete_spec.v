Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import service_obj_delete.
Require Import kernel_obj_delete_spec.
Require Import ifun_spec.

Open Scope list_scope.

Definition sobjdel_idxerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
     exists idx,
     vl = (Vint32 idx) :: nil /\ 
      (Int.ltu idx Int.zero = true \/
       Int.ltu (Int.repr MAX_OBJ_NUM) idx = true \/ Int.eq idx (Int.repr MAX_OBJ_NUM) = true) /\  
      opv = Some (Vint32 (Int.mone)) /\ 
       O_opt = Some O1
  end.

Definition sobjdel_kobjerr
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
     exists idx objs,
     vl = (Vint32 idx) :: nil /\
     Int.ltu idx Int.zero = false /\
     Int.ltu idx (Int.repr MAX_OBJ_NUM) = true /\
     get O1 absobjsid = Some (absobjs objs) /\
     ~ (exists ptr attr, get objs idx = Some (objid ptr, attr)) /\
      opv = Some (Vint32 (Int.mone)) /\
       O_opt = Some O1
  end.

Definition sobjdel_set_kobj
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
     exists idx objs attr ptr vptr,
     vl = (Vint32 idx) :: (vptr) :: nil /\
     Int.ltu idx Int.zero = false /\
     Int.ltu idx (Int.repr MAX_OBJ_NUM) = true /\
     get O1 absobjsid = Some (absobjs objs) /\
     get objs idx = Some (objid ptr, attr) /\
     opv = None /\
     (vptr = Vptr ptr /\ O_opt = Some (set O1 absobjsid (absobjs (set objs idx (objnull, attr))))
      \/ vptr <> Vptr ptr /\ O_opt = None)
  end.

Definition sobjdel_del_succ
  (vl: vallist) (O1: osabst) (rst: option val * option osabst) :=
  match rst with
  | (opv, O_opt) =>
     vl = nil /\
     opv = Some (Vint32 Int.zero) /\
     O_opt = Some O1
  end.

(* the abstract program for the function service_obj_delete *) 
Definition sobjdel (vl: vallist) :=
  match vl with
    vidx :: vptr :: nil => 
      sobjdel_idxerr (| vidx :: nil |) ??
      sobjdel_kobjerr (| vidx :: nil |) ?? 
      (sobjdel_set_kobj (| vidx :: vptr :: nil |) ;; spec_code_cons (kobjdel (vptr :: nil)) (sobjdel_del_succ (| nil |)))
  | _ => ABORT
  end.

Local Open Scope code_scope.

Require Import os_program.
Require Import abs_op.
Require Import include_frm.
Require Import os_code_defs.
Require Import os_spec.

Require Import os_inv.
Require Import inv_prop.

Require Import init_spec.

Local Open Scope list_scope.

Definition sobjdelapi := (sobjdel, (Tint32, Tint32 :: nil)).

Definition new_api_spec_list := 
  (service_obj_delete, sobjdelapi) ::
  nil.

Definition new_api_spec := convert_api_spec new_api_spec_list.

Definition new_os_spec := (new_api_spec, GetHPrio).

