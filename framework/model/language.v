Require Import memory.

Set Implicit Arguments.
Unset Strict Implicit.

(**The High-level Specification Language **)
Definition priority := int32.
Definition ecbid := addrval.
Definition msg := val.
Definition maxlen := int32.
Definition  ostime := int32.
Definition waitset := list tid.

Definition eid := addrval.

Inductive tcbstats:=
| os_stat_sem: ecbid -> tcbstats
| os_stat_q: ecbid -> tcbstats
| os_stat_postq: ecbid -> tcbstats
| os_stat_time:  tcbstats
| os_stat_mbox: ecbid -> tcbstats
| os_stat_mutexsem: ecbid -> tcbstats.

Inductive taskstatus :=
 | rdy: taskstatus
 | wait : tcbstats -> int32 -> taskstatus.

Module abstcb.
  Definition B : Set := ( priority * taskstatus * msg)%type.
  Definition holder : B:= (Int.zero, rdy, Vnull).
End abstcb.

Module TcbMod := MapLib.MapFun tidspec abstcb.

Program Instance TcbMap: PermMap tid ( priority * taskstatus * msg) TcbMod.map :=
  {
    usePerm := TcbMod.usePerm;
    isRw := TcbMod.isRw;
    flip := TcbMod.flip;
    sameV := TcbMod.sameV;
    same := TcbMod.same;
    emp := TcbMod.emp;
    join := TcbMod.join;
    del := TcbMod.del;
    get := TcbMod.get;
    set := TcbMod.set;
    sig := TcbMod.sig;
    merge := TcbMod.merge;
    minus := TcbMod.minus;
    map_dec_a := TcbMod.map_dec_a
}.
Next Obligation.
  apply TcbMod.map_join_emp.
Qed.
Next Obligation.
  apply TcbMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply TcbMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_eql; auto.
Qed.
Next Obligation.
  apply TcbMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply TcbMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_get_sig.
Qed.
Next Obligation.
  apply TcbMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply TcbMod.map_get_set.
Qed.
Next Obligation.
  apply TcbMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply TcbMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_set_emp.
Qed.
Next Obligation.
  apply TcbMod.map_set_sig.
Qed.
Next Obligation.
  apply TcbMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply TcbMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply TcbMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply TcbMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply TcbMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply TcbMod.map_del_sem.
Qed.

Definition owner:= option (tid * int32).

Inductive edata:=
| abssem: int32 -> edata
| absmsgq : list msg -> maxlen -> list tid -> edata
| absmbox: msg -> edata
| absmutexsem: int32 -> owner -> edata.

Module absecb.
  Definition B : Set := prod edata waitset.
  Definition holder : B := (absmbox Vnull, nil).
End absecb.

Module EcbMod := MapLib.MapFun tidspec absecb.

Program Instance EcbMap: PermMap tid (prod edata waitset) EcbMod.map :=
  {
    usePerm := EcbMod.usePerm;
    isRw := EcbMod.isRw;
    flip := EcbMod.flip;
    sameV := EcbMod.sameV;
    same := EcbMod.same;
    emp := EcbMod.emp;
    join := EcbMod.join;
    del := EcbMod.del;
    get := EcbMod.get;
    set := EcbMod.set;
    sig := EcbMod.sig;
    merge := EcbMod.merge;
    minus := EcbMod.minus;
    map_dec_a := EcbMod.map_dec_a
  }.
Next Obligation.
  apply EcbMod.map_join_emp.
Qed.
Next Obligation.
  apply EcbMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply EcbMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply EcbMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply EcbMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply EcbMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply EcbMod.map_eql; auto.
Qed.
Next Obligation.
  apply EcbMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply EcbMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply EcbMod.map_get_sig.
Qed.
Next Obligation.
  apply EcbMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply EcbMod.map_get_set.
Qed.
Next Obligation.
  apply EcbMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply EcbMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply EcbMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply EcbMod.map_set_emp.
Qed.
Next Obligation.
  apply EcbMod.map_set_sig.
Qed.
Next Obligation.
  apply EcbMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply EcbMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply EcbMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply EcbMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply EcbMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply EcbMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply EcbMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply EcbMod.map_del_sem.
Qed.

(* Module about abstract service objects *)

Inductive obj_id :=
| objid: addrval -> obj_id
| objnull
| objholder.

Module absobj.
  Definition B : Set := (obj_id * int32)%type.  
  Definition holder : B := (objnull, Int.repr 0).   
End absobj.

Module ObjMod := MapLib.MapFun idxspec absobj. 

Program Instance ObjMap: PermMap int32 (obj_id * int32) ObjMod.map :=    
 {
    usePerm := ObjMod.usePerm;
    isRw := ObjMod.isRw;
    flip := ObjMod.flip;
    sameV := ObjMod.sameV;
    same := ObjMod.same;
    emp := ObjMod.emp;
    join := ObjMod.join;
    del := ObjMod.del;
    get := ObjMod.get;
    set := ObjMod.set;
    sig := ObjMod.sig;
    merge := ObjMod.merge;
    minus := ObjMod.minus;
    map_dec_a := ObjMod.map_dec_a
}.

Next Obligation.
  apply ObjMod.map_join_emp.
Qed.
Next Obligation.
  apply ObjMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply ObjMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply ObjMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply ObjMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply ObjMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply ObjMod.map_eql; auto.
Qed.
Next Obligation.
  apply ObjMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply ObjMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply ObjMod.map_get_sig.
Qed.
Next Obligation.
  apply ObjMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply ObjMod.map_get_set.
Qed.
Next Obligation.
  apply ObjMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply ObjMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply ObjMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply ObjMod.map_set_emp.
Qed.
Next Obligation.
  apply ObjMod.map_set_sig.
Qed.
Next Obligation.
  apply ObjMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply ObjMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply ObjMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply ObjMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply ObjMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply ObjMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply ObjMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply ObjMod.map_del_sem.
Qed.

(* Module about abstract OSTCBPrioTbl block *)

Inductive eid_type : Type :=
Null | Holder | Valid_Addr: tid -> eid_type.

Module absptb.
  Definition B := ( eid_type )%type.
  Definition holder : B := ( Null ).
End absptb.

Module PtbMod := MapLib.MapFun idxspec absptb. 

Program Instance PtbMap: PermMap int32 ( eid_type ) PtbMod.map := 
 {
    usePerm := PtbMod.usePerm;
    isRw := PtbMod.isRw;
    flip := PtbMod.flip;
    sameV := PtbMod.sameV;
    same := PtbMod.same;
    emp := PtbMod.emp;
    join := PtbMod.join;
    del := PtbMod.del;
    get := PtbMod.get;
    set := PtbMod.set;
    sig := PtbMod.sig;
    merge := PtbMod.merge;
    minus := PtbMod.minus;
    map_dec_a := PtbMod.map_dec_a 
}.

Next Obligation.
  apply PtbMod.map_join_emp.
Qed.
Next Obligation.
  apply PtbMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply PtbMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply PtbMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply PtbMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply PtbMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply PtbMod.map_eql; auto.
Qed.
Next Obligation.
  apply PtbMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply PtbMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply PtbMod.map_get_sig.
Qed.
Next Obligation.
  apply PtbMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply PtbMod.map_get_set.
Qed.
Next Obligation.
  apply PtbMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply PtbMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply PtbMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply PtbMod.map_set_emp.
Qed.
Next Obligation.
  apply PtbMod.map_set_sig.
Qed.
Next Obligation.
  apply PtbMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply PtbMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply PtbMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply PtbMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply PtbMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply PtbMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply PtbMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply PtbMod.map_del_sem.
Qed.

(* Module about auxiliary variable for program location *)

Module absauxloc.
  Definition B : Set := val. 
  Definition holder : B := Vundef.  
End absauxloc. 

Module AuxLocMod := MapLib.MapFun tidspec absauxloc. 

Program Instance AuxLocMap: PermMap tid val AuxLocMod.map :=  
 {
    usePerm := AuxLocMod.usePerm;
    isRw := AuxLocMod.isRw;
    flip := AuxLocMod.flip;
    sameV := AuxLocMod.sameV;
    same := AuxLocMod.same;
    emp := AuxLocMod.emp;
    join := AuxLocMod.join;
    del := AuxLocMod.del;
    get := AuxLocMod.get;
    set := AuxLocMod.set;
    sig := AuxLocMod.sig;
    merge := AuxLocMod.merge;
    minus := AuxLocMod.minus;
    map_dec_a := AuxLocMod.map_dec_a
}.

Next Obligation.
  apply AuxLocMod.map_join_emp.
Qed.
Next Obligation.
  apply AuxLocMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply AuxLocMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply AuxLocMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply AuxLocMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply AuxLocMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply AuxLocMod.map_eql; auto.
Qed.
Next Obligation.
  apply AuxLocMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply AuxLocMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply AuxLocMod.map_get_sig.
Qed.
Next Obligation.
  apply AuxLocMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply AuxLocMod.map_get_set.
Qed.
Next Obligation.
  apply AuxLocMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply AuxLocMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply AuxLocMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply AuxLocMod.map_set_emp.
Qed.
Next Obligation.
  apply AuxLocMod.map_set_sig.
Qed.
Next Obligation.
  apply AuxLocMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply AuxLocMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply AuxLocMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply AuxLocMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply AuxLocMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply AuxLocMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply AuxLocMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply AuxLocMod.map_del_sem.
Qed.

(* Module about auxiliary variable for object  pointer *) 

Module absauxptr.
  Definition B : Set := val. 
  Definition holder : B := Vundef.   
End absauxptr. 

Module AuxPtrMod := MapLib.MapFun tidspec absauxptr. 

Program Instance AuxPtrMap: PermMap tid val AuxPtrMod.map := 
 {
    usePerm := AuxPtrMod.usePerm;
    isRw := AuxPtrMod.isRw;
    flip := AuxPtrMod.flip;
    sameV := AuxPtrMod.sameV;
    same := AuxPtrMod.same;
    emp := AuxPtrMod.emp;
    join := AuxPtrMod.join;
    del := AuxPtrMod.del;
    get := AuxPtrMod.get;
    set := AuxPtrMod.set;
    sig := AuxPtrMod.sig;
    merge := AuxPtrMod.merge;
    minus := AuxPtrMod.minus;
    map_dec_a := AuxPtrMod.map_dec_a 
}.

Next Obligation.
  apply AuxPtrMod.map_join_emp.
Qed.
Next Obligation.
  apply AuxPtrMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply AuxPtrMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply AuxPtrMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply AuxPtrMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply AuxPtrMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply AuxPtrMod.map_eql; auto.
Qed.
Next Obligation.
  apply AuxPtrMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply AuxPtrMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply AuxPtrMod.map_get_sig.
Qed.
Next Obligation.
  apply AuxPtrMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply AuxPtrMod.map_get_set.
Qed.
Next Obligation.
  apply AuxPtrMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply AuxPtrMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply AuxPtrMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply AuxPtrMod.map_set_emp.
Qed.
Next Obligation.
  apply AuxPtrMod.map_set_sig.
Qed.
Next Obligation.
  apply AuxPtrMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply AuxPtrMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply AuxPtrMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply AuxPtrMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply AuxPtrMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply AuxPtrMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply AuxPtrMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply AuxPtrMod.map_del_sem.
Qed. 


Inductive absdataid:=
| abstcblsid : absdataid
| absecblsid: absdataid
| ostmid : absdataid
| curtid:absdataid
| absptlsid: absdataid (* ostcbpriotbl *)
| absobjsid: absdataid (* abstract objects *) 
(* | auxlocid: absdataid (* auxiliary program location (not explicitly tracked in abstract state) *) *)
(* | auxptrid: absdataid (* auxiliary object pointer (not explicitly tracked in abstract state) *)  *) 
.

Definition absdataid_eq (id1 id2:absdataid):=
  match id1, id2 with
  | abstcblsid, abstcblsid => true
  | absecblsid, absecblsid => true
  | ostmid, ostmid => true
  | curtid, curtid => true
  | absptlsid, absptlsid => true
  | absobjsid, absobjsid => true
  (* | auxlocid, auxlocid => true  *)
  (* | auxptrid, auxptrid => true   *)
  | _, _ => false
  end.

Definition absdataid_lt (id1 id2:absdataid):=
  match id1, id2 with
  | abstcblsid, abstcblsid => false
  | abstcblsid, _ => true
  | absecblsid, abstcblsid => false
  | absecblsid, absecblsid => false
  | absecblsid, _ =>true
  | ostmid, abstcblsid =>false
  | ostmid, absecblsid => false
  | ostmid, ostmid => false
  | ostmid, _ => true
  | curtid, abstcblsid => false
  | curtid, absecblsid => false 
  | curtid, ostmid => false
  | curtid, curtid => false
  | curtid, _ => true  
  | absptlsid,abstcblsid => false (* ostcbpriotbl *)
  | absptlsid,absecblsid => false
  | absptlsid,ostmid => false
  | absptlsid,curtid => false
  | absptlsid,absptlsid => false
  | absptlsid,_ => true
  | absobjsid, _ (* abstcblsid *) => false (* abstract objs *) 
  (* | absobjsid, absecblsid => false *)
  (* | absobjsid, ostmid => false *)
  (* | absobjsid, curtid => false *)
  (* | absobjsid, absptlsid => false  *)
  (* | absobjsid, absobjsid => false  *)
  (* | absobjsid, _ => true  *)
  (* | auxlocid, abstcblsid => false (* auxliary program location *) *)
  (* | auxlocid, absecblsid => false  *)
  (* | auxlocid, ostmid => false  *)
  (* | auxlocid, curtid => false  *)
  (* | auxlocid, absptlsid => false *)
  (* | auxlocid, absobjsid => false  *)
  (* | auxlocid, auxlocid => false  *)
  (* | auxlocid, _ => true  *)
  (* | auxptrid, _ => false *)
  end.

Module absdataidspec.
  Definition A := absdataid.
  Definition beq := absdataid_eq.
  Definition blt := absdataid_lt.
 
Lemma beq_true_eq : forall a a' : A,
    beq a a' = true -> a = a'.
Proof.
  intros.
  destruct a,a';simpl in H;auto;tryfalse.
Qed.    


Lemma beq_false_neq : forall a a' : A,
    beq a a' = false -> a <> a'.
Proof. 
  intros.
  destruct a,a';simpl in H; introv Hf; auto;tryfalse.
Qed.  

Lemma eq_beq_true : forall a a' : A,
    a = a' -> beq a a' = true.
Proof.
  intros.
  destruct a,a';simpl in H;auto;tryfalse.
Qed.

Lemma neq_beq_false : forall a a' : A,
    a <> a' -> beq a a' = false.
Proof.
  intros.
  destruct a ,a';simpl in H;auto;tryfalse.
Qed.

Lemma blt_trans : 
  forall a a' a'' : A,
    blt a a' = true -> blt a' a'' = true -> blt a a'' = true.
Proof.
  unfold blt; intros.
  destruct a,a',a'';simpl in H, H0;auto;tryfalse.
Qed.

Lemma blt_irrefl :
  forall a : A,
    blt a a = false.
Proof.  
  unfold blt; intros.
  destruct a;simpl;auto.
Qed.

Lemma blt_asym : 
  forall a b : A, 
    blt a b = true -> blt b a = false.
Proof.  
  unfold blt; intros.
  destruct a,b;simpl in *;auto;tryfalse.
Qed.

Lemma blt_beq_dec :
  forall a b : A,
    {blt a b = true} + {beq a b = true} + {blt b a = true}.
Proof.
  unfold blt; unfold beq; intros.
  remember (absdataid_lt a b) as bool1; destruct bool1.
  left; left; auto.
  remember (absdataid_eq a b) as bool2; destruct bool2.
  left; right; auto.
  destruct a,b;simpl in *;auto;tryfalse.
Qed.  

End absdataidspec.

Inductive absdata:= 
| abstcblist: TcbMod.map -> absdata
| absecblist: EcbMod.map -> absdata
| ostm: ostime -> absdata
| oscurt: addrval -> absdata
| absptls: PtbMod.map -> absdata 
| absobjs: ObjMod.map -> absdata 
.

Module absdatastru.
 
 Definition B := absdata. 
 Definition holder : B := (abstcblist emp).
 
End absdatastru.

Module OSAbstMod := MapLib.MapFun absdataidspec absdatastru.

Definition osabst:= OSAbstMod.map. 

(* Definition abstdel := fun (M:OSAbstMod.map) a => OSAbstMod.minus M (OSAbstMod.sig a (abstcblist emp)). *)

Program Instance AMap: PermMap absdataid absdata osabst :=
  {
    usePerm := OSAbstMod.usePerm;
    isRw := OSAbstMod.isRw;
    flip := OSAbstMod.flip;
    sameV := OSAbstMod.sameV;
    same := OSAbstMod.same;
    emp := OSAbstMod.emp;
    join := OSAbstMod.join;
    del := OSAbstMod.del;
    get := OSAbstMod.get;
    set := OSAbstMod.set;
    sig := OSAbstMod.sig;
    merge := OSAbstMod.merge;
    minus := OSAbstMod.minus;
    map_dec_a := OSAbstMod.map_dec_a
  }.
Next Obligation.
  apply OSAbstMod.map_join_emp.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_eql; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_get_sig.
Qed.
Next Obligation.
  apply OSAbstMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_get_set.
Qed.
Next Obligation.
  apply OSAbstMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply OSAbstMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_set_emp.
Qed.
Next Obligation.
  apply OSAbstMod.map_set_sig.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply OSAbstMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply OSAbstMod.map_del_sem.
Qed.

Definition osabstep := vallist -> osabst -> (option val * option osabst) -> Prop.

Definition absexpr := osabst -> Prop.

Inductive spec_code:=
| spec_prim :  vallist-> osabstep -> spec_code
| sched : spec_code
| spec_crt : val -> val -> val -> spec_code
| spec_del : val -> spec_code
| spec_done : option val -> spec_code
| spec_seq : spec_code -> spec_code -> spec_code
| spec_choice : spec_code -> spec_code -> spec_code
| spec_assume : absexpr -> spec_code
| spec_assert : absexpr -> spec_code
| spec_abort : spec_code. 

Notation " x '(|' vl '|)' " := (spec_prim vl x) (at level 40).
Notation  " 'END' v " := (spec_done v)(at level 40).
Notation  " x ';;' y " := (spec_seq x y) (right associativity, at level 44). 
Notation  " x '??' y " := (spec_choice x y) (right associativity, at level 45).
Notation  " 'ASSUME' b " := (spec_assume b) (at level 40).
Notation " 'ASSERT' b " := (spec_assert b) (at level 40).
Notation " 'ABORT' " := (spec_abort) (at level 40).  

(**The Low-level Language ***)

(**The expressions and statements for the Low-level Language**)
Definition fid :=  ident.

(**The max number of interrupt handlers**)
Definition INUM := 2%nat.

Definition  hid := nat.

Inductive expr:=
| enull : expr
| evar : var -> expr
| econst32 : int32 -> expr
| eptrconst: addrval -> expr 
| eunop : uop -> expr -> expr
| ebinop : bop -> expr -> expr -> expr
| ederef : expr -> expr
| eaddrof : expr -> expr 
| efield : expr -> ident -> expr
| ecast : expr -> type -> expr
| earrayelem : expr -> expr -> expr.  (* expr1 [ expr2 ] *)

Definition exprlist : Set := list expr.

Inductive prim :=
 | exint : prim
 | switch : var -> prim
 | eoi : int32 -> prim
 | excrit : prim
 | encrit : prim
 | cli : prim
 | sti : prim
 | checkis : var -> prim 
 | stkinit : expr -> expr -> expr -> prim
 | stkfree : expr -> prim.

Inductive stmts :=
 | sskip : option val -> stmts
 | sassign : expr -> expr -> stmts (* expr1 = expr2 *)
 | sif : expr -> stmts -> stmts -> stmts (* if ( expr ) stmts1 else stmts2 *)
 | sifthen:expr->stmts->stmts
 | swhile : expr -> stmts -> stmts
 | sret : stmts
 | srete : expr -> stmts
 | scall : fid -> exprlist -> stmts
 | scalle : expr -> fid -> exprlist -> stmts
 | sseq : stmts -> stmts -> stmts (* right associative *)
 | sprint : expr -> stmts
 | sfexec : fid -> vallist -> typelist -> stmts
 | sfree : freelist -> option val ->  stmts
(*
 | sfreev : freelist -> val -> stmts
*)
 | salloc : vallist -> decllist -> stmts
 | sprim : prim -> stmts

 | hapi_code:spec_code -> stmts .

Open Scope type_scope.

Definition function  :=  (type  *  decllist * decllist *  stmts).

Definition progunit  := fid -> option function.

Definition intunit  := hid -> option stmts.

Definition oscode := (progunit * progunit * intunit).

Definition lprog  := (progunit * oscode).


Inductive cureval:=
|cure : expr -> cureval
(*
|curv : val-> cureval
*)
|curs : stmts -> cureval.
Notation "'SKIP'  " := (curs (sskip None))  (at level 0).

Notation "'[' v ']'" := (curs (sskip (Some v))) (at level 0).

(*Definition of continuation, which is a pair of expression continuation and statement continuation*)
Inductive exprcont:=
| kenil : exprcont
| keop1 : uop -> type -> exprcont -> exprcont
| keop2r : bop -> expr -> type -> type -> exprcont -> exprcont
| keop2l: bop -> val -> type -> type ->exprcont -> exprcont
| kederef : type -> exprcont -> exprcont 
| keoffset: int32 -> exprcont -> exprcont
| kearrbase: expr -> type -> exprcont -> exprcont
| kearrindex: val -> type -> exprcont -> exprcont
| kecast: type -> type -> exprcont -> exprcont.

Inductive stmtcont:=
| kstop : stmtcont
| kseq : stmts -> stmtcont -> stmtcont
| kcall : fid  -> stmts -> env -> stmtcont -> stmtcont
| kint : cureval -> exprcont -> env -> stmtcont -> stmtcont
| kassignr: expr -> type -> stmtcont -> stmtcont
| kassignl : val -> type -> stmtcont -> stmtcont
(*
| kcalle : fid -> exprlist -> type -> stmtcont -> stmtcont
*)
| kfuneval : fid -> vallist -> typelist -> exprlist -> stmtcont -> stmtcont
| kif : stmts -> stmts -> stmtcont -> stmtcont
| kwhile : expr -> stmts -> stmtcont -> stmtcont
| kret :   stmtcont -> stmtcont

| kevent : cureval -> exprcont -> stmtcont -> stmtcont
.

Definition  cont := (exprcont * stmtcont).

Definition code  := (cureval * cont).

Module CodeSpec.
  Definition B:= code.
  Definition holder : B := (curs (sskip None), (kenil, kstop)).
End CodeSpec.

Module TasksMod := MapLib.MapFun tidspec CodeSpec.

Definition tasks :=TasksMod.map.

(* Definition tasksdel := fun (M:tasks) a => TasksMod.minus M (TasksMod.sig a (curs (sskip None),(kenil,kstop))). *)

Program Instance TasksMap: PermMap tid code tasks :=
  {
    usePerm := TasksMod.usePerm;
    isRw := TasksMod.isRw;
    flip := TasksMod.flip;
    sameV := TasksMod.sameV;
    same := TasksMod.same;
    emp := TasksMod.emp;
    join := TasksMod.join;
    del := TasksMod.del;
    get := TasksMod.get;
    set := TasksMod.set;
    sig := TasksMod.sig;
    merge := TasksMod.merge;
    minus := TasksMod.minus;
    map_dec_a := TasksMod.map_dec_a
  }.
Next Obligation.
  apply TasksMod.map_join_emp.
Qed.
Next Obligation.
  apply TasksMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply TasksMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply TasksMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply TasksMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply TasksMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply TasksMod.map_eql; auto.
Qed.
Next Obligation.
  apply TasksMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply TasksMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply TasksMod.map_get_sig.
Qed.
Next Obligation.
  apply TasksMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply TasksMod.map_get_set.
Qed.
Next Obligation.
  apply TasksMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply TasksMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply TasksMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply TasksMod.map_set_emp.
Qed.
Next Obligation.
  apply TasksMod.map_set_sig.
Qed.
Next Obligation.
  apply TasksMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply TasksMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply TasksMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply TasksMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply TasksMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply TasksMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply TasksMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply TasksMod.map_del_sem.
Qed.

Module EnvSpec.
  Definition B:= env.
  Definition holder : B := emp.
End EnvSpec.

Module CltEnvMod:= MapFun tidspec EnvSpec.

Definition cltenvs := CltEnvMod.map.
(* Definition cltenvdel := fun (M:CltEnvMod.map) a => CltEnvMod.minus M (CltEnvMod.sig a emp). *)

Program Instance CMap: PermMap tid env cltenvs :=
  {
    usePerm := CltEnvMod.usePerm;
    isRw := CltEnvMod.isRw;
    flip := CltEnvMod.flip;
    sameV := CltEnvMod.sameV;
    same := CltEnvMod.same;
    emp := CltEnvMod.emp;
    join := CltEnvMod.join;
    del := CltEnvMod.del;
    get := CltEnvMod.get;
    set := CltEnvMod.set;
    sig := CltEnvMod.sig;
    merge := CltEnvMod.merge;
    minus := CltEnvMod.minus;
    map_dec_a := CltEnvMod.map_dec_a
  }.
Next Obligation.
  apply CltEnvMod.map_join_emp.
Qed.
Next Obligation.
  apply CltEnvMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply CltEnvMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply CltEnvMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply CltEnvMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply CltEnvMod.map_eql; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply CltEnvMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply CltEnvMod.map_get_sig.
Qed.
Next Obligation.
  apply CltEnvMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_get_set.
Qed.
Next Obligation.
  apply CltEnvMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply CltEnvMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply CltEnvMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply CltEnvMod.map_set_emp.
Qed.
Next Obligation.
  apply CltEnvMod.map_set_sig.
Qed.
Next Obligation.
  apply CltEnvMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply CltEnvMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply CltEnvMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply CltEnvMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply CltEnvMod.map_del_sem.
Qed.

(**The Low-level World**)
Definition  clientst :=  (env * cltenvs * mem)%type.
(*Interrupt Enable*)
Definition ie := bool.
(**Interrupt Stack**)
Definition is := list hid.
(**Historical values of ie**)
Definition cs := list ie.

Definition localst := (ie * is * cs)%type.

Module LocalStSpec.
  Definition B:= localst.
  Definition holder : B := (true, nil, nil).
End LocalStSpec.

Module TaskLStMod:= MapFun tidspec LocalStSpec.

Definition ltaskstset:= TaskLStMod.map.

(* Definition tasklstdel := fun (M:ltaskstset) a => TaskLStMod.minus M (TaskLStMod.sig a (true,nil,nil)). *)

Program Instance TaskLStMap: PermMap tid localst ltaskstset :=
  {
    usePerm := TaskLStMod.usePerm;
    isRw := TaskLStMod.isRw;
    flip := TaskLStMod.flip;
    sameV := TaskLStMod.sameV;
    same := TaskLStMod.same;
    emp := TaskLStMod.emp;
    join := TaskLStMod.join;
    del := TaskLStMod.del;
    get := TaskLStMod.get;
    set := TaskLStMod.set;
    sig := TaskLStMod.sig;
    merge := TaskLStMod.merge;
    minus := TaskLStMod.minus;
    map_dec_a := TaskLStMod.map_dec_a
  }.
Next Obligation.
  apply TaskLStMod.map_join_emp.
Qed.
Next Obligation.
  apply TaskLStMod.map_join_pos; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_join_comm; auto.
Qed.
Next Obligation.
  eapply TaskLStMod.map_join_assoc; eauto.
Qed.
Next Obligation.
  eapply TaskLStMod.map_join_cancel; eauto.
Qed.
Next Obligation.
  eapply TaskLStMod.map_join_deter; eauto.
Qed.
Next Obligation.
  apply TaskLStMod.map_eql; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_disjoint; auto.
Qed.
Next Obligation.
  eapply TaskLStMod.map_get_unique; eauto.
Qed.
Next Obligation.
  apply TaskLStMod.map_get_sig.
Qed.
Next Obligation.
  apply TaskLStMod.map_get_sig'; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_get_set.
Qed.
Next Obligation.
  apply TaskLStMod.map_get_set'; auto.
Qed.
Next Obligation.
  eapply TaskLStMod.map_join_get_none; eauto.
Qed.
Next Obligation.
  eapply TaskLStMod.map_join_get_some; eauto.
Qed.
Next Obligation.
  apply TaskLStMod.map_set_emp.
Qed.
Next Obligation.
  apply TaskLStMod.map_set_sig.
Qed.
Next Obligation.
  apply TaskLStMod.map_join_set_none; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_join_get_sig; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_merge_sem; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_join_merge; eauto.
Qed.
Next Obligation.
  apply TaskLStMod.map_merge_comm; eauto.
Qed.
Next Obligation.
  apply TaskLStMod.map_minus_sem; auto.
Qed.
Next Obligation.
  apply TaskLStMod.map_join_minus; eauto.
Qed.
Next Obligation.
  apply TaskLStMod.map_del_sem.
Qed.

(*Definition isr register*)
Definition isr :=  hid -> bool.

Definition isrupd (r : isr) (x : hid) (b : bool):= 
      fun (y : hid) => if beq_nat x y then b else r y.


Fixpoint leb_nat (m : nat) : nat -> bool :=
  match m with
  | O => fun _ : nat => true
  | S m' => fun n : nat => match n with
                           | O  => false
                           | S n' =>  leb_nat  m' n'
                           end
  end.

Fixpoint highpri' (r : isr) (n : nat) : hid :=
  match n with
   | O => INUM
   | S n' => let y := highpri' r n' in 
                 if r n' then
                    if (leb_nat  n' y) then n' else y 
                 else y
 end.

Definition highpri (r:isr) := highpri' r INUM.

Definition higherint (r:isr) (i:hid) :=  forall i', Nat.le i' i -> r i' = false. 

Definition empisr := fun (x : hid) => false. 

Definition  osstate  := (clientst * isr * ltaskstset).

Definition  smem  :=  (env * env * mem).

Definition  taskst := (smem *  isr * localst).

Definition get_smem (ts : taskst) :=
      match ts with
      (m, _, _) => m
     end.

Definition  lworld :=  (lprog * tasks * clientst * osstate * tid).


(**The High-level World**)

Definition funtype : Set := prod type typelist.

Definition api_code := vallist -> spec_code.

Definition osapi := prod api_code  funtype.
  
Definition osapispec :=  fid -> option osapi.

Definition int_code := spec_code.

Definition osintspec := hid -> option int_code.

Definition ossched := osabst -> tid -> Prop.

Definition osspec := (osapispec * osintspec * ossched).

Definition hprog := (progunit * osspec). 

Definition hworld := (hprog * tasks * clientst * osabst ). 

Definition isrdy (st:taskstatus):=
  match st with
    | rdy => True
    | _ => False
  end.

Definition eqenv (o o': taskst) : Prop :=
     match o, o' with
          | (G,E,M,isr,aux),(G',E',M',isr',aux') => G =G' /\ E = E' 
      end.

