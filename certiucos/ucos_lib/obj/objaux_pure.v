
Require Import os_code_defs.
Require Import code_notations.
Require Import os_inv.
Require Import inv_prop.
Require Import pure_lib.
Require Import OSTimeTickPure.
Require Import seplog_tactics.
Require Import objauxvar_lemmas.
Require Import seplog_lemmas.

Require Import join_lib. 

Open Scope int_scope. 
Open Scope code_scope.

Definition tsk_loc_ptr (locmp: AuxLocMod.map) (ptrmp: AuxPtrMod.map) t vloc sid :=
  get locmp t = Some (V$ vloc) /\
    get ptrmp t = Some (Vptr sid).


Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by (clear; tauto); 
  destruct h as [Ht | Hf].

Lemma obj_aux_cre: 
  forall t locmp ptrmp ecbls fecbh fecbvl objs ptr, 
    OBJ_AUX_P locmp ptrmp ecbls fecbh fecbvl objs ->
    get locmp t = Some (V$ __Loc_objcre) ->
    get ptrmp t = Some (Vptr ptr) ->
    (~ ptr_in_ecblist (Vptr ptr) fecbh fecbvl /\
     ~ obj_ref objs ptr /\ is_kobj ecbls ptr). 
Proof.
  introv Hmep Hgetl Hgetp.
  unfold OBJ_AUX_P in Hmep.
  lets H00: Hmep Hgetp. clear Hmep.
  destruct H00.
  destructs H.
  splits; auto.
  destruct H.
  destructs H. rewrite Hgetl in H. inverts H.
  destructs H. rewrite Hgetl in H. inverts H.
Qed.

Lemma obj_aux_nml: 
  forall locmp ptrmp els fecbh fecbvl objs ptr ct, 
    OBJ_AUX_P locmp ptrmp els fecbh fecbvl objs ->
    get ptrmp ct = Some (Vptr ptr) ->
    get locmp ct = Some (V$ os_code_defs.__Loc_normal) ->
    (is_kobj els ptr \/ ptr_in_ecblist (Vptr ptr) fecbh fecbvl).
Proof.
  introv Hop Hgetp Hgetl.
  unfold OBJ_AUX_P in Hop.
  lets H00: Hop Hgetp.
  clear Hop.
  destruct H00 as [Hcre | [Hnml | Hdel]]; simpljoin1.
  rewrite Hgetl in H.
  tryfalse.
  auto.
  rewrite Hgetl in H.
  tryfalse.
Qed.

Lemma obj_aux_del: 
  forall locmp ptrmp ecbls fecbh fecbvl objs t ptr, 
    OBJ_AUX_P locmp ptrmp ecbls fecbh fecbvl objs ->
    tsk_loc_ptr locmp ptrmp t __Loc_objdel ptr ->
    (is_kobj ecbls ptr /\
     ~ (exists t0,
           get locmp t0 = Some (V$ __Loc_objcre) /\
            get ptrmp t0 = Some (Vptr ptr)) /\
     ~ obj_ref objs ptr). 
Proof.
  introv Hop Htlp.
  unfold tsk_loc_ptr in Htlp.
  destruct Htlp as (Hgetl & Hgetp).
  unfold OBJ_AUX_P in Hop.
  lets H00: Hop Hgetp.
  rewrite Hgetl in H00.
  destruct H00.
  simpljoin1. tryfalse.
  destruct H. 
  simpljoin1. tryfalse.
  simpljoin1.
  splits; auto.
Qed.

Lemma n_ptr_in_ecblist_tail: 
  forall eptr sid p vl vll, 
    ~ ptr_in_ecblist (Vptr eptr) (Vptr sid) (vl :: vll) ->
    V_OSEventListPtr vl = Some (Vptr p) -> 
    ~ ptr_in_ecblist (Vptr eptr) (Vptr p) vll. 
Proof.
  introv Hnin Hnxtp Hin.
  apply Hnin.
  unfold ptr_in_ecblist.
  unfold ptr_in_ecblist in Hin.
  unfold ptr_in_ecbsllseg; fold ptr_in_ecbsllseg.
  destruct (beq_val (Vptr eptr) (Vptr sid)) eqn: E.
  auto.
  rewrite Hnxtp.
  auto.
Qed.

Lemma ptr_in_ecblist_tail: 
  forall eptr sid hd' vl vll, 
    ptr_in_ecblist (Vptr eptr) (Vptr sid) (vl :: vll) ->
    eptr <> sid ->
    V_OSEventListPtr vl = Some hd' -> 
    isptr hd' -> 
    ptr_in_ecblist (Vptr eptr) hd' vll. 
Proof.
  introv Hin Hneq Hnxt Hisptr.
  unfold ptr_in_ecblist in *.
  unfold ptr_in_ecbsllseg in Hin.
  fold ptr_in_ecbsllseg in Hin.
  assert (Hfalse: beq_val (Vptr eptr) (Vptr sid) = false).
  {
    unfold beq_val. unfold os_inv.beq_addrval.
    destruct eptr. destruct sid.
    destruct (beq_pos b b0) eqn: E1;
      destruct (Int.eq i i0) eqn: E2;
      simpl; auto.
    assert (b = b0). 
    { rewrite beq_pos_Pos_eqb_eq in E1. rewrite Pos.eqb_eq in E1. auto. }
    assert (i = i0).
    {
      lets H00: Int.eq_spec.
      specialize (H00 i i0).
      rewrite E2 in H00.
      auto.
    }
    subst.
    false.
  } 
  rewrite Hfalse in Hin.
  rewrite Hnxt in Hin.
  auto.
Qed.

Lemma not_in_els_notcre_:
  forall locmp ptrmp ecbls fecbh fecbvl objs a vp t,
    OBJ_AUX_P locmp ptrmp ecbls fecbh fecbvl objs ->
    get ecbls a = None ->
    get locmp t = Some (Vint32 (Int.repr __Loc_objcre)) ->
    get ptrmp t = Some (vp) ->
    vp <> Vptr a.
Proof.
  introv Hop Hnone Hgetl Hgetp.
  intro Hf.
  subst vp.
  lets H00: obj_aux_cre Hop Hgetl Hgetp.
  destruct H00. unfold is_kobj in H0.
  simpljoin1.
  unfold get in H1, Hnone.
  unfold EcbMap in H1,Hnone.
  rewrite H1 in Hnone; inverts Hnone.
Qed.

Lemma not_in_els_notcre:
  forall locmp ptrmp ecbls fecbh fecbvl objs a,
    OBJ_AUX_P locmp ptrmp ecbls fecbh fecbvl objs ->
    get ecbls a = None ->
    ~exists t, tsk_loc_ptr locmp ptrmp t __Loc_objcre a.
Proof.
  introv Hop Hnone Hex.
  destruct Hex as (t & Htlp).
  unfold tsk_loc_ptr in Htlp.
  destruct Htlp as (Hcre & Hptr).
  eapply not_in_els_notcre_; eauto.
Qed.

Lemma not_in_els_notdel: 
  forall locmp ptrmp ecbls fecbh fecbvl objs a, 
    OBJ_AUX_P locmp ptrmp ecbls fecbh fecbvl objs ->
    get ecbls a = None ->
    ~exists t, tsk_loc_ptr locmp ptrmp t __Loc_objdel a.
Proof.
  introv Hop Hnone Hex.
  destruct Hex as (t & Htlp).
  unfold tsk_loc_ptr in Htlp.
  destruct Htlp as (Hdel & Hptr).
  lets H00: Hop Hptr.
  rewrite Hdel in H00.
  inverts H00.
  simpljoin1. tryfalse.
  inverts H. simpljoin1. tryfalse.
  simpljoin1.
  destruct H0 as (n & wls & Hf).
  unfold get in Hf, Hnone.
  unfold EcbMap in Hf,Hnone.
  rewrite Hf in Hnone; inverts Hnone.
Qed.

Lemma inactive_ecb_no_obj_ref: 
  forall ptr ecbls objs, 
    get ecbls ptr = None -> 
    RH_OBJ_ECB_P ecbls objs -> 
    ~ obj_ref objs ptr.
Proof. 
  introv Hnone Hobj Href.
  unfold obj_ref in Href.
  destruct Href as ( idx & attr & Hget).
  unfold RH_OBJ_ECB_P in Hobj.
  apply Hobj in Hget.
   rewrite Hnone in Hget. simpljoin1. tryfalse.
Qed.


(*************** lemmas for  the use of kernel objects *****************)

Lemma objdel_nodup_normal_ptr_preserve: 
  forall locmp ptrmp tid sid, 
    objdel_nodup locmp ptrmp ->
    get locmp tid = Some (V$ __Loc_normal) -> 
    get ptrmp tid = Some (Vnull) -> 
    objdel_nodup locmp (set ptrmp tid (Vptr sid)). 
Proof.
  introv Hnd Hgetl Hgetp.
  unfold objdel_nodup in *.
  introv Hneq Hgetl1 Hgetl2 Hptr1 Hptr2.
  casetac t1 tid Ht Hf.
  subst.
  rewrite Hgetl in Hgetl1. tryfalse.
  rewrite set_a_get_a' in Hptr1; eauto.
  casetac t2 tid Ht' Hf'.
  subst.
  rewrite Hgetl in Hgetl2. tryfalse.
  rewrite set_a_get_a' in Hptr2; eauto.
Qed.

Lemma objcre_nodup_normal_semptr_preserve: 
  forall locmp ptrmp tid sid, 
    objcre_nodup locmp ptrmp ->
    get locmp tid = Some (V$ __Loc_normal) -> 
    get ptrmp tid = Some (Vnull) -> 
    objcre_nodup locmp (set ptrmp tid (Vptr sid)). 
Proof.
  introv Hnd Hgetl Hgetp.
  unfold objcre_nodup in *.
  introv Hneq Hgetl1 Hgetl2 Hptr1 Hptr2.
  casetac t1 tid Ht Hf.
  subst.
  rewrite Hgetl in Hgetl1. tryfalse.
  rewrite set_a_get_a' in Hptr1; eauto.
  casetac t2 tid Ht' Hf'.
  subst.
  rewrite Hgetl in Hgetl2. tryfalse.
  rewrite set_a_get_a' in Hptr2; eauto.
Qed.

Lemma obj_aux_p_ptr_normal_preserve: 
  forall locmp ptrmp els fecbh fecbvl objs ptr tid, 
    OBJ_AUX_P locmp ptrmp els fecbh fecbvl objs ->
    get locmp tid = Some (V$ __Loc_normal) -> 
    get ptrmp tid = Some (Vnull) ->
    is_kobj els ptr ->
    OBJ_AUX_P locmp (set ptrmp tid (Vptr ptr)) els fecbh fecbvl objs. 
Proof.
  introv Hop Hgetl Hgetp Hobj.
  unfold OBJ_AUX_P in *.
  introv Hgetp'.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
    right. left.
    splits; auto.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    eapply Hop in Hgetp'.
    destruct Hgetp'; auto.
    destruct H; auto.
    right. right.
    simpljoin.
    splits; auto.
    introv Hc.
    simpljoin.
    casetac tid x Ht1 Hf1.
    subst.
    rewrite set_a_get_a in H4; inverts H4.
    rewrite Hgetl in H3; tryfalse.
    rewrite set_a_get_a' in H4; eauto.
Qed.

Lemma objdel_nodup_set_null_preserve:  
  forall locmp ptrmp tid, 
    objdel_nodup locmp ptrmp ->
    objdel_nodup locmp (set ptrmp tid (Vnull)). 
Proof.
  introv Hnd.
  unfold objdel_nodup in *.
  introv Hne Hgetl1 Hgetl2 Het1 Het2.
  casetac t1 tid Ht Hf.
  subst.
  rewrite set_a_get_a in Het1.
  simpljoin1; tryfalse.
  rewrite set_a_get_a' in Het1; eauto.
  casetac t2 tid Ht' Hf'.
  subst.
  rewrite set_a_get_a in Het2. 
  simpljoin1; tryfalse.
  rewrite set_a_get_a' in Het2; eauto.
Qed.

Lemma objcre_nodup_set_null_preserve:   
  forall locmp ptrmp tid, 
    objcre_nodup locmp ptrmp ->
    objcre_nodup locmp (set ptrmp tid (Vnull)). 
Proof.
  introv Hnd.
  unfold objcre_nodup in *.
  introv Hne Hgetl1 Hgetl2 Het1 Het2.
  casetac t1 tid Ht Hf.
  subst.
  rewrite set_a_get_a in Het1.
  simpljoin1; tryfalse.
  rewrite set_a_get_a' in Het1; eauto.
  casetac t2 tid Ht' Hf'.
  subst.
  rewrite set_a_get_a in Het2. 
  simpljoin1; tryfalse.
  rewrite set_a_get_a' in Het2; eauto.
Qed.

Lemma obj_aux_p_set_null_preserve: 
  forall locmp ptrmp els fecbh fecbvl objs tid, 
    OBJ_AUX_P locmp ptrmp els fecbh fecbvl objs ->
    OBJ_AUX_P locmp (set ptrmp tid (Vnull)) els fecbh fecbvl objs. 
Proof.
  introv Hop.
  unfold OBJ_AUX_P in *.
  introv Hgetp.
  casetac tid t Ht Hf.
  -
    subst.
    rewrite set_a_get_a in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a' in Hgetp; eauto.
    eapply Hop in Hgetp.
    destruct Hgetp; auto.
    destruct H; auto.
    right. right.
    simpljoin.
    splits; auto.
    introv Hc.
    simpljoin.
    casetac tid x Ht1 Hf1.
    subst.
    rewrite set_a_get_a in H4; inverts H4.
    rewrite set_a_get_a' in H4; eauto.
Qed.

(* Require Import seplog_lemmas. *)

Ltac mytac :=
  heat; jeauto2.

Require Import ifun_spec.
Require Import seplog_pattern_tacs.

Lemma llsegobjaux_set_node : 
  forall vltcb vltcb' p s P head vl vl' locmp ptrmp,
    s |= llsegobjaux head Vnull vltcb locmp ptrmp V_OSTCBNext ** P -> 
    tcblist_get p head vltcb = Some vl -> 
    set_node p vl' head vltcb = vltcb' -> 
    same_prev_next vl vl' -> 
    s |= llsegobjaux head Vnull vltcb' locmp ptrmp V_OSTCBNext ** P. 
Proof.
  inductions vltcb.
  -
    intros.
    unfold llsegobjaux in H.
    destruct vltcb'.
    unfold llsegobjaux. sep auto.
    simpl in H1.
    inverts H1.
  -
    introv Hsat Htg Hsn Hspn.
    unfold llsegobjaux in Hsat.
    fold llsegobjaux in Hsat.
    sep normal in Hsat.
    sep destruct Hsat.
    sep split in Hsat.
    simpl in Hsn.
    destruct (beq_val p head) eqn: E.
    +
      subst vltcb'.
      unfold tcblist_get in Htg.
      rewrite E in Htg. inverts Htg. 
      unfold llsegobjaux; fold llsegobjaux.
      sep normal.
      exists x x0 x1 x2. do 2 eexists.
      sep split; eauto.
      unfolds in Hspn. 
      rewrite H0 in Hspn.
      destruct (V_OSTCBNext vl').
      simpljoin1.
      tryfalse.
    +
      destruct a.
      unfold V_OSTCBNext in H0. simpl in H0. inverts H0.
      rewrite <- Hsn.
      unfold llsegobjaux; fold llsegobjaux.
      unfolds in H0. simpl in H0. inverts H0.
      sep normal. sep eexists. 
      sep cancel objaux_node.
      sep_lifts_trms llsegobjaux.
      eapply IHvltcb; eauto.
      sep cancel llsegobjaux. 
      sep split; eauto.
      simpl in Htg. rewrite E in Htg.
      auto.
Qed.

(* used for servel objects create *)

Lemma objref_distinct_null_holder_preserve: 
  forall attr idx objs, 
    objref_distinct objs ->
    get objs idx = Some (objnull, attr) -> 
    objref_distinct (set objs idx (objholder, attr)).
Proof.
  introv Hed Hget.
  unfold objref_distinct in *.
  introv Hget1 Hget2.
  specialize (Hed ptr).
   casetac idx idx1 Heq1 Hneq1.
  subst. rewrite set_a_get_a in Hget1. inverts Hget1.
  casetac idx idx2 Heq2 Hneq2.
  subst. rewrite set_a_get_a in Hget2. inverts Hget2.
  rewrite set_a_get_a' in Hget1; eauto.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma OBJ_AUX_P_null_holder_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl objs idx attr,
    OBJ_AUX_P locmp ptrmp ecbls fecbh fecbvl objs ->
    get objs idx = Some (objnull, attr) ->
    OBJ_AUX_P locmp ptrmp ecbls fecbh fecbvl (set objs idx (objholder, attr))  .
Proof.
  introv Hop Hget.
  unfold OBJ_AUX_P in *.
  introv Hptr.
  lets H00: Hop Hptr. clear Hop.
  destruct H00.
  - 
    left.
    simpljoin1.
    splits; auto.
    introv Href. apply H1.
    unfold obj_ref in *.
    destruct Href as (idx0 & att & Href).
    casetac idx idx0 Heq Hneq.
    subst. rewrite set_a_get_a in Href. inverts Href.
    rewrite set_a_get_a' in Href; eauto.
  -
    destruct H.
    +
      right; left.
      simpljoin1.
      splits; auto.
    +
      simpljoin1.
      right. right.
      splits; auto.
      introv Href. apply H2.
      unfold obj_ref in *.
      destruct Href as (idx0 & att & Href).
      casetac idx idx0 Heq Hneq.
      subst. rewrite set_a_get_a in Href. inverts Href.
      rewrite set_a_get_a' in Href; eauto.
Qed.

Lemma objref_objnull_preserve:
  forall objs idx attr ptr, 
    obj_ref (set objs idx (objnull, attr)) ptr -> 
    obj_ref objs ptr. 
Proof.
  introv Her.
  unfold obj_ref in *.
  destruct Her.
  simpljoin.
  casetac idx x Heq Hneq.
  subst. rewrite set_a_get_a in H. inverts H.
  rewrite set_a_get_a' in H; eauto.
Qed.

Lemma obj_aux_p_objnull_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl objs idx attr tid, 
    OBJ_AUX_P locmp ptrmp ecbls fecbh fecbvl objs ->
    get ptrmp tid = Some (Vnull) -> 
    OBJ_AUX_P (set locmp tid (V$ __Loc_normal)) ptrmp ecbls fecbh fecbvl
              (set objs idx (objnull, attr)).
Proof.
  introv Hop.
  unfold OBJ_AUX_P in *.
  introv Hnull Hgetp.
  casetac tid t Heq Hneq.
  -
    subst.
    rewrite Hnull in Hgetp.
    inverts Hgetp.
  -
    rewrite set_a_get_a'; eauto.
    clear Hnull.
    lets H00: Hop Hgetp.
    destruct H00.
    left.
    simpljoin1. splits; auto.
    introv Hf. apply H1.
    eapply objref_objnull_preserve; eauto.

    destruct H.
    right. left.
    simpljoin1.
    splits; auto.

    right. right.
    simpljoin1.
    splits; auto.
    introv Hf.
    simpljoin.
    apply H1.
    casetac tid x Ht1 Hf1.
    subst.
    rewrite set_a_get_a in H3; inverts H3.
    rewrite set_a_get_a' in H3; eauto.
    introv Hf. apply H2.
    eapply objref_objnull_preserve; eauto.
Qed.

Lemma objref_distinct_objnull_preserve: 
  forall objs idx attr, 
    objref_distinct objs ->
    objref_distinct (set objs idx (objnull, attr))  .
Proof.
  introv Hed.
  unfold objref_distinct in *.
  introv Hget1 Hget2.
  specialize (Hed ptr).
  casetac idx idx1 Heq1 Hneq1.
  subst. rewrite set_a_get_a in Hget1. inverts Hget1.
  casetac idx idx2 Heq2 Hneq2.
  subst. rewrite set_a_get_a in Hget2. inverts Hget2.
  rewrite set_a_get_a' in Hget1; eauto.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma objref_distinct_noref_ptr_preserve: 
  forall objs ptr idx attr,
    objref_distinct objs ->  
    ~ obj_ref objs ptr -> 
    objref_distinct (set objs idx (objid ptr, attr))  .
Proof.
  introv Hed Hnref.
  unfold objref_distinct in *.
  introv Hget1 Hget2.
  unfold obj_ref in Hnref.
  casetac idx idx1 Heq1 Hneq1.
  subst. rewrite set_a_get_a in Hget1. inverts Hget1.
  casetac idx1 idx2 Heq2 Hneq2.
  subst. auto. rewrite set_a_get_a' in Hget2; eauto.
  false. eapply Hnref; eauto.
  rewrite set_a_get_a' in Hget1; eauto.
  casetac idx idx2 Heq2 Hneq2.
  subst. rewrite set_a_get_a in Hget2; inverts Hget2.
  false. eapply Hnref; eauto.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma objcre_nodup_cre_cre_contra: 
  forall t tid ptr locmp ptrmp, 
    objcre_nodup locmp ptrmp -> 
    t <> tid -> 
    tsk_loc_ptr locmp ptrmp t __Loc_objcre ptr ->
    get locmp tid = Some (V$ __Loc_objcre) ->
    get ptrmp tid = Some (Vptr ptr) ->  
    False.
Proof.
  introv Hcrendp Htne Htlp Hgetl Hgetp.
  unfold tsk_loc_ptr in Htlp.
  destruct Htlp as (Hgetl' & Hgetp').
  unfold objcre_nodup in Hcrendp.
  eapply Hcrendp in Hgetp; eauto.
Qed.

Lemma objdel_del_del_contra:
  forall t tid ptr locmp ptrmp, 
    objdel_nodup locmp ptrmp -> 
    t <> tid -> 
    tsk_loc_ptr locmp ptrmp t __Loc_objdel ptr ->
    get locmp tid = Some (V$ __Loc_objdel) ->
    get ptrmp tid = Some (Vptr ptr) ->  
    False.
Proof.
  introv Hdelndp Htne Htlp Hgetl Hgetp.
  unfold tsk_loc_ptr in Htlp.
  destruct Htlp as (Hgetl' & Hgetp').
  unfold objdel_nodup in Hdelndp.
  eapply Hdelndp in Hgetp; eauto.
Qed.

Lemma n_objref_diff_ptr_preserve: 
  forall objs eptr ptr idx attr, 
    ~ obj_ref objs eptr ->
    eptr <> ptr ->
    ~ obj_ref (set objs idx (objid ptr, attr))   eptr. 
Proof.
  introv Hnref Hneq Href.
  apply Hnref.
  unfold obj_ref in *.
  simpljoin.
  casetac idx x He Hne.
  subst. rewrite set_a_get_a in H. inverts H.
  tryfalse.
  rewrite set_a_get_a' in H; eauto. 
Qed.

(* Lemma OBJ_AUX_P_normal_null_preserve: 
  forall locmp ptrmp ecbls fecbh fecbvl objs tid ptr idx attr,
    OBJ_AUX_P locmp ptrmp ecbls fecbh fecbvl objs ->
    ~(exists t, t <> tid /\ tsk_loc_ptr locmp ptrmp t __Loc_objcre ptr) -> 
    OBJ_AUX_P (set locmp tid (V$ __Loc_normal)) (set ptrmp tid (Vnull)) ecbls
              fecbh fecbvl (set objs idx (objid ptr, attr))  .
Proof.
  introv Hop Hncre.
  unfold OBJ_AUX_P in *.
  introv Hgetp'.
  casetac tid t Hteq Htne.
  -
    subst.
    rewrite set_a_get_a in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hop Hgetp'.
    clear Hop.
    rewrite set_a_get_a'; eauto.
    destruct H00.
    +
      destruct H as (Hgetl & Hnin & Hnref & Hnone).
      left. splits; auto.
      casetac ptr ptr0 He Hne.
      *
        subst.
        false.
        apply Hncre.
        exists t. splits; auto.
        unfold tsk_loc_ptr. splits; auto.
     * eapply n_objref_diff_ptr_preserve; eauto.
    +
      destruct H.
      auto.
      destruct H as (Hgetl & Hnin & Hnref & Hnone).
      right. right.
      splits; auto.
      introv Hf.
      simpljoin.
      eapply Hnref.
      casetac tid x He Hne.
      subst.
      rewrite set_a_get_a in H; inverts H.
      rewrite set_a_get_a' in H; eauto.
      rewrite set_a_get_a' in H0; eauto.
      casetac ptr ptr0 He Hne.
      *
        subst.
(*         false.
        apply Hncre.
        exists t. splits; auto.
        unfold tsk_loc_ptr. splits; auto.
     * eapply n_objref_diff_ptr_preserve; eauto.
        casetac eptr eid He Hne.
        subst.
        false.
        apply Hncre2.
        exists t. splits; auto.
        unfold tsk_loc_ptr. splits; auto. do 3 eexists; eauto.

        right. left.
        splits; auto.
        eapply n_eibref_diff_ptr_preserve; eauto.
        unfold is_kobj. eauto.
      *
        destruct H as (Hgetl & Hor2).
        right; right.
        splits; auto. *)
Qed. *)

Lemma objref_distinct_set_idx_attr: 
  forall objs idx e attr attr', 
    objref_distinct objs ->
    get objs idx = Some (e, attr) -> 
    objref_distinct (set objs idx (e, attr'))  . 
Proof.
  introv Hed Hget.
  unfold objref_distinct in *.
  introv Hget1 Hget2.
  casetac idx idx1 Ht Hf.
  subst. rewrite set_a_get_a in Hget1. inverts Hget1.
  casetac idx1 idx2 Ht' Hf'.
  subst. auto.
  rewrite set_a_get_a' in Hget2; eauto.
  rewrite set_a_get_a' in Hget1; eauto.
  casetac idx idx2 Ht' Hf'.
  subst.
  rewrite set_a_get_a in Hget2.
  inverts Hget2.
  eapply Hed; eauto.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma n_objref_set_attr_preserve: 
  forall objs ptr idx e attr attr', 
    ~ obj_ref objs ptr -> 
    get objs idx = Some (e, attr) ->
    ~ obj_ref (set objs idx (e, attr'))  ptr.
Proof.
  introv Hnr Hget.
  introv Hf. apply Hnr.
  unfold obj_ref in Hf. unfold obj_ref.
  simpljoin.
  casetac idx x Ht Hf.
  subst. rewrite set_a_get_a in H. inverts H.
  do 2 eexists; eauto.
  rewrite set_a_get_a' in H; eauto.
Qed.

Lemma OBJ_AUX_P_set_attr_preserve:  
  forall locmp ptrmp ecbls fecbh fecbvl objs idx e attr attr', 
    OBJ_AUX_P locmp ptrmp ecbls fecbh fecbvl objs ->
    get objs idx = Some (e, attr) -> 
    OBJ_AUX_P locmp ptrmp ecbls fecbh fecbvl (set objs idx (e, attr'))  .
Proof.
  introv Hop Hget.
  unfold OBJ_AUX_P in *.
  introv Hget'.
  lets H00: Hop Hget'. clear Hop.
  destruct H00.
  left.
  simpljoin1. splits; auto.
  eapply n_objref_set_attr_preserve; eauto.
  destruct H.
  simpljoin1.
  right; left.
  splits; auto.
  simpljoin1.
  right; right.
  splits; eauto.
  eapply n_objref_set_attr_preserve; eauto.
Qed.

Lemma objref_distinct_del_preserve: 
  forall objs idx attr, 
    objref_distinct objs -> 
    objref_distinct (set objs idx (objnull, attr))  . 
Proof.
  introv Hed.
  unfold objref_distinct in *.
  introv Hget1 Hget2.
  casetac idx idx1 Ht Hf.
  subst. rewrite set_a_get_a in Hget1. inverts Hget1.
  rewrite set_a_get_a' in Hget1; eauto.
  casetac idx idx2 Ht' Hf'.
  subst.
  rewrite set_a_get_a in Hget2.
  inverts Hget2.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma obj_ref_del_preserve: 
  forall idx attr objs ptr, 
    obj_ref (set objs idx (objnull, attr)) ptr -> 
    obj_ref objs ptr.
Proof.
  introv Her.
  unfold obj_ref in *.
  simpljoin1.
  casetac idx x Ht Hf.
  subst.
  rewrite set_a_get_a in H. inverts H.
  rewrite set_a_get_a' in H; eauto.
Qed.


Local Open Scope list_scope.

Lemma objdel_nodup_cre_preserve: 
  forall locmp ptrmp ct ptr,
    objdel_nodup locmp ptrmp ->
    objdel_nodup (set locmp ct (V$ __Loc_objcre)) (set ptrmp ct (Vptr ptr)). 
Proof.
  introv Hdnp.
  unfold objdel_nodup in*.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hget1.
  inverts Hget1.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hget2.
  inverts Hget2.
  rewrite set_a_get_a' in Hget1, Hget2; eauto.
  rewrite set_a_get_a' in Hp1, Hp2; eauto.
Qed.

Lemma objcre_nodup_cre_preserve: 
  forall locmp ptrmp ct ptr,
    objcre_nodup locmp ptrmp ->
    (~exists t, tsk_loc_ptr locmp ptrmp t __Loc_objcre ptr) -> 
    objcre_nodup (set locmp ct (V$ __Loc_objcre)) (set ptrmp ct (Vptr ptr)). 
Proof.
  introv Hdnp Hnex1.
  unfold objcre_nodup in*.
  unfold tsk_loc_ptr in *.
  introv Hneqt Hget1 Hget2 Hp1 Hp2.
  assert (Hor1: t1 = ct \/ t1 <> ct) by tauto.
  destruct Hor1.
  subst t1.
  rewrite set_a_get_a in Hp1.
  inverts Hp1.
  assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  tryfalse.
  rewrite set_a_get_a' in Hp2; eauto.
  rewrite set_a_get_a' in Hget2; eauto.
  introv Heq.
  subst.
  eapply Hnex1; eauto.
  rewrite set_a_get_a' in Hp1; eauto.
  rewrite set_a_get_a' in Hget1; eauto.
   assert (Hor2: t2 = ct \/ t2 <> ct) by tauto.
  destruct Hor2.
  subst t2.
  rewrite set_a_get_a in Hp2; inverts Hp2.
  intros Heq.
  subst.
  eapply Hnex1; eauto.
  rewrite set_a_get_a' in Hp2; eauto.
  rewrite set_a_get_a' in Hget2; eauto.
Qed.

Lemma obj_aux_cre_preserve: 
  forall locmp ptrmp ecbls ct n ptr objs hd' vl vll,
    OBJ_AUX_P locmp ptrmp ecbls (Vptr ptr) (vl::vll) objs ->  
    get ptrmp ct = Some Vnull -> 
    get ecbls ptr = None ->  
    RH_OBJ_ECB_P ecbls objs -> 
    V_OSEventListPtr vl = Some hd' -> 
    isptr hd' ->
    ~ptr_in_ecblist (Vptr ptr) hd' vll -> 
    ~(exists t, t <> ct /\ tsk_loc_ptr locmp ptrmp t __Loc_objcre ptr) -> 
    ~(exists t, t <> ct /\ tsk_loc_ptr locmp ptrmp t __Loc_objdel ptr) -> 
    OBJ_AUX_P (set locmp ct (V$ __Loc_objcre)) (set ptrmp ct (Vptr ptr)) (set ecbls ptr (abssem n, nil)) hd' vll objs.
Proof.
  introv Hop Hgetp Hnone Hobj Hvp Hhd Hnptr Hnex Hnex2.
  unfold OBJ_AUX_P in *.
  introv Hgetp'.
  assert (Hor: t = ct \/ t <> ct) by tauto.
  destruct Hor.
  - (* t = ct *)
    subst t.
    rewrite set_a_get_a in Hgetp'; inverts Hgetp'.
    left.
    splits; auto.
    rewrite set_a_get_a. auto.
    eapply inactive_ecb_no_obj_ref; eauto.
    unfold is_kobj.
    do 2 eexists.
    rewrite set_a_get_a. eauto. 
  - (* t <> ct *)
    rewrite set_a_get_a' in Hgetp'; eauto.
    lets H00: Hop Hgetp'.
    clear Hop.
    destruct H00.
    + 
      left.
      simpljoin1. splits; auto.
      rewrite set_a_get_a'; auto.
      destruct Hhd; simpljoin.
      introv Hf. unfold ptr_in_ecblist in Hf. destruct vll; tryfalse.
      eapply n_ptr_in_ecblist_tail; eauto.
      assert (Hor': ptr = ptr0 \/ ptr <> ptr0) by tauto.
      destruct Hor'.
      subst.  unfold is_kobj. rewrite set_a_get_a. do 2 eexists; eauto.
      unfold is_kobj. rewrite set_a_get_a'; eauto. 
    +
      destruct H0. 
      right. left.
      simpljoin1.
      splits; auto.
      rewrite set_a_get_a'; auto.
      assert (Hor': ptr = ptr0 \/ ptr <> ptr0) by tauto.
      destruct Hor'.
      left.
      subst.  unfold is_kobj. rewrite set_a_get_a. do 2 eexists; eauto.
      destruct H1.
      left.
      unfold is_kobj. rewrite set_a_get_a'; eauto.
      right.
      simpl in H1.
      destruct (os_inv.beq_addrval ptr0 ptr) eqn:eq1.
      eapply beq_tid_true_eq in eq1; subst. tryfalse.
      rewrite Hvp in H1. auto.

      right. right.
      simpljoin1.
      splits; auto.
      rewrite set_a_get_a'; auto.
      assert (Hor': ptr = ptr0 \/ ptr <> ptr0) by tauto.
      destruct Hor'.
      subst.  unfold is_kobj. rewrite set_a_get_a. do 2 eexists; eauto.
      unfold is_kobj. rewrite set_a_get_a'; eauto.
      introv Hf.
      simpljoin.
      assert (Hor': x = ct \/ x <> ct) by tauto.
      destruct Hor'.
      subst.
      rewrite set_a_get_a in H5; inverts H5.
      unfold tsk_loc_ptr in *.
      eapply Hnex2; eauto.
      rewrite set_a_get_a' in H4, H5; eauto.
Qed.

Lemma obj_aux_p_cre_preserve' :
forall locmp ptrmp ecbls fecbh fecbvl objs ct idx ptr att',
 ~(exists t, t <> ct /\ tsk_loc_ptr locmp ptrmp t __Loc_objdel ptr) -> 
 ~(exists t, t <> ct /\ tsk_loc_ptr locmp ptrmp t __Loc_objcre ptr) -> 
OBJ_AUX_P locmp ptrmp ecbls fecbh fecbvl objs ->
OBJ_AUX_P (set locmp ct (V$ __Loc_normal)) (set ptrmp ct Vnull) ecbls fecbh fecbvl (set objs idx (objid ptr, att')).
Proof.
unfold OBJ_AUX_P.
introv Hdel Hcre Hop.
introv Hgetp.
casetac t ct Heqt Hneqt.
  * subst.
     rewrite set_a_get_a in *. tryfalse.
  * rewrite set_a_get_a' in *; eauto.
     lets H00: Hop Hgetp.
     clear Hop.
     destruct H00.
     simpljoin. left.
     splits; auto.
     casetac ptr ptr0 Heq Hneq.
     subst.
     unfold tsk_loc_ptr in *.
     false. eapply Hcre; eauto.
     eapply n_objref_diff_ptr_preserve; eauto.
     destruct H.
     auto.
     simpljoin.
     right. right.
     splits; auto.
     introv Hf. simpljoin.
     casetac x ct Heqt0 Hneqt0.
     subst.
     rewrite set_a_get_a in *. tryfalse.
     rewrite set_a_get_a' in *; eauto.
     casetac ptr ptr0 Heq Hneq.
     subst.
      unfold tsk_loc_ptr in *.
     false. eapply Hdel; eauto.
     eapply n_objref_diff_ptr_preserve; eauto.
Qed.

Lemma obj_aux_p_del_preserve': 
  forall locmp ptrmp els els' fecbh fecbvl objs ct i1 eptr etbl ptr pegrp petbl wls,
    OBJ_AUX_P locmp ptrmp els fecbh fecbvl objs ->
    isptr fecbh ->
    get ptrmp ct = Some (Vptr ptr) ->
    ~ (exists t', tsk_loc_ptr locmp ptrmp t' __Loc_objcre ptr) ->
    ~ (exists t', t' <> ct /\ tsk_loc_ptr locmp ptrmp t' __Loc_objdel ptr) -> 
    join els' (sig ptr (abssem i1, wls)) els -> 
    OBJ_AUX_P locmp (set ptrmp ct Vnull) els' (Vptr ptr)
              ((V$ OS_EVENT_TYPE_UNUSED :: Vint32 Int.zero :: Vint32 i1 :: eptr :: etbl :: fecbh :: pegrp :: petbl :: nil) :: fecbvl)
              objs.
Proof.
  introv Hop Hisptr Hgetp Hncre Hndel Hjo.
  unfold OBJ_AUX_P in Hop.
  unfold OBJ_AUX_P.
  introv Hgetp'.
  casetac t ct Heqt Hneqt.
  * subst.
     rewrite set_a_get_a in Hgetp'; inverts Hgetp'.
  * rewrite set_a_get_a' in Hgetp'; eauto.
     lets H00: Hop Hgetp'.
     clear Hop.
     destruct H00 as [Hcre |  [Hnml | Hdel]].
    + destruct Hcre as (Hgetl' & Hnin & Hnref & Hptr).
       left.
       split; auto.
       casetac ptr0 ptr Heqe Hneqe.
      -
        subst.
        false. apply Hncre.
        exists t.
        unfold tsk_loc_ptr.
        split; auto.
      -
        splits; auto.
        introv Hptrin. apply Hnin.
        eapply ptr_in_ecblist_tail; eauto. 
        unfold is_kobj in Hptr. unfold is_kobj.
        simpljoin1.
        exists x x0.
        assert (join (sig ptr (abssem i1, wls)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
   +
     simpljoin.
     right. left.
     splits; auto.
     casetac ptr0 ptr Ht Hf.
      -
        subst.
        right.
        unfold ptr_in_ecblist. unfold ptr_in_ecbsllseg. simpl.
        asserts_rewrite ((os_inv.beq_addrval ptr ptr) = true).
        {
          unfold os_inv.beq_addrval.
          destruct ptr.
          rewrite OSTimeTickPure.beq_pos_true.
          rewrite Int.eq_true.
          tauto.
        }
        auto.
     -
       destruct H0.
       left. unfold is_kobj in H0. unfold is_kobj. simpljoin1. exists x x0.
        assert (join (sig ptr (abssem i1, wls)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        right.
        unfold ptr_in_ecblist.
        unfold ptr_in_ecblist in H0.
        unfold ptr_in_ecbsllseg; fold ptr_in_ecbsllseg.
        destruct (beq_val (Vptr ptr0) (Vptr ptr)) eqn: E.
        auto.
        change (V_OSEventListPtr
                  (V$ OS_EVENT_TYPE_UNUSED :: V$ 0 :: Vint32 i1 :: eptr :: etbl :: fecbh :: pegrp :: petbl :: nil)) with (Some fecbh).
        simpl. auto.
    + right. right.
        simpljoin.
        casetac ptr0 ptr Ht Hf.
        subst.
        false.
        unfold tsk_loc_ptr in *.
        eapply Hndel; eauto.
        splits; auto.
        unfold is_kobj in H0. unfold is_kobj. simpljoin1. exists x x0.
        assert (join (sig ptr (abssem i1, wls)) els' els).
        join auto.
        eapply perm_map_lemmas_part4.join_sig_get_r; eauto.
        introv Hf'.
        simpljoin.
        casetac ct x Ht0 Hf0.
        subst. rewrite set_a_get_a in H4; inverts H4.
        rewrite set_a_get_a' in H4; eauto.
Qed.


Lemma objdel_nodup_del_preserve:
forall locmp ptrmp ct ptr,
  objdel_nodup locmp ptrmp ->
 ~ (exists t, tsk_loc_ptr locmp ptrmp t __Loc_objdel ptr) -> 
  objdel_nodup (set locmp ct (V$ __Loc_objdel)) (set ptrmp ct (Vptr ptr)).
Proof.
 unfold objdel_nodup.
 introv Hdel Hnex.
 unfold tsk_loc_ptr in *.
 introv Hneq Hget1 Hget2 Hp1 Hp2.
 casetac ct t1 Ht Hf.
 subst.
 rewrite set_a_get_a in Hget1, Hp1.
 inverts Hget1; inverts Hp1.
 rewrite set_a_get_a' in Hget2, Hp2; eauto.
 introv Heq.
 subst.
 eapply Hnex; eauto.
 rewrite set_a_get_a' in Hget1, Hp1; eauto.
 casetac ct t2 Ht0 Hf0.
 subst.
 rewrite set_a_get_a in Hget2, Hp2.
 inverts Hget2; inverts Hp2.
  introv Heq.
  subst.
  eapply Hnex; eauto.
  rewrite set_a_get_a' in Hget2, Hp2; eauto.
Qed.

Lemma objcre_nodup_del_preserve:
forall locmp ptrmp ct ptr,
  objcre_nodup locmp ptrmp ->
  objcre_nodup (set locmp ct (V$ __Loc_objdel)) (set ptrmp ct (Vptr ptr)).
Proof.
 unfold objcre_nodup.
 introv Hcre.
 introv Hneq Hget1 Hget2 Hp1 Hp2.
 casetac ct t1 Ht Hf.
 subst.
 rewrite set_a_get_a in Hget1, Hp1.
 inverts Hget1; inverts Hp1.
 rewrite set_a_get_a' in Hget1, Hp1; eauto.
 casetac ct t2 Ht0 Hf0.
 subst.
 rewrite set_a_get_a in Hget2, Hp2.
 inverts Hget2; inverts Hp2.
  rewrite set_a_get_a' in Hget2, Hp2; eauto.
Qed.

Lemma objref_distinct_objref_clear_nref: 
  forall objs idx ptr att att',
    objref_distinct objs ->
    get objs idx = Some (objid ptr, att) -> 
    ~obj_ref (set objs idx (objnull, att')) ptr.
Proof.
  introv Hct Hget Href.
  unfold obj_ref in *.
  unfold objref_distinct in *.
  simpljoin.
  casetac idx x Ht Hf.
  subst.
  rewrite set_a_get_a in H. inverts H.
  rewrite set_a_get_a' in H; eauto.
Qed.

Lemma obj_aux_p_del_preserve: 
  forall locmp ptrmp els fecbh fecbvl objs idx attr ct ptr, 
    OBJ_AUX_P locmp ptrmp els fecbh fecbvl objs ->
    is_kobj els ptr ->
   ~ obj_ref (set objs idx (objnull, attr)) ptr ->
    ~ (exists t', tsk_loc_ptr locmp ptrmp t' __Loc_objcre ptr) ->
    OBJ_AUX_P (set locmp ct (V$ __Loc_objdel)) (set ptrmp ct (Vptr ptr)) els fecbh fecbvl
                        (set objs idx (objnull, attr))  .
Proof.
  introv Hop Hobj Hnref Hnex.
  unfold OBJ_AUX_P in Hop.
  unfold OBJ_AUX_P.
  introv Hgetp'.
  unfold tsk_loc_ptr in *.
  casetac t ct Heqt Hneqt.
  * subst.
     rewrite set_a_get_a in *.
     inverts Hgetp'.
     right. right.
     splits; eauto.
     introv Hf.
     simpljoin.
     casetac x ct Heqt0 Hneqt0.
     subst.
     rewrite set_a_get_a in *.
     tryfalse.
     rewrite set_a_get_a' in *; eauto.
  *
    rewrite set_a_get_a' in *; eauto.
    lets H00: Hop Hgetp'.
    clear Hop.
    destruct H00 as [Hcre |  [Hnml | Hdel]].
    +
       simpljoin.
       left. splits; auto.
       introv Hf.
       eapply H1.
       eapply obj_ref_del_preserve; eauto.
   + simpljoin.
       auto.
   + simpljoin.
       right. right.
       splits; auto.
       introv Hf.
       simpljoin.
       casetac x ct Heqt0 Hneqt0.
       subst.
       rewrite set_a_get_a in *.
       tryfalse.
       rewrite set_a_get_a' in *; eauto.
       introv Hf.
       eapply H2.
       eapply obj_ref_del_preserve; eauto.
Qed.

Lemma objdel_nodup_set_normal_loc_preserve: 
  forall locmp ptrmp tid, 
    objdel_nodup locmp ptrmp ->
    objdel_nodup (set locmp tid (V$ __Loc_normal)) ptrmp. 
Proof.
  introv Hnd.
  unfold objdel_nodup in *.
  introv Hne Hget1 Hget2 Het1 Het2.
  casetac tid t1 Heq Hneq.
  - subst.
    rewrite set_a_get_a in Hget1; inverts Hget1.
  - casetac tid t2 Heq' Hneq'.
    + subst.
      rewrite set_a_get_a in Hget2; inverts Hget2.
    + rewrite set_a_get_a' in Hget1, Hget2; eauto.
Qed.

Lemma objcre_nodup_set_normal_loc_preserve: 
  forall locmp ptrmp tid, 
    objcre_nodup locmp ptrmp ->
    objcre_nodup (set locmp tid (V$ __Loc_normal)) ptrmp.  
Proof.
  introv Hnc.
  unfold objcre_nodup in *.
  introv Hne Hget1 Hget2 Het1 Het2.
  casetac tid t1 Heq Hneq.
  - subst.
    rewrite set_a_get_a in Hget1.
    tryfalse.
  - casetac tid t2 Heq' Hneq'.
    + subst.
      rewrite set_a_get_a in Hget2.
      tryfalse.
    + rewrite set_a_get_a' in Hget1, Hget2; eauto.
Qed.

Lemma obj_aux_p_set_normal_loc_preserve: 
  forall locmp ptrmp els fecbh fecbvl objs tid, 
    OBJ_AUX_P locmp ptrmp els fecbh fecbvl objs ->
    get ptrmp tid = Some (Vnull) -> 
    OBJ_AUX_P (set locmp tid (V$ __Loc_normal)) ptrmp els fecbh fecbvl objs. 
Proof.
  introv Hop Hgetp. 
  unfold OBJ_AUX_P in *. 
  introv Hgetp'.
  lets H00: Hop Hgetp'. clear Hop. 
  casetac tid t Ht Hf.
  -
    subst.
    rewrite Hgetp in Hgetp'.
    inverts Hgetp'.
  -
    rewrite set_a_get_a'; eauto.
    destruct H00; auto.
    destruct H; auto.
    simpljoin.
    right. right.
    splits; auto.
    introv Hex. apply H1.
    simpljoin1.
    casetac tid x Heq' Hneq'.
    subst. rewrite set_a_get_a in *. tryfalse.
    rewrite set_a_get_a' in *; eauto.
Qed.


