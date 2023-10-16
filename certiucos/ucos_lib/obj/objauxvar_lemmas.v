
Require Import include_frm.
Require Import os_ucos_h.
Require Import code_notations.
Require Import os_inv.

Require Import seplog_lemmas.
Require Import seplog_tactics.
Require Import sep_cancel_ext.

Require Import derived_rules.
Require Import hoare_forward.
Require Import symbolic_lemmas. 

Require Import join_lib. 
Require Import join_lib_aux.

Require Import inv_prop. 

Require Import seplog_pattern_tacs.

Ltac simpl_sat H := unfold sat in H; fold sat in H; simpl substmo in H; simpl getmem in H; simpl getabst in H; simpl empst in H.

Ltac simpl_sat_goal := unfold sat; fold sat; unfold substmo; unfold substaskst; unfold getmem; unfold getabst; unfold get_smem; unfold get_mem.

Ltac simp_mem_abst :=
  repeat (
      match goal with
      | H: context [getmem (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)] |- _ =>
          change (getmem (t1, t2, t3, t4, t5, t6, t7)) with t3 in H
      | H: context [getabst (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)] |- _ =>
          change (getabst (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)) with t6 in H
      | H: Maps.join ?t1 empenv ?t2 |- _ => (apply map_join_emp' in H; subst t1)
      | H: Maps.join empenv ?t1 ?t2 |- _ => (apply map_join_emp'' in H; subst t1)
      | H: context [?t = empenv] |- _ => subst t
      end).

Ltac change_smo hyp :=
  repeat (
      match type of hyp with
      | context [substmo (?e, ?e0, ?m, ?i0, ?l, ?o, ?a) ?m' ?o'] =>
          change (substmo (e, e0, m, i0, l, o, a) m' o') with (e, e0, m', i0, l, o', a) in hyp
      end).

Ltac change_smo_hyps :=
  repeat (
      match goal with
      | H: context [substmo (?e, ?e0, ?m, ?i0, ?l, ?o, ?a) ?m' ?o'] |- _ => 
          change (substmo (e, e0, m, i0, l, o, a) m' o') with (e, e0, m', i0, l, o', a) in H
      end).

Open Scope Z_scope. 
Open Scope int_scope. 
Open Scope code_scope. 

Lemma tcbllsegobjaux_split: 
  forall vll1 vll2 head locmp ptrmp s tn nextf,
    s |= llsegobjaux head tn (vll1 ++ vll2) locmp ptrmp nextf -> 
    exists locmp1 ptrmp1 locmp2 ptrmp2 tn',
      s |= llsegobjaux head tn' vll1 locmp1 ptrmp1 nextf **
        llsegobjaux tn' tn vll2 locmp2 ptrmp2 nextf ** 
        [| join locmp1 locmp2 locmp |] **
        [| join ptrmp1 ptrmp2 ptrmp |]. 
Proof.
  inductions vll1.

  introv Hsat. 
  simpl in Hsat.
  exists (emp : AuxLocMod.map).
  exists (emp : AuxPtrMod.map).
  simpl llsegobjaux at 1.
  exists locmp. exists ptrmp. exists head.
  sep split; auto.
  join auto. join auto.

  introv Hsat.
  change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)) in Hsat.
  unfold llsegobjaux in Hsat. fold llsegobjaux in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
 
  simpl_sat Hsat; simpljoin1.
  eapply IHvll1 in H8.
  destruct s as [[[[[[]]]]]]. simp_mem_abst. change_smo_hyps.
  destruct H8 as (locmp10 & ptrmp10 & locmp20 & ptrmp20 & tn'0 & Hsat0).
  sep split in Hsat0.
  exists (merge (sig x x1) locmp10).
  exists (merge (sig x x2) ptrmp10).
  exists locmp20.
  exists ptrmp20.
  exists tn'0.
  unfold llsegobjaux at 1. fold llsegobjaux.
  sep normal.
  exists x. exists x0. exists x1 x2.
  exists locmp10. exists ptrmp10.
  sep split; eauto.
  sep remember (1::nil)%nat.
  simpl_sat_goal.
  do 6 eexists.
  splits; eauto.

  unfold TcbJoin in H2.
  eapply join_lib_aux.join_join_join_merge; eauto.
  unfold TcbJoin in H1.
  eapply join_lib_aux.join_join_join_merge; eauto.

  unfold TcbJoin. unfold TcbJoin in H2.
  clear -H2 H3.
  assert (Hjo1: join x4 (sig x x2) ptrmp) by join auto.
  assert (Hjo2: join ptrmp20 ptrmp10 x4) by join auto.
  lets H00: join_whole2part Hjo2 Hjo1.
  apply join_disj in H00. 
  apply join_merge_disj.
  eapply disjoint_sym; eauto.

  unfold TcbJoin. unfold TcbJoin in H1.
  clear -H H1.
  assert (Hjo1: join x3 (sig x x1) locmp) by join auto.
  assert (Hjo2: join locmp20 locmp10 x3) by join auto.
  lets H00: join_whole2part Hjo2 Hjo1.
  apply join_disj in H00.
  apply join_merge_disj. 
  eapply disjoint_sym; eauto.
Qed.

Lemma tcbllsegobjaux_split3: 
  forall vll1 vl vll2 head locmp ptrmp s tn nextf,
  s |= llsegobjaux head tn (vll1 ++ vl :: vll2) locmp ptrmp nextf -> 
  exists v1 v2 locmp1 ptrmp1 locmp2 ptrmp2,
  exists locmp' ptrmp' tn' a vn, 
    s |= llsegobjaux head tn' vll1 locmp1 ptrmp1 nextf **
           objaux_node a v1 v2 ** 
           llsegobjaux vn tn vll2 locmp2 ptrmp2 nextf ** 
           [| tn' = Vptr a |] ** 
           [| nextf vl = Some vn |] ** 
           [| join locmp1 (sig a v1) locmp' |] **
           [| join ptrmp1 (sig a v2) ptrmp' |] ** 
           [| join locmp' locmp2 locmp |] **
           [| join ptrmp' ptrmp2 ptrmp |].  
Proof.
  introv Hsat.
  apply tcbllsegobjaux_split in Hsat.
  unfold llsegobjaux at 2 in Hsat.
  fold llsegobjaux in Hsat.
  destruct Hsat as (locmp10 & ptrmp10 & locmp20 & ptrmp20 & tn' & Hsat0).
  sep normal in Hsat0.
  sep destruct Hsat0.
  sep split in Hsat0.
  exists x1 x2.
  subst tn'.
  exists locmp10 ptrmp10 x3 x4.
  exists (merge locmp10 (sig x x1)).
  exists (merge ptrmp10 (sig x x2)).
  exists (Vptr x) x x0.
  sep split; eauto.
  sep cancel objaux_node.
  sep lift 2%nat. auto.

  clear - H4 H2.
  unfold TcbJoin in H2.  
  eapply join_lib_aux.join_join_join_merge; eauto.

  clear - H1 H3.
  unfold TcbJoin in H1.
  eapply join_lib_aux.join_join_join_merge; eauto.

  unfold TcbJoin in H2.
  clear -H2 H4.
  assert (Hjo1: join x4 (sig x x2) ptrmp20) by join auto.
  assert (Hjo2: join ptrmp20 ptrmp10 ptrmp) by join auto.
  lets H00: join_whole2part Hjo1 Hjo2.
  apply join_disj in H00. 
  apply join_merge_disj.
  eapply disjoint_sym; eauto.

  unfold TcbJoin in H1.
  clear -H1 H3.
  assert (Hjo1: join x3 (sig x x1) locmp20) by join auto.
  assert (Hjo2: join locmp20 locmp10 locmp) by join auto.
  lets H00: join_whole2part Hjo1 Hjo2.
  apply join_disj in H00. 
  apply join_merge_disj.
  eapply disjoint_sym; eauto.
Qed.

Lemma tcbllsegobjaux_split3_join2: 
  forall vll1 vl vll2 head locmp ptrmp s tn nextf,
  s |= llsegobjaux head tn (vll1 ++ vl :: vll2) locmp ptrmp nextf -> 
  exists v1 v2 locmp1 ptrmp1 locmp2 ptrmp2,
  exists locmp' ptrmp' tn' a vn, 
    s |= llsegobjaux head tn' vll1 locmp1 ptrmp1 nextf **
           objaux_node a v1 v2 ** 
           llsegobjaux vn tn vll2 locmp2 ptrmp2 nextf ** 
           [| tn' = Vptr a |] ** 
           [| nextf vl = Some vn |] ** 
           [| join (sig a v1) locmp2 locmp' |] **
           [| join (sig a v2) ptrmp2 ptrmp' |] ** 
           [| join locmp1 locmp' locmp |] **
           [| join ptrmp1 ptrmp' ptrmp |].  
Proof.
  introv Hsat.
  apply tcbllsegobjaux_split in Hsat.
  unfold llsegobjaux at 2 in Hsat.
  fold llsegobjaux in Hsat.
  destruct Hsat as (locmp10 & ptrmp10 & locmp20 & ptrmp20 & tn' & Hsat0).
  sep normal in Hsat0.
  sep destruct Hsat0.
  sep split in Hsat0.
  exists x1 x2.
  subst tn'.
  exists locmp10 ptrmp10 x3 x4.
  exists (merge (sig x x1) x3).
  exists (merge (sig x x2) x4).
  exists (Vptr x) x x0.
  sep split; eauto.
  sep cancel objaux_node.
  sep lift 2%nat. auto.
  {
    clear - H2 H4.
    unfold TcbJoin in H2.
    apply join_merge in H2. subst ptrmp20. auto.
  }
  {
    clear - H1 H3.
    unfold TcbJoin in H1.
    apply join_merge in H1. subst locmp20. auto.
  }
  {
    apply map_join_merge.
    eexists; eauto.
  }
  {
    apply map_join_merge.
    eexists; eauto.    
  }
Qed.   

Lemma tcbllsegobjaux_split3_frm: 
  forall vll1 vl vll2 head locmp ptrmp s tn nextf P,
  s |= llsegobjaux head tn (vll1 ++ vl :: vll2) locmp ptrmp nextf ** P -> 
  s |= (EX v1 v2 locmp1 ptrmp1 locmp2 ptrmp2 locmp' ptrmp' tn' a vn, 
           llsegobjaux head tn' vll1 locmp1 ptrmp1 nextf **
           objaux_node a v1 v2 ** 
           llsegobjaux vn tn vll2 locmp2 ptrmp2 nextf ** 
           [| tn' = Vptr a |] **
           [| nextf vl = Some vn |] ** 
           [| join locmp1 (sig a v1) locmp' |] **
           [| join ptrmp1 (sig a v2) ptrmp' |] ** 
           [| join locmp' locmp2 locmp |] **
           [| join ptrmp' ptrmp2 ptrmp |]) ** P.  
Proof.
  intros.
  sep cancel P.
  eapply tcbllsegobjaux_split3 in H.
  do 11 destruct H.
  exists x x0 x1 x2.
  sep eexists. 
  eauto.
Qed. 

Lemma tcbllsegobjaux_split3_join2_frm: 
  forall vll1 vl vll2 head locmp ptrmp s tn nextf P,
  s |= llsegobjaux head tn (vll1 ++ vl :: vll2) locmp ptrmp nextf ** P -> 
  s |= (EX v1 v2 locmp1 ptrmp1 locmp2 ptrmp2 locmp' ptrmp' tn' a vn, 
           llsegobjaux head tn' vll1 locmp1 ptrmp1 nextf **
           objaux_node a v1 v2 ** 
           llsegobjaux vn tn vll2 locmp2 ptrmp2 nextf ** 
           [| tn' = Vptr a |] **
           [| nextf vl = Some vn |] ** 
           [| join (sig a v1) locmp2 locmp' |] **
           [| join (sig a v2) ptrmp2 ptrmp' |] ** 
           [| join locmp1 locmp' locmp |] **
           [| join ptrmp1 ptrmp' ptrmp |]) ** P.
Proof.
  intros.
  sep cancel P.
  eapply tcbllsegobjaux_split3_join2 in H.
  do 11 destruct H.
  exists x x0.
  sep eexists.
  eauto.
Qed. 

Lemma tcbvl_llsegaux_match_tn: 
  forall vll head hprev tail locmp ptrmp s tn tn',
    s |= llsegobjaux head tn vll locmp ptrmp V_OSTCBNext ** 
           tcbdllseg head hprev tail tn' vll -> 
    tn = tn'. 
Proof.
  inductions vll.
  -
    intros.
    simpl in H; simpljoin1.
  -
    introv Hsat.
    unfold llsegobjaux in Hsat; fold llsegobjaux in Hsat.
    unfold tcbdllseg in Hsat; fold tcbdllseg in Hsat.
    unfold dllseg in Hsat; fold dllseg in Hsat. 
    sep normal in Hsat.
    sep destruct Hsat.
    sep split in Hsat.  
    assert
      (Heq: dllseg x5 head tail tn' vll OS_TCB_flag V_OSTCBPrev V_OSTCBNext
       = tcbdllseg x5 head tail tn' vll) 
      by (unfold tcbdllseg; auto).
    rewrite Heq in Hsat. clear Heq. 
    sep_lifts_trms_in Hsat (node, objaux_node).
    destruct Hsat. simpljoin1.
    destruct H11. simpljoin1.
    rewrite H in H2. inverts H2.
    sep_lifts_trms_in H13 llsegobjaux.
    apply IHvll in H13. 
    congruence.
Qed. 

Lemma tcbvl_llsegaux_match_tn_frm: 
  forall vll head hprev tail locmp ptrmp s tn tn' P,
    s |= llsegobjaux head tn vll locmp ptrmp V_OSTCBNext ** 
           tcbdllseg head hprev tail tn' vll ** P ->  
    tn = tn'. 
Proof.
  intros.
  sep_lifts_trms_in H P.
  destruct H. simpljoin1.
  eapply tcbvl_llsegaux_match_tn in H4; eauto.
Qed.   

Lemma tcblist_llsegaux_match_tn_frm: 
  forall vll head locmp ptrmp s tn tn' P vll2 rtbl ct tcbls,
    s |= llsegobjaux head tn vll locmp ptrmp V_OSTCBNext ** 
           AOSTCBList head tn' vll vll2 rtbl ct tcbls ** P -> 
    tn = tn'. 
Proof.
  introv Hsat.
  unfold AOSTCBList in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep_lifts_trms_in Hsat (llsegobjaux, tcbdllseg).
  eapply tcbvl_llsegaux_match_tn_frm in Hsat; eauto.
Qed.   

Lemma llsegobjaux_merge_hd: 
  forall ct v1 v2 hd tn l locmp ptrmp locmp' ptrmp' v0 s P, 
    s |= objaux_node ct v1 v2 ** 
           llsegobjaux hd tn l locmp ptrmp V_OSTCBNext ** P -> 
    V_OSTCBNext v0 = Some hd -> 
    joinsig ct v1 locmp locmp' -> 
    joinsig ct v2 ptrmp ptrmp' -> 
    s |= llsegobjaux (Vptr ct) tn (v0 :: l) locmp' ptrmp' V_OSTCBNext ** P.  
Proof.
  introv Hsat Hv0 Hjo1 Hjo2.
  unfold llsegobjaux.
  fold llsegobjaux.
  sep normal.
  sep eexists.
  sep split; eauto.
Qed.   

Lemma llsegobjaux_merge2: 
  forall l1 l2 hd tn' tn locmp1 locmp2 ptrmp1 ptrmp2 locmp ptrmp s, 
    s |= llsegobjaux hd tn' l1 locmp1 ptrmp1 V_OSTCBNext ** 
           llsegobjaux tn' tn l2 locmp2 ptrmp2 V_OSTCBNext ->  
    join locmp1 locmp2 locmp -> 
    join ptrmp1 ptrmp2 ptrmp -> 
    s |= llsegobjaux hd tn (l1 ++ l2) locmp ptrmp V_OSTCBNext. 
Proof.
  inductions l1.

  introv Hsat Hjo1 Hjo2.
  unfold llsegobjaux in Hsat. fold llsegobjaux in Hsat.
  sep split in Hsat.
  simpljoin1.
  change (nil ++ l2) with l2.
  auto.

  introv Hsat Hjo1 Hjo2. 
  unfold llsegobjaux at 1 in Hsat. fold llsegobjaux in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  change ((a :: l1) ++ l2) with (a :: (l1 ++ l2)).
  unfold llsegobjaux; fold llsegobjaux.
  exists x x0 x1 x2.
  exists (merge x3 locmp2). exists (merge x4 ptrmp2).
  sep split; eauto.
  sep_rmb_trms_in Hsat objaux_node.
  solve_sat Hsat. 
  destruct_s s.
  change_smo_hyps. 
  lets H00: IHl1 H9.
  eapply H00.  
  eapply perm_map_lemmas_part1.join_join_merge; eauto.
  eapply perm_map_lemmas_part1.join_join_merge; eauto. 
  clear IHl1 Hsat.
  eapply join_join_merge23_join; eauto.
  eapply join_join_merge23_join; eauto.
Qed. 

Lemma llsegobjaux_merge2_frm: 
  forall l1 l2 hd tn' tn locmp1 locmp2 ptrmp1 ptrmp2 locmp ptrmp s P, 
    s |= llsegobjaux hd tn' l1 locmp1 ptrmp1 V_OSTCBNext ** 
           llsegobjaux tn' tn l2 locmp2 ptrmp2 V_OSTCBNext ** P ->  
    join locmp1 locmp2 locmp -> 
    join ptrmp1 ptrmp2 ptrmp -> 
    s |= llsegobjaux hd tn (l1 ++ l2) locmp ptrmp V_OSTCBNext ** P.  
Proof.
  introv Hsat Hjo1 Hjo2. 
  sep cancel 3%nat 2%nat.
  eapply llsegobjaux_merge2; eauto.
Qed.   

Require Import sep_auto.

Lemma locv_combine_eq:
  forall s ct v a v1 v2 P, 
    s |= PV get_off_addr ct loc_off @ Tint8 |-r-> v ** objaux_node a v1 v2 ** P -> 
    rule_type_val_match Tint8 v = true -> 
    ct = a -> 
    v = v1. 
Proof.
  introv Hsat Hmt Heq.
  unfold objaux_node in Hsat.
  sep normal in Hsat.
  subst a.
  sep combine (get_off_addr ct loc_off) in Hsat.
  sep split in Hsat.
  eapply rule_type_val_match_encode_val_eq
    with (v1 := v) (v2 := v1) (t := Tint8); auto.
Qed.

Ltac gen_eq_loc :=
  match goal with
    H: _ |= _ |- _ =>
    match type of H with
      context [get_off_addr ?ct loc_off] => (
      sep_lifts_trms_in H (get_off_addr ct loc_off, objaux_node);
      eapply locv_combine_eq in H; 
      eauto)
    end
  end.

Lemma ptrv_combine_eq: 
  forall s ct v a v1 v2 P, 
     s |= PV get_off_addr ct ptr_off @ (Tptr OS_EVENT) |-r-> v ** 
            objaux_node a v1 v2 ** P ->
     rule_type_val_match (Tptr OS_EVENT) v = true -> 
     ct = a -> 
     v = v2. 
Proof.
  introv Hsat Hmt Heq.
  unfold objaux_node in Hsat.
  sep normal in Hsat.
  subst a.
  sep combine (get_off_addr ct ptr_off) in Hsat.  
  sep split in Hsat.
  eapply rule_type_val_match_encode_val_eq
      with (v1 := v) (v2 := v2) (t:=Tptr OS_EVENT); 
    auto.
Qed.

Ltac gen_eq_ptr :=
  match goal with
    H: _ |= _ |- _ =>
    match type of H with
      context [get_off_addr ?ct ptr_off] => (
      sep_lifts_trms_in H (get_off_addr ct ptr_off, objaux_node);
      eapply ptrv_combine_eq in H;
      eauto)
    end
  end.

Ltac combine_aux trm :=
  let h := fresh in 
  eapply backward_rule1;
  [introv h;
   unfold objaux_node in h;
   sep normal in h;
   sep combine trm in h;
   eauto | idtac ]. 

Ltac forward_aux ct eq_tp_tac :=
  let h := fresh in 
  hoare_lifts_trms_pre Aop; 
  eapply seq_rule;
  [eapply assign_rule';
   [ eq_tp_tac; eauto |
     introv h; 
     split;
     [eapply symbolic_lemmas.field_asrt_impl_g;
      [ | |
        sep normal; 
        unfold AOSTCBList in h; 
        sep normal in h; 
        sep destruct h; 
        destruct ct; 
        sep cancel (Agvarmapsto OSTCBCur); 
        sep_lifts_trms_in h A_dom_lenv; 
        eapply symbolic_lemmas.dom_lenv_imp_notin_lenv with (x:=OSTCBCur) in h; 
        [sep cancel A_notin_lenv; sep auto | auto] 
      ]
     | sep get rv ]
     | ]
  | ] .

Ltac forward_ptr_assg ct :=
  combine_aux (get_off_addr ct ptr_off);
  forward_aux ct ltac:(eapply eq_vptr).

Ltac forward_loc_assg ct :=
  combine_aux (get_off_addr ct loc_off);
  forward_aux ct ltac:(eapply eq_int).  

Ltac try_cancel_aux_asst := 
  repeat first
         [sep cancel loc_off |
          sep cancel ptr_off ].


Ltac forward_aux_null ct eq_tp_tac :=
  let h := fresh in 
  hoare_lifts_trms_pre Aop; 
  eapply seq_rule;
  [eapply assign_rule';
   [ eq_tp_tac; eauto |
     introv h; 
     split;
     [eapply symbolic_lemmas.field_asrt_impl_g;
      [ | |
        sep normal; 
        unfold AOSTCBList in h; 
        sep normal in h; 
        sep destruct h; 
        destruct ct; 
        sep cancel (Agvarmapsto OSTCBCur); 
        sep_lifts_trms_in h A_dom_lenv; 
        eapply symbolic_lemmas.dom_lenv_imp_notin_lenv with (x:=OSTCBCur) in h; 
        [sep cancel A_notin_lenv; sep auto | auto] 
      ]
     |  eapply null_rv; eauto ]  
     | ]
  | ] .

Ltac forward_ptr_assg_null ct :=
  combine_aux (get_off_addr ct ptr_off);
  forward_aux_null ct ltac:(eapply eq_tnull).

Ltac get_hsat Hs := 
  match goal with
    H: _ |= _ |- _ => rename H into Hs
  end.

Require Import pure_lib.
Require Import ucos_pauto.

Lemma tcbllsegobjaux_split3_join2_frm': 
  forall vll1 vl vll2 head locmp ptrmp s tn P tn' rtbl ct tcbls vll3,
  s |= llsegobjaux head tn (vll1 ++ vl :: vll2) locmp ptrmp V_OSTCBNext **
         AOSTCBList head tn' vll1 vll3 rtbl ct tcbls ** P -> 
  s |= (EX v1 v2 locmp1 ptrmp1 locmp2 ptrmp2 locmp' ptrmp' vn, 
           llsegobjaux head tn' vll1 locmp1 ptrmp1 V_OSTCBNext **
           objaux_node ct v1 v2 ** 
           llsegobjaux vn tn vll2 locmp2 ptrmp2 V_OSTCBNext ** 
           [| tn' = Vptr ct |] **
           [| V_OSTCBNext vl = Some vn |] ** 
           [| join (sig ct v1) locmp2 locmp' |] **
           [| join (sig ct v2) ptrmp2 ptrmp' |] ** 
           [| join locmp1 locmp' locmp |] **
           [| join ptrmp1 ptrmp' ptrmp |]) **
          AOSTCBList head tn' vll1 vll3 rtbl ct tcbls ** P.
Proof.
  intros.
  eapply tcbllsegobjaux_split3_join2_frm in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  lets Heq: H.
  sep lifts (1 :: 4 :: nil)%nat in Heq.
  eapply tcblist_llsegaux_match_tn_frm in Heq.
  subst.
  assert (Heq: x8 = ct).
  { unfold AOSTCBList in H.
     sep normal in H.
     sep destruct H.
     sep split in H.
     destruct H0.
     inverts H9.
     auto. }
  subst.
  sep pauto; eauto.
Qed.

Lemma tcbllsegobjaux_split3_join2_frm'': 
  forall vll1 vl vll2 head locmp ptrmp s tn P tn' rtbl ct tcbls vll3 vinit loc ptr,
  s |= llsegobjaux head tn (vll1 ++ vl :: vll2) locmp ptrmp V_OSTCBNext **
         AOSTCBList head tn' vll1 vll3 rtbl ct tcbls **
         p_local OSLInv ct (logic_val vinit :: logic_val loc :: logic_val ptr :: nil)%list ** P -> 
  s |= (EX locmp1 ptrmp1 locmp2 ptrmp2 locmp' ptrmp' vn, 
           llsegobjaux head tn' vll1 locmp1 ptrmp1 V_OSTCBNext **
           objaux_node ct loc ptr ** 
           llsegobjaux vn tn vll2 locmp2 ptrmp2 V_OSTCBNext ** 
           [| tn' = Vptr ct |] **
           [| V_OSTCBNext vl = Some vn |] ** 
           [| join (sig ct loc) locmp2 locmp' |] **
           [| join (sig ct ptr) ptrmp2 ptrmp' |] ** 
           [| join locmp1 locmp' locmp |] **
           [| join ptrmp1 ptrmp' ptrmp |]) **
          AOSTCBList head tn' vll1 vll3 rtbl ct tcbls **
          p_local OSLInv ct (logic_val vinit :: logic_val loc :: logic_val ptr :: nil)%list ** P.
Proof.
  intros.
  eapply tcbllsegobjaux_split3_join2_frm' in H.
  sep normal in H.
  sep destruct H.
  sep split in H.
  subst.
  assert (Heq: x = loc /\  x0 = ptr).
  { unfold p_local in H.
     unfold OSLInv in H.
     unfold LINV in H.
     sep normal in H.
     sep destruct H.
     sep split in H.
     inverts H0. inverts H7.
     destruct H8 as (Hflag & Hloc & Hptr).
     splits; 
    [ gen_eq_loc; funfold Hloc; destruct Hloc as [ Hp | [Hp | Hp] ]; subst; pauto
      | gen_eq_ptr; funfold Hptr; destruct Hptr as [Hptr | (vp & Hptr)]; subst; simpl; auto].
  }
  simpljoin. subst.
  sep pauto; eauto.
Qed.


