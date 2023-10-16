
Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import service_obj_oper.
Require Import ifun_spec.
Require Import kernel_obj_oper_spec.
Require Import service_obj_oper_spec.
(* absimp lemmas *)
Require Import abs_infer_step.
Require Import abs_infer_abt.
Require Import ucos_frmaop.
Require Import hoare_tactics.
Require Import pure_auto.
Require Import ucos_pauto.
Require Import sep_auto.
Require Import seplog_tactics.
Require Import seplog_lemmas.
Require Import sep_cancel_ext.
Require Import derived_rules.
Require Import hoare_conseq.
Require Import ucos_forward.
Require Import math_auto.

Require Import symbolic_lemmas.
Require Import Aarray_new_common.
Require Import Aarray_new_common_extend.

Require Import sem_common.
Require Import obj_common.
Require Import obj_common_ext.

Require Import objauxvar_lemmas.
Require Import objaux_pure.
Require Import seplog_pattern_tacs.
Require Import hoare_assign_tac_ext.

Lemma sobjoper_absimp_idxerr:
  forall sch idx P vptr verr,
    (Int.ltu idx Int.zero = true \/
       Int.ltu (Int.repr MAX_OBJ_NUM) idx = true \/ Int.eq idx (Int.repr MAX_OBJ_NUM) = true) -> 
    can_change_aop P ->
    absinfer sch
      (<|| sobjoper ( Vint32 idx :: vptr :: verr :: nil) ||>  ** P) 
      (<|| END (Some (Vint32 Int.mone)) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma sobjoper_absimp_kobjerr:
  forall sch idx P objs vptr verr,
    Int.ltu idx Int.zero = false ->
    Int.ltu idx (Int.repr MAX_OBJ_NUM) = true ->
    ~ (exists ptr attr, get objs idx = Some (objid ptr, attr)) ->
    can_change_aop P ->
    absinfer sch
      (<|| sobjoper ( Vint32 idx :: vptr :: verr :: nil) ||>  ** HObjs objs ** P) 
      (<|| END (Some (Vint32 Int.mone)) ||> ** HObjs objs ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma sobjoper_absimp_get_kobj:
  forall sch idx P objs ptr attr vptr verr,
    Int.ltu idx Int.zero = false ->
    Int.ltu idx (Int.repr MAX_OBJ_NUM) = true ->
    get objs idx = Some (objid ptr, attr) ->
    vptr = Vptr ptr ->
    can_change_aop P ->
    absinfer sch
      (<|| sobjoper ( Vint32 idx :: vptr :: verr :: nil) ||>  ** HObjs objs ** P) 
      (<|| kobjoper ( vptr :: verr :: nil) ;; sobjoper_kobj_ret (| verr :: nil |) ||> ** HObjs objs ** P).
Proof.
  infer_solver 2%nat.
Qed.

Lemma sobjoper_absimp_get_kobj_abt:
  forall sch idx P objs ptr attr vptr verr,
    Int.ltu idx Int.zero = false ->
    Int.ltu idx (Int.repr MAX_OBJ_NUM) = true ->
    get objs idx = Some (objid ptr, attr) ->
    vptr <> Vptr ptr ->
    can_change_aop P ->
    absinfer sch
      (<|| sobjoper ( Vint32 idx :: vptr :: verr :: nil) ||>  ** HObjs objs ** P) 
      (<|| ABORT ||> ** HObjs objs ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HObjs objs ** P)).
  can_change_aop_solver.
  do 2 (eapply absinfer_trans; try eapply absinfer_choice2; eauto).
  eapply absinfer_trans; try eapply absinfer_seq_abt; eauto.
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma sobjoper_absimp_kobj_ret:
  forall sch P verr,
    can_change_aop P ->
    absinfer sch
      (<|| sobjoper_kobj_ret (| verr :: nil |) ||>  ** P) 
      (<|| END (Some verr) ||> ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma service_obj_oper_Proof: 
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api service_obj_oper sobjoperapi vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api service_obj_oper sobjoperapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api service_obj_oper = Some (t, d1, d2, s) /\
        {|new_OS_spec, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 3 (destruct v'; try apply absabort_rule).
  rename i into vi.
  rename v into vptr.
  rename v0 into verr.
  rename v'0 into errv.
  rename v'1 into v'0.

  hoare forward prim.
  hoare unfold.
  hoare_lifts_trms_pre Aop.
  hoare forward; try solve [pure_auto].
  hoare unfold.
  assert (Hif: Int.ltu vi Int.zero = true \/
                       Int.ltu (Int.repr MAX_OBJ_NUM) vi = true \/ 
                       Int.eq vi (Int.repr MAX_OBJ_NUM) = true).
  { change ($ 0) with Int.zero in *.
     destruct (Int.ltu vi Int.zero) eqn: eq1;
     destruct (Int.ltu (Int.repr MAX_OBJ_NUM) vi) eqn: eq2;
     destruct (Int.eq vi (Int.repr MAX_OBJ_NUM)) eqn: eq3;
     simpl in H1; auto.
  }
 clear H1 H2 H3.
 eapply abscsq_rule.
 eapply noabs_oslinv.
 eapply sobjoper_absimp_idxerr; eauto.
 can_change_aop_solver.
 eapply absinfer_eq.
 hoare forward prim.
 pure_auto.
 hoare forward.
 eapply hoare_disj_afalseP_l_pre.
 hoare unfold.
 assert (Hif: Int.ltu vi Int.zero = false /\ Int.ltu vi (Int.repr MAX_OBJ_NUM) = true).
  { change ($ 0) with Int.zero in *.
     destruct (Int.ltu vi Int.zero) eqn: eq1;
     destruct (Int.ltu (Int.repr MAX_OBJ_NUM) vi) eqn: eq2;
     destruct (Int.eq vi (Int.repr MAX_OBJ_NUM)) eqn: eq3;
     simpl in H1; auto;
     repeat (try change (Int.ltu Int.zero Int.zero) with false in *; 
                  try change (Int.ltu Int.zero Int.one) with true in *; simpl in *);
     try destruct H1;
     tryfalse.
     rewrite Intlt_false_is_Zge in eq2.
     apply semacc_int_eq_false in eq3.
     rewrite <- ZIntneq_is_Zneq in eq3.
     rewrite Intlt_true_is_Zlt.
     splits; auto with zarith.
  }
 clear H1. destruct Hif as (Hrgn1 & Hrgn2).
 (* p ′ =ₑ efield (obj_arr ′ [idx ′]) ptr;ₛ *)
 unfold AOBJ.
 unfold AObjs.
 hoare unfold.
 rename v'21 into objvll.
 hoare_assert_pure (length objvll = (∘ (MAX_OBJ_NUM))).
  { get_hsat Hsat. 
    sep_lifts_trms_in Hsat AObjArr.
     eapply aobjarr_len_frm; eauto.  }
  eapply pure_split_rule'; introv Hlen.
  hoare_lifts_trms_pre (Aop, AObjArr).
  eapply backward_rule1.
  introv Hsat.
  eapply AObjArr_unfold_any_idx_frm with (idxv:=Z.to_nat (Int.unsigned vi)).
  sep cancel AObjArr.
  eauto.
  rewrite Hlen.
  eapply obj_rgn_idx_lt; eauto.

  hoare unfold.
  hoare_lifts_trms_pre (Aop).
  hoare forward.
  eapply assign_rule_lvar.
  split; introv Hsat. sep cancel (Alvarmapsto p). eauto.
  sep auto.
  sep_get_rv_array_struct.
  eapply new_array_type_vallist_match_split in H3; eauto.
  simpljoin; auto.
  eapply eq_vptr; eauto.
  intros. eexists. sep cancel p_local. simpl; eauto.

  lets Hobj_vll: H3.
  rename H3 into Hobj_vl.
  eapply new_array_type_vallist_match_split in Hobj_vl; eauto.
  destruct Hobj_vl as (Hmat1 & Hmat2 & Hobj_vl).
  lets Hisptr: struct_type_vallist_match_service_obj_t_ptr Hobj_vl.
  lets Hobj_vl_eq: struct_type_vallist_match_service_obj_t_vl Hobj_vl.
  destruct Hobj_vl_eq as (vattr & vp & Heq).
  subst.
  simpl nth_val' in *.

  lets Hls: obj_corr H1 H10 Hrgn1.
  destruct Hls as (oid_opt & att & Hget & Hvatt & Hcs).
  clear -Hrgn1 Hrgn2.  unfold MAX_OBJ_NUM in *. int auto.
  inverts Hvatt.
  unfold V_ObjPtr in Hcs; simpl nth_val in Hcs.

  (* If (p ′ ==ₑ NULL ||ₑ p ′ ==ₑ 〈 OS_EVENT ∗ 〉 PlaceHolder) *)
  unfold PlaceHolder.
  hoare_lifts_trms_pre ((* Aop,  *)p, AOSTCBPrioTbl(* , A_dom_lenv *)).
  hoare remember (1 :: 2 :: (* 3 :: 4 :: *) nil)%nat pre.
  assert (Hif_rv: 
                  LV p @ OS_EVENT ∗ |-> vp ** AOSTCBPrioTbl v'5 v'11 v'14 v'20 vhold_addr ** H3 ==>
                  Rv p ′ ==ₑ NULL ||ₑ p ′ ==ₑ 〈 OS_EVENT ∗ 〉 (&ₐ OSPlaceHolder ′) @ Int32u == 
                  val_inj (bool_or (val_inj (val_eq vp Vnull)) (val_inj (val_eq vp (Vptr vhold_addr)))) ).
  { introv Hsat.
     subst.
     unfold AOSTCBPrioTbl in *.
     eapply bop_rv.
     sep get rv.
     clear -Hisptr; pure_auto.
     clear -Hisptr; pure_auto.
     eapply bop_rv.
     sep get rv.
     clear -Hisptr; pure_auto.
     eapply cast_rv_tptr.
     eapply addrof_gvar_rv.
     apply  astar_l_anotinlenv_intro.
     sep cancel OSPlaceHolder.
     eauto.
    {
     sep_lifts_trms_in Hsat A_dom_lenv.
     apply astar_l_adomlenv_elim in Hsat.
     destruct Hsat as (Hlenv & _).
     clear -Hlenv.
     unfolds in Hlenv.
     unfold EnvMod.indom.
     pure_auto.
     destruct H as ((l & t) & H).
     assert (Hf: ~ListSet.set_In (OSPlaceHolder, t)
                           ((idx, long) :: (err, long) :: (p, OS_EVENT ∗) :: nil)).
     simpl; pure_auto; tryfalse.
     rewrite Hlenv in Hf.
     pure_auto.
    }
    simpl; auto.
    eauto.
    simpl. 
    destruct Hisptr as [Heq | ((pb & pi) & Heq)]; destruct vhold_addr;
    subst; simpl; clear; pure_auto.
    simpl; eauto.
    simpl; auto.
    destruct Hisptr as [Heq | ((pb & pi) & Heq)]; destruct vhold_addr;
    subst; simpl; clear; pure_auto.
    simpl; auto.
   }
  subst.
  hoare forward.
  eapply ift_rule_general.
  introv Hsat.
  eexists.
  eapply Hif_rv; eauto.
  (* Aisfalse *)
  introv Hsat.
  eapply sep_aconj_r_aisfalse_to_astar; eauto.
  (* Aistrue *)
  eapply backward_rule1.
  introv Hsat.
  eapply sep_aconj_r_aistrue_to_astar; eauto.
  (* actual if true *)
  hoare unfold.
  instantiate (1:= Afalse).
  assert (Hif2: vp = Vnull \/ vp =  (Vptr vhold_addr)).
  { clear -H3 Hisptr.
     destruct Hisptr as [Heq | ((pb & pi) & Heq)]; destruct vhold_addr;
     subst; simpl in *; auto.
     destruct (peq pb b) eqn: eq1;
     destruct (Int.eq pi i) eqn: eq2;
     simpl in H3;
     repeat (try change (Int.ltu Int.zero Int.zero) with false in *; 
                  try change (Int.ltu Int.zero Int.one) with true in *; simpl in *);
     tryfalse.
     eapply semacc_int_eq_true in eq2; subst; auto.
  }
  assert (Hnptr: ~(exists ptr attr, get v'22 vi = Some (objid  ptr, attr))).
  { clear -Hif2 Hcs Hget.
     rewrite Hget. 
     destruct Hif2; subst.
     destruct Hcs as [ | []]; simpljoin; tryfalse.
     introv Hf; destruct Hf as (ptr & sttr & Hf); inverts Hf.
     destruct Hcs as [ | []]; simpljoin; tryfalse.
     introv Hf; destruct Hf as (ptr & sttr & Hf); inverts Hf.
  }
  hoare_lifts_trms_pre (Aop, absobjs).
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply sobjoper_absimp_kobjerr; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  hoare forward prim.
  unfold AOBJ.
  unfold AObjs.
  sep pauto; eauto.
  sep cancel tcbllsegobjaux.
  sep cancel p_local.
  eapply AObjArr_select_sn_ex_strong.
  exists v'16 (Z.to_nat (Int.unsigned vi)) v'21 v'25 v'26.
  exists (Vint32 att :: vp :: nil).
  sep pauto; eauto.
  pure_auto.
  hoare forward.
  hoare forward.
  hoare_split_pure_all.
  assert (Hif2: vp <> Vnull /\ vp <>  (Vptr vhold_addr)).
  { clear -H3 Hisptr.
     destruct Hisptr as [Heq | ((pb & pi) & Heq)]; destruct vhold_addr;
     subst; simpl in *; auto;
     repeat (try change (Int.ltu Int.zero Int.zero) with false in *; 
                  try change (Int.ltu Int.zero Int.one) with true in *; simpl in *);
     try destruct H3;
     tryfalse;
     try destruct (peq pb b) eqn: eq1;
     try destruct (Int.eq pi i) eqn: eq2;
     simpl in H;
     repeat (try change (Int.ltu Int.zero Int.zero) with false in *; 
                  try change (Int.ltu Int.zero Int.one) with true in *; simpl in *);
     tryfalse;
     try eapply semacc_int_eq_false in eq2;
     try eapply semacc_int_eq_true in eq2;
     try subst; split; auto;
     try solve [ introv Hf; inverts Hf; tryfalse].
  }
  assert (Heq:  exists oid, oid_opt = objid oid /\ vp = Vptr oid).
  { clear -Hif2 Hcs.
     destruct Hcs as [ | []]; simpljoin; tryfalse.
     inverts H2.
     eauto.
  }
  destruct Heq as (ptr & Heq & Heq2); subst.
  clear Hif_rv.
  eapply backward_rule1.
  introv hsat.
  eapply AObjArr_select_sn_ex_strong.
  exists v'16 (Z.to_nat (Int.unsigned vi)) v'21 v'25 v'26.
  exists (Vint32 att :: Vptr ptr :: nil).
  sep pauto.
  (*  *)
  unfold tcbllsegobjaux.
  hoare_lifts_trms_pre (llsegobjaux, AOSTCBList, p_local).
  eapply backward_rule1.
  introv Hsat.
  eapply tcbllsegobjaux_split3_join2_frm''; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  assert (Hloc: get v'23 tid = Some (V$ __Loc_normal)).
  { eapply join_get_r; eauto.
      eapply join_sig_get; eauto.
   }
  assert (Hptr: get v'24 tid = Some Vnull).
  { eapply join_get_r; eauto.
      eapply join_sig_get; eauto.
   }
  hoare_assign_aux.
  fold_aux_ptr (Vptr ptr).

  hoare_lifts_trms_pre (Aop, absobjs).
  assert (Hrvp: vptr = Vptr ptr \/ vptr <> Vptr ptr) by tauto.
  destruct Hrvp. subst.
  2:{
       eapply abscsq_rule.
       eapply noabs_oslinv.
       eapply sobjoper_absimp_get_kobj_abt; eauto.
       unfold CurTid.
       can_change_aop_solver.
       eapply absinfer_eq.
       eapply absabort_rule.
      }
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply sobjoper_absimp_get_kobj; eauto.
  unfold CurTid.
  can_change_aop_solver.
  eapply absinfer_eq.


  assert (Hobj: obj_ref v'22 ptr).
  { unfolds; eauto. }
  assert (Hnex1: ~ (exists t, tsk_loc_ptr v'23 v'24 t __Loc_objdel ptr)).
  { introv Hf.
     destruct Hf as (t' & Hf).
     eapply obj_aux_del; eauto.
  }
  assert (Hnex2: ~ (exists t, tsk_loc_ptr v'23 v'24 t __Loc_objcre ptr)).
  { introv Hf.
     destruct Hf as (t' & Hl & Hp).
     eapply obj_aux_cre; eauto.
  }

  hoare forward prim.
  unfold p_local. unfold LINV. unfold OSLInv.
  unfold AOBJ.
  unfold AObjs.
  unfold tcbllsegobjaux.
  sep normal.
  sep eexists.
  sep cancel llsegobjaux.
  sep pauto; eauto.
  eapply objdel_nodup_normal_ptr_preserve; eauto.
  eapply objcre_nodup_normal_semptr_preserve; eauto.
  eapply obj_aux_p_ptr_normal_preserve; eauto.
  unfolds. eauto.
  pure_auto.

  change (Vptr ptr :: verr :: nil) with ((Vptr ptr :: nil) ++ (verr :: nil)).
  hoare forward.
  sep cancel Aop.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel p_local.
  eauto.
  simpl; eauto.
  pure_auto.

  unfold retpost. introv Hsat.
  inverts Hsat; sep pauto.
  get_hsat Hsat. sep destruct Hsat.
  sep split in Hsat. simpljoin1. pure_auto.

  intros. sep auto. sep cancel p_local. simpl; auto.
  intros. sep auto. sep cancel p_local. simpl; auto.

  unfold KObjOperPost.
  unfold KObjOperPost'.
  unfold getasrt.
  hoare unfold.
  inverts H18.

  clear.
  hoare forward prim.
  unfold AOBJ.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  simpljoin.

  unfold tcbllsegobjaux.
  hoare_lifts_trms_pre (llsegobjaux, AOSTCBList, p_local).
  eapply backward_rule1.
  introv Hsat.
  eapply tcbllsegobjaux_split3_join2_frm''; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  hoare_assign_aux.
  unfold isptr; auto.
  fold_aux_ptr Vnull.

  rename v'22 into locmp.
  rename v'23 into ptrmp.
  assert (Hget_loc: get locmp tid = Some (V$ os_code_defs.__Loc_normal)).
  { eapply join_get_r; eauto.
     eapply join_sig_get; eauto.
   }
  assert (Hget_ptr: get ptrmp tid = Some (Vptr ptr)).
  { eapply join_get_r; eauto.
     eapply join_sig_get; eauto.
   }

  hoare_lifts_trms_pre (Aop).
  eapply abscsq_rule.
  eapply noabs_oslinv.
  eapply sobjoper_absimp_kobj_ret; eauto.
  unfold CurTid.
  can_change_aop_solver.
  eapply absinfer_eq.

  hoare forward prim.
  unfold p_local. unfold LINV. unfold OSLInv.
  unfold AOBJ.
  unfold tcbllsegobjaux.
  sep normal.
  sep eexists.
  sep cancel llsegobjaux.
  sep cancel AObjs.
  sep pauto; eauto.
  eapply objdel_nodup_set_null_preserve; eauto.
  eapply objcre_nodup_set_null_preserve; eauto.
  eapply obj_aux_p_set_null_preserve; eauto.
  unfold isptr.
  splits; eauto.
  pure_auto.

  hoare forward.
  Unshelve.
  exact O.
Qed.

