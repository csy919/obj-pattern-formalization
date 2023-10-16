
Require Import include_frm.
Require Import NPeano.
Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import service_obj_create.
Require Import ifun_spec.
Require Import get_free_obj_idx_spec.
Require Import kernel_obj_create_spec.
Require Import service_obj_create_spec.
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

Lemma sobjcre_absimp_get_idx:
  forall sch P vr_idx objs s0,
   ((~(exists idx attr,  get objs idx = Some (objnull, attr) /\ 0 <= Int.unsigned idx < MAX_OBJ_NUM) /\
                                         vr_idx = Vint32 (Int.repr 255)) \/
                (exists idx attr,  get objs idx = Some (objnull, attr) /\ 0 <= Int.unsigned idx < MAX_OBJ_NUM /\
                                            vr_idx = Vint32 idx )) ->
    can_change_aop P ->
    absinfer sch
      (<|| sobjcre_get_idx (|vr_idx :: nil|);; s0 ||>  ** HObjs objs ** P)
      (<|| s0 ||> ** HObjs objs ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma sobjcre_absimp_get_idx_abt:
  forall sch P vkatt vsatt vr_idx vr_cre objs,
   ((~(exists idx attr,  get objs idx = Some (objnull, attr) /\ 0 <= Int.unsigned idx < MAX_OBJ_NUM) /\
                                         vr_idx <> Vint32 (Int.repr 255)) \/
                (exists idx attr,  get objs idx = Some (objnull, attr) /\ 0 <= Int.unsigned idx < MAX_OBJ_NUM /\
                                            vr_idx <> Vint32 idx)) ->
    can_change_aop P ->
    absinfer sch
      (<|| sobjcre ( vkatt :: vsatt :: vr_idx :: vr_cre :: nil) ||>  ** HObjs objs ** P)
      (<|| ABORT ||> ** HObjs objs ** P).
Proof.
  intros.
  assert (Hc: can_change_aop (HObjs objs ** P)).
  can_change_aop_solver.
  eapply absinfer_trans; try eapply absinfer_seq_abt; eauto.
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma sobjcre_absimp_idxerr:
  forall sch P vr_idx objs s0,
    ~(exists idx attr,  get objs idx = Some (objnull, attr) /\ 0 <= Int.unsigned idx < MAX_OBJ_NUM) -> 
    vr_idx = Vint32 (Int.repr 255) ->
    can_change_aop P ->
    absinfer sch
      (<|| sobjcre_idxerr (| vr_idx :: nil |) ?? s0 ||>  ** HObjs objs ** P) 
      (<|| END (Some (Vint32 Int.mone)) ||> ** HObjs objs ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma sobjcre_absimp_set_hold:
  forall sch idx P objs attr s0 s1,
    get objs idx = Some (objnull, attr) ->
    Vint32 idx <> Vint32 (Int.repr 255) ->
    0 <= Int.unsigned idx < MAX_OBJ_NUM ->
    can_change_aop P ->
    absinfer sch
      (<|| s1 ?? (sobjcre_set_hold (| Vint32 idx :: nil |) ;; s0) ||>  ** HObjs objs ** P) 
      (<|| s0 ||> ** HObjs (set objs idx (objholder, attr)) ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma sobjcre_absimp_hold_kobj:
  forall sch P idx attr objs s0,
   get objs idx = Some (objholder, attr) ->
   Vint32 idx <> Vint32 (Int.repr 255) ->
   0 <= Int.unsigned idx < MAX_OBJ_NUM ->
    can_change_aop P ->
    absinfer sch
      (<|| sobjcre_hold_kobj (| Vint32 idx :: nil |) ;; s0  ||>  ** HObjs objs ** P)
      (<|| s0 ||> ** HObjs objs ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma sobjcre_absimp_hold_kobj_abt:
  forall sch P idx objs s0,
   ~(exists attr, get objs idx = Some (objholder, attr)) ->
   Vint32 idx <> Vint32 (Int.repr 255) ->
   0 <= Int.unsigned idx < MAX_OBJ_NUM ->
    can_change_aop P ->
    absinfer sch
      (<|| sobjcre_hold_kobj (| Vint32 idx :: nil |) ;; s0  ||>  ** HObjs objs ** P)
      (<|| ABORT ||> ** HObjs objs ** P).
Proof.
   intros.
   simpljoin.
  assert (Hc: can_change_aop (HObjs objs ** P)).
  can_change_aop_solver.
  eapply absinfer_trans; try eapply absinfer_seq_abt; eauto.
  eapply absinfer_seq; eauto.
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma sobjcre_absimp_create_err:
  forall sch idx P objs attr s0,
    get objs idx = Some (objholder, attr) ->
    Vint32 idx <> Vint32 (Int.repr 255) ->
    0 <= Int.unsigned idx < MAX_OBJ_NUM ->
    can_change_aop P ->
    absinfer sch
      (<|| sobjcre_create_err (| Vint32 idx :: Vnull :: nil |) ?? s0 ||>  ** HObjs objs ** P) 
      (<|| END (Some (Vint32 Int.mone)) ||> ** HObjs (set objs idx (objnull, attr)) ** P).
Proof.
  infer_solver 0%nat.
Qed.

Lemma sobjcre_absimp_create_succ:
  forall sch idx P ptr objs attr sattr s0,
    get objs idx = Some (objholder, attr) ->
    Vint32 idx <> Vint32 (Int.repr 255) ->
    0 <= Int.unsigned idx < MAX_OBJ_NUM ->
    can_change_aop P ->
    absinfer sch
      (<|| s0 ?? sobjcre_create_succ (| Vint32 idx :: Vptr ptr :: Vint32 sattr :: nil |) ||>  ** HObjs objs ** P) 
      (<|| END (Some (Vint32 idx)) ||> ** HObjs (set objs idx (objid ptr, sattr)) ** P).
Proof.
  infer_solver 1%nat.
Qed.

Lemma service_obj_create_Proof: 
  forall tid vl p r, 
    Some p =
      BuildPreA' os_api service_obj_create sobjcreapi vl OSLInv tid init_lg ->
    Some r =
      BuildRetA' os_api service_obj_create sobjcreapi vl OSLInv tid init_lg ->
    exists t d1 d2 s,
      os_api service_obj_create = Some (t, d1, d2, s) /\
        {|OS_spec_ext, GetHPrio, OSLInv, I, r, Afalse|} |- tid {{p}} s {{Afalse}}.
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  do 3 (destruct v'; try apply absabort_rule).
  rename v into vr_idx.
  rename v0 into vr_cre.
  rename i into vkatt.
  rename i0 into vsatt.

  hoare forward prim.
  unfold AOBJ.
  unfold AObjs.
  hoare unfold.
  hoare forward.
  sep cancel Aop.
  sep cancel Aisr.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aie.
  sep cancel p_local.
  sep cancel AObjArr.
  eauto.
  pure_auto.
  unfold retpost. introv Hsat.
  inverts Hsat; sep pauto.
  introv Hsat.
  sep destruct Hsat.
  destruct Hsat as [Hsat | Hsat];
   try (sep destruct Hsat;
  eexists; sep cancel p_local; simpl; auto).

  intros.
  sep pauto. sep cancel p_local. sep auto.

  unfold getFreeObjIdxPost.
  unfold getFreeObjIdxPost'.
  unfold getasrt.
  hoare unfold.
  rename v'24 into objs.
  eapply backward_rule1.
  introv Hsat.
  eapply disj_split in Hsat; eapply adisj_intro;
  destruct Hsat as [Hsat | Hsat]; [left; eauto | right; eauto].
  hoare forward.
  2: {
    (* ObjArr_full_P *)
    hoare unfold.
    inverts H10.
    (* idx ′ =ₑ 〈 long 〉 y ′;ₛ *)
    hoare forward.
    hoare_lifts_trms_pre Aop.
    eapply assign_rule_lvar.
    split; sep pauto.
    intros.
    eapply cast_rv_tint8_tint32.
    symbolic_execution.
    simpl; auto.
    apply assign_type_match_true; simpl; auto.

    intros.
    sep pauto. sep cancel p_local. sep pauto.

    (* If (idx ′ ==ₑ ′ 255) *)
    hoare forward.
    rewrite Int.eq_true.
    hoare unfold.
    hoare_assert_pure (length v'27 = ∘ (MAX_OBJ_NUM)).
    {
      get_hsat Hsat.
      sep_lifts_trms_in Hsat AObjArr.
      eapply aobjarr_len_frm in Hsat; eauto.
    }
    eapply pure_split_rule'; introv Hlen.
    lets Hget_full: obj_get_not_null H H1 Hlen.
    rewrite Hlen in Hget_full.
    change (Z.of_nat ∘ MAX_OBJ_NUM) with MAX_OBJ_NUM in *.
   hoare_lifts_trms_pre (Aop, absobjs).
   assert (Hv: vr_idx =  V$ 255 \/ vr_idx <>  V$ 255) by tauto.
    destruct Hv as [Hv | Hv].
    2:{ 
        eapply abscsq_rule.
       apply noabs_oslinv.
       eapply sobjcre_absimp_get_idx_abt; eauto.
      can_change_aop_solver.
      eapply absinfer_eq.
      apply absabort_rule.
      }
(*     hoare_lifts_trms_pre (Aop, absobjs). *)
    subst.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply sobjcre_absimp_get_idx; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    instantiate (1:= Afalse).
     eapply abscsq_rule.
    apply noabs_oslinv.
    eapply sobjcre_absimp_idxerr; eauto.
    can_change_aop_solver.
    eapply absinfer_eq.
    hoare forward prim.
    unfold AOBJ.
    unfold AObjs.
    sep pauto; eauto.
    sep cancel AObjArr.
    sep cancel tcbllsegobjaux.
    sep cancel p_local.
    eauto.
    pure_auto.
    hoare forward.
    hoare forward.
    rewrite Int.eq_true; simpl val_inj.
    hoare_split_pure_all.
    destruct H9; tryfalse.
  }
  (* nth_ObjArr_free_P *)
    hoare unfold.
    inverts H10.
    rename v'28 into idx.
    hoare_assert_pure (0 <= idx < MAX_OBJ_NUM).
  {
    get_hsat Hsat. 
    sep_lifts_trms_in Hsat AObjArr.
    eapply nth_ObjArr_free_P_range; eauto.
  }
  eapply pure_split_rule'; introv Hy_range.
  (* idx ′ =ₑ 〈 long 〉 y ′;ₛ *)
  hoare forward.
  hoare_lifts_trms_pre Aop.
  eapply assign_rule_lvar.
  split; sep pauto.
  intros.
  eapply cast_rv_tint8_tint32. 
  symbolic_execution.
  clear -Hy_range.
  unfold MAX_OBJ_NUM in *.
  change (Byte.max_unsigned) with 255.
  int auto. destruct (idx <=? 255) eqn: eq1; auto with zarith.
  simpl; auto.
  apply assign_type_match_true; simpl; auto.

  intros.
  sep pauto. sep cancel p_local. sep pauto.

  assert (Hif_false: Int.eq ($ idx) ($ 255) = false). 
  {
    clear -Hy_range.
    unfold MAX_OBJ_NUM in *.
    int auto.
  }
  hoare forward. 
  pure_auto.
  rewrite Hif_false.
  simpl val_inj.
  instantiate (1:=Afalse).
  hoare unfold. tryfalse.
  hoare forward.
  hoare_split_pure_all.
  clear H9.
  assert (Hif_false': Vint32 ($ idx) <> Vint32 ($ 255)).
  { lets Hif_false': semacc_int_eq_false Hif_false.
     pure_auto.
   }
  assert (Hrgn: Int.ltu ($ idx) Int.zero = false /\ Int.ltu ($ idx) ($ MAX_OBJ_NUM) = true).
  { clear - Hy_range.
     unfold MAX_OBJ_NUM in *.
     int auto.
   }
  destruct Hrgn as (Hrgn1 & Hrgn2).
  (* efield (obj_arr ′ [os_code_defs.idx ′]) ptr =ₑ 〈 OS_EVENT ∗ 〉 service_obj_create.PlaceHolder;ₛ *)
  rename v'27 into objvll.
 hoare_assert_pure (length objvll = (∘ (MAX_OBJ_NUM))).
  { get_hsat Hsat.
    sep_lifts_trms_in Hsat AObjArr.
     eapply aobjarr_len_frm; eauto.  }
  eapply pure_split_rule'; introv Hlen.
  hoare_lifts_trms_pre (Aop, AObjArr).
  eapply backward_rule1.
  introv Hsat.
  eapply AObjArr_unfold_any_idx_frm with (idxv:=Z.to_nat (Int.unsigned ($ idx))).
  sep cancel AObjArr.
  eauto.
  rewrite Hlen.
  eapply obj_rgn_idx_lt; eauto.

  destruct Hy_range as (Hrgn_lt0 & Hrgn_lt1).
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  simpljoin.
  rename v'28 into objvl.
  lets Hls: obj_corr H H12 Hrgn1.
  destruct Hls as (oid_opt & att & Hget & Hvatt & Hcs).
  apply Int.unsigned_range_2.

  rewrite Int.unsigned_repr in *;
  try solve [clear -Hrgn_lt0 Hrgn_lt1; unfold MAX_OBJ_NUM in *; int auto].
  assert (Hget_null:
            exists att, get objs ($ idx) = Some (objnull, att) /\ V_ObjPtr objvl = Some Vnull).
  {
    eapply obj_getnull; eauto.
  }
  destruct Hget_null as (satt & Hget_null & Hvnull).
  assert (Hidx_eq: Int.unsigned ($ idx) = idx).
  {
    rewrite Int.unsigned_repr in *;
    try solve [clear -Hrgn_lt0 Hrgn_lt1; unfold MAX_OBJ_NUM in *; int auto].
   }


     hoare_lifts_trms_pre (Aop, absobjs).
    assert (Hv: vr_idx = Vint32 ($ idx) \/ vr_idx <> Vint32 ($ idx)) by tauto.
    destruct Hv as [Hv | Hv].
    (* vr_idx <> Vint32 ($ idx) *)
    2: {
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply sobjcre_absimp_get_idx_abt; eauto.
      right. do 2 eexists. splits; eauto.
      rewrite Hidx_eq; auto.
      can_change_aop_solver.
      eapply absinfer_eq.
      apply absabort_rule.
    }
    subst.
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply sobjcre_absimp_get_idx; eauto.
    right. do 2 eexists. splits; eauto.
    rewrite Hidx_eq; auto.
    can_change_aop_solver.
    eapply absinfer_eq.

    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply sobjcre_absimp_set_hold; eauto.
    rewrite Hidx_eq; auto.
    can_change_aop_solver.
    eapply absinfer_eq.

   lets Hsplit : H9.
   eapply new_array_type_vallist_match_split in Hsplit; eauto.
  destruct Hsplit as (Hsp1 & Hsp2 & Hsp).
  lets Hvl: struct_type_vallist_match_elim_2 Hsp.
  destruct Hvl as (vatt & vp & Heq). subst.
  inverts Hvnull.
  inverts Hvatt.
  rewrite Hget_null in Hget; inverts Hget.

    (* actual assign *)
  unfold service_obj_create.PlaceHolder.
  hoare forward.
  hoare_assign_array_struct.
  { unfold AOSTCBPrioTbl.
     introv Hsat.
     eapply cast_rv_tptr.
     eapply addrof_gvar_rv.
     apply astar_l_anotinlenv_intro.
     sep cancel (Agvarenv' OSPlaceHolder).
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
                           ((satt, long)
           :: (katt, Int16u) :: (idx, long) :: (y, char_t) :: (p, OS_EVENT ∗) :: nil)).
     simpl; pure_auto; tryfalse.
     rewrite Hlenv in Hf.
     pure_auto.
    }
    simpl; auto.
   }
  eapply backward_rule1.
  introv Hsat.
  eapply AObjArr_select_sn_ex_strong.
  exists v'18 (Z.to_nat idx) v'23 v'24 v'27.
  exists (Vint32 att :: Vptr vhold_addr :: nil).
  sep pauto; eauto.
  rewrite <- Hlen.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.
  eapply new_array_type_vallist_match_compose_struct; auto.
  hoare forward prim.
  unfold AOBJ.
  unfold AObjs.
  sep cancel p_local.
  sep normal.
  sep eexists.
  sep cancel tcbllsegobjaux.
  sep_lifts_trms ObjArray_P.
  sep cancel absobjs.
  eapply astar_l_apure_intro;
  [idtac |
    eapply ObjArray_P_hold_for_update_to_hold'; eauto;
    try solve [rewrite <- Hidx_eq; apply Int.unsigned_range_2];
    unfolds; simpl; eauto ].
  unfold update_nth_val.
  sep pauto; eauto.
  eapply objref_distinct_null_holder_preserve; eauto.
  eapply OBJ_AUX_P_null_holder_preserve; eauto.
  eapply RH_OBJ_ECB_P_set_to_hold; eauto.
  pure_auto.
  (* p ′ =ᶠ kernel_obj_create (·katt ′·);ₛ *)
  change (Vint32 vkatt :: vr_cre :: nil) with ((Vint32 vkatt :: nil) ++ (vr_cre :: nil)).
  hoare forward.
  pure_auto.
  sep cancel Aop.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel p_local.
  eauto.
  pure_auto.
  unfold retpost. introv Hsat.
  inverts Hsat; sep pauto.
  get_hsat Hsat. sep destruct Hsat.
  sep split in Hsat. simpljoin1. pure_auto.
  pure_auto.

  intros. sep auto. sep cancel p_local. simpl; auto.
  intros. sep auto. sep cancel p_local. simpl; auto.

  unfold KObjCreatePost.
  unfold KObjCreatePost'.
  unfold getasrt.
  hoare unfold.
  inverts H11.
  rename v'31 into vr_cre.
  rename H19 into Hvp_neq.

  (* ENTER_CRITICAL;ₛ *)
  hoare forward prim.
  unfold AOBJ.
  unfold AObjs.
  hoare unfold.
  rename v'51 into objs'.
  hoare_lifts_trms_pre (Aop, absobjs).
  assert (Hhold: (exists attr, get objs' ($ idx) = Some (objholder, attr)) \/
                          ~(exists attr, get objs' ($ idx) = Some (objholder, attr) )) by tauto.
  destruct Hhold as [Hhold | Habt].
   2: {
      eapply abscsq_rule.
      apply noabs_oslinv.
      eapply sobjcre_absimp_hold_kobj_abt; eauto.
      rewrite Hidx_eq; auto.
      can_change_aop_solver.
      eapply absinfer_eq.
      apply absabort_rule.
    }
   destruct Hhold as (attr & Hget').
    eapply abscsq_rule.
    apply noabs_oslinv.
    eapply sobjcre_absimp_hold_kobj; eauto.
    rewrite Hidx_eq; auto.
    can_change_aop_solver.
    eapply absinfer_eq.

  rename v'50 into objvll.
 hoare_assert_pure (length objvll = (∘ (MAX_OBJ_NUM))).
  { get_hsat Hsat.
    sep_lifts_trms_in Hsat AObjArr.
     eapply aobjarr_len_frm; eauto.  }
  eapply pure_split_rule'; introv Hlen'.
  hoare_lifts_trms_pre (Aop, AObjArr).
  eapply backward_rule1.
  introv Hsat.
  eapply AObjArr_unfold_any_idx_frm with (idxv:=Z.to_nat (Int.unsigned ($ idx))).
  sep cancel AObjArr.
  eauto.
  rewrite Hlen'.
  eapply obj_rgn_idx_lt; eauto.

  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  simpljoin.
  rename v'55 into objvl'.
  lets Hls: obj_corr H11 H27 Hrgn1.
  destruct Hls as (oid_opt & att' & Hget & Hvatt & Hcs').
  apply Int.unsigned_range_2.

  lets Hsplit : H18.
   eapply new_array_type_vallist_match_split in Hsplit; eauto.
  destruct Hsplit as (Hsp1' & Hsp2' & Hsp').
  lets Hvl: struct_type_vallist_match_elim_2 Hsp'.
  destruct Hvl as (vatt & vp & Heq). subst.
  inverts Hvatt.
  rewrite Hget' in Hget; inverts Hget.
  assert (Hvp: vp = Vptr vhold_addr).
  { clear -Hcs'.
     unfold V_ObjPtr in *. simpl nth_val in *.
     destruct Hcs' as [ | [ | ] ]; simpljoin; tryfalse.
     inverts H0; auto.
   }
  subst.

  (* efield (obj_arr ′ [os_code_defs.idx ′]) ptr =ₑ p ′;ₛ *)
  rewrite Hidx_eq in *.
  hoare forward.
  hoare_assign_array_struct.
  pure_auto.
  rename v'52 into locmp.
  rename v'53 into ptrmp.
   hoare_assert_pure (get locmp tid = Some v'32 /\ get ptrmp tid = Some vr_cre).
   { get_hsat Hsat.
      unfold tcbllsegobjaux in Hsat.
      sep_lifts_trms_in Hsat (llsegobjaux, AOSTCBList, p_local).
      eapply tcbllsegobjaux_split3_join2_frm'' in Hsat; eauto.
      sep normal in Hsat.
      sep destruct Hsat.
      sep split in Hsat.
      substs.
      split.
      eapply join_get_r; eauto.
      eapply join_sig_get; eauto.
      eapply join_get_r; eauto.
      eapply join_sig_get; eauto.
    }
   eapply pure_split_rule'; introv Hget_lp.
   destruct Hget_lp as (Hloc & Hptr).

  destruct H17 as [Hnull | ((pb & pi) & Hp)]; subst.
  destruct H16; simpljoin; tryfalse.
  (* true If (p ′ ==ₑ NULL) *)
  hoare forward.
  pure_auto.
  pure_auto.
  hoare unfold.
  hoare_lifts_trms_pre (Aop, absobjs).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply sobjcre_absimp_create_err; eauto.
  rewrite Hidx_eq; auto.
  can_change_aop_solver.
  eapply absinfer_eq.
  (*  *)
  hoare forward prim.
  unfold AOBJ.
  unfold AObjs.
  sep cancel p_local.
  sep normal.
  sep eexists.
  sep cancel tcbllsegobjaux.
  sep cancel absobjs.
  eapply AObjArr_select_sn_ex_strong.
  exists v'45 (Z.to_nat idx) v'50 v'51 v'54.
  exists (Vint32 att' :: Vnull :: nil).
  sep_lifts_trms ObjArray_P.
  eapply astar_l_apure_intro;
  [idtac |
    eapply ObjArray_P_hold_for_update_to_null'; eauto;
    try solve [rewrite <- Hidx_eq; apply Int.unsigned_range_2];
    unfolds; simpl; eauto ].
  unfold update_nth_val.
  sep pauto; eauto.
  eapply objref_distinct_objnull_preserve; eauto.
  lets Hsame: AuxLocMod.get_set_same Hloc.
  rewrite <- Hsame.
  eapply obj_aux_p_objnull_preserve; eauto.
  eapply RH_OBJ_ECB_P_null_preserve; eauto.
  rewrite <- Hlen'.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.
  eapply new_array_type_vallist_match_compose_struct; auto.
  pure_auto.
  hoare forward.
  hoare forward.
  hoare unfold.
  destruct H16; tryfalse.
  (* false If (p ′ ==ₑ NULL)  *)
  hoare forward.
  pure_auto.
  pure_auto.
  hoare unfold.
  tryfalse.
  instantiate (1:= Afalse).
  hoare forward.
  hoare unfold.
  (* efield (obj_arr ′ [os_code_defs.idx ′]) attr =ₑ satt′ ;ₛ *)
  hoare forward.
  hoare_assign_array_struct.
  (*  OSTCBCur ′ .. __OSTskLoc =ₑ ′ __Loc_normal;ₛ *)
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
  unfold isloc; auto.
  hoare_assign_aux.
  unfold isloc; auto.
  unfold isptr; auto.
  fold_aux_ptr_loc (V$ __Loc_normal) (Vnull).
  (*  *)
  hoare_lifts_trms_pre (Aop, absobjs).
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply sobjcre_absimp_create_succ; eauto.
  rewrite Hidx_eq; auto.
  unfold CurTid.
  can_change_aop_solver.
  eapply absinfer_eq.
  destruct H16; simpljoin; tryfalse.

  eapply backward_rule1.
  introv Hsat.
  eapply AObjArr_select_sn_ex_strong.
  exists v'45 (Z.to_nat idx) v'50 v'51 v'54.
  exists (Vint32 vsatt :: Vptr (pb, pi) :: nil).
  sep pauto; eauto.
  rewrite <- Hlen'.
  rewrite app_length.
  rewrite <- list_prop1.
  rewrite app_length.
  simpl length. auto.
  eapply new_array_type_vallist_match_compose_struct; auto.

  lets Hcre: obj_aux_cre H19 Hloc Hptr.
  destruct Hcre as (Hnfree & Hnref & Hkobj).

  hoare forward prim.
  unfold AOBJ.
  unfold AObjs.
  unfold p_local. unfold LINV, OSLInv.
  unfold tcbllsegobjaux.
  sep normal.
  sep eexists.
  sep cancel absobjs.
  sep cancel llsegobjaux.
  sep_lifts_trms ObjArray_P.
  eapply astar_l_apure_intro.
  2:{ eapply ObjArray_P_hold_for_update_to_tid_att'.
        rewrite H27; rewrite Z2Nat.id; auto.
        rewrite H27; rewrite Z2Nat.id; auto.
        rewrite <- Hidx_eq; apply Int.unsigned_range_2.
        rewrite <- Hidx_eq; apply Int.unsigned_range_2.
        3: eauto.
        unfolds; simpl; eauto.
        clear -Hvp_neq. pure_auto. }
  unfold update_nth_val.
  sep pauto; eauto.
  eapply objref_distinct_noref_ptr_preserve; eauto.
  eapply objdel_nodup_set_normal_loc_preserve;
  eapply objdel_nodup_set_null_preserve; eauto.
  eapply objcre_nodup_set_normal_loc_preserve;
  eapply objcre_nodup_set_null_preserve; eauto.
  eapply obj_aux_p_cre_preserve'; eauto.
  { introv Hf. destruct Hf as (t & Hneq & Htsk).
     eapply obj_aux_del in Htsk; eauto.
     destruct Htsk as (_ & Hf & _).
     eapply Hf; eauto.
   }
   { introv Hf. destruct Hf as (t & Hneq & Htsk).
      eapply objcre_nodup_cre_cre_contra; eauto.
    }
  eapply RH_OBJ_ECB_P_ptr_preserve; eauto.
  unfold isloc. unfold isptr. splits; auto.
  pure_auto.
  hoare forward.
Qed.
