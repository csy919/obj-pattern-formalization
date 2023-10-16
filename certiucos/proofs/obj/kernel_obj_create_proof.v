Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import kernel_obj_create.
Require Import kernel_obj_create_spec.

Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.

Require Import abs_step.
Require Import abs_infer_abt.

Require Import sem_common.
Require Import seplog_pattern_tacs.
Require Import objauxvar_lemmas.
Require Import objaux_pure. 

Require Import obj_common.
Require Import obj_common_ext.
Require Import freeevtlist_lemmas.

Require Import hoare_assign_tac_ext.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

(*********************** kernel obj cre **************************************)

Lemma kobjcre_absimp_no_free:
  forall P n sch s,
    can_change_aop P ->
    (Z.leb (Int.unsigned n) Int16.max_unsigned) = true ->
    absinfer sch
             ( <|| kobjcre (Vint32 n :: Vnull :: nil) ;; s ||> ** P)
             (<|| s ||> ** P).
Proof.
    intros.
    eapply absinfer_trans; try (eapply absinfer_seq_end; auto); eauto.
    eapply absinfer_seq; eauto.
    infer_solver 0%nat.
Qed.

Lemma kobjcre_absimp_no_free_abt:
  forall P n sch s v,
    can_change_aop P ->
    (Z.leb (Int.unsigned n) Int16.max_unsigned) = true ->
    v <> Vnull ->
    absinfer sch
             ( <|| kobjcre (Vint32 n :: v :: nil) ;; s ||> ** P)
             (<|| ABORT ||> ** P).
Proof.
    intros.
    eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
    eapply absinfer_seq; eauto.
    eapply absinfer_trans; try (eapply absinfer_choice1; eauto).
    eapply absinfer_abt; eauto.
    absimp_abt_solver.
Qed.

Lemma kobjcre_absimp_ecb_activate: 
  forall sch n sid s P els els' v,
    can_change_aop P ->
    (Int.unsigned n <=? Int16.max_unsigned) = true -> 
    get els sid = None -> 
    els' = (set els sid (abssem n, nil)) ->
    v = Vptr sid ->
    absinfer sch
             (<|| kobjcre (Vint32 n :: v :: nil) ;; s ||> ** HECBList els **  P)
             (<|| s ||> ** HECBList els' ** P).  
Proof.
  intros.
  assert (Hc: forall els, can_change_aop (HECBList els ** P))
   by (intros; can_change_aop_solver).
  substs.
  eapply absinfer_trans;
  try (eapply absinfer_seq_end; [idtac | idtac | eauto]; eauto).
  eapply absinfer_seq; eauto.
  infer_solver 1%nat.
Qed.

Lemma kobjcre_absimp_ecb_activate_abt:
  forall sch n sid s P els v,
    can_change_aop P ->
    (Int.unsigned n <=? Int16.max_unsigned) = true -> 
    get els sid = None -> 
    v <> Vptr sid ->
    absinfer sch
             (<|| kobjcre (Vint32 n :: v :: nil) ;; s ||> ** HECBList els **  P)
             (<|| ABORT ||> ** HECBList els ** P).  
Proof.
  intros.
  assert (Hc: can_change_aop (HECBList els ** P)) by (can_change_aop_solver).
  eapply absinfer_trans; try (eapply absinfer_seq_abt; eauto).
  eapply absinfer_seq; eauto.
  eapply absinfer_trans; try (eapply absinfer_choice2; eauto).
  eapply absinfer_abt; eauto.
  absimp_abt_solver.
Qed.

Lemma kernel_obj_create_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI new_os_internal kernel_obj_create vl logicl KObjCreatePre ct->
    Some r =
    BuildRetI new_os_internal kernel_obj_create vl logicl KObjCreatePost ct->
    exists t d1 d2 s,
      new_os_internal kernel_obj_create = Some (t, d1, d2, s) /\
      {|new_OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  rename v'1 into vsid.
  change ((Vint32 i :: nil) ++ (vsid :: nil)) with (Vint32 i :: vsid :: nil).
  subst logicl.

  hoare forward prim; pure_auto.
  hoare unfold.
  hoare forward; pure_auto.
  destruct v'1; hoare unfold.
(*   destruct H2 as [Hvull | ((vp_b & vp_i) & Hvp)]; subst. *)
  
(***************************** OSEventFreeList = Null **************************)
  lzh_hoare_if;
  match goal with
    | H: Vint32 (Int.notbool Int.one) <> Vint32 Int.zero /\
         Vint32 (Int.notbool Int.one) <> Vnull /\
         Vint32 (Int.notbool Int.one) <> Vundef |- _ =>
      destruct H as (H & _);
      unfold Int.notbool in H;
      rewrite Int.eq_false in H; eauto;
      tryfalse
    | _ => idtac
  end.

  assert (Hvret: vsid =Vnull \/ vsid <> Vnull) by tauto.
  destruct Hvret. 
  subst.
  2:{ (* vsid <> Vnull  *)
        eapply abscsq_rule.
        apply noabs_oslinv. 
        eapply kobjcre_absimp_no_free_abt; pure_auto.
        eapply absinfer_eq.
        eapply absabort_rule.
   }
  (* vsid =Vnull  *)
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply kobjcre_absimp_no_free; pure_auto.
  eapply absinfer_eq.

  lzh_hoare_if;
  match goal with
    | H: Vint32 (Int.notbool Int.one) <> Vint32 Int.zero /\
         Vint32 (Int.notbool Int.one) <> Vnull /\
         Vint32 (Int.notbool Int.one) <> Vundef |- _ =>
      destruct H as (H & _);
      unfold Int.notbool in H;
      rewrite Int.eq_false in H; eauto;
      tryfalse
    | _ => idtac
  end.
  hoare forward prim.
  unfold AOSEventFreeList.
  unfold ecbf_sll.
  sep cancel p_local.
  sep cancel AOBJ.
  simpl ecbf_sllseg.
  sep pauto.
  pure_auto.
  hoare forward.

(***************************** OSEventFreeList <> Null **************************)
  rename v'29 into pevent_block.
  rename v'25 into pevent_event_tbl.
  rename v'27 into pevent_event_ptbl.
  rename v'28 into petbl.

  unfold AOBJ. hoare normal pre. hoare_ex_intro.
  pure intro.
  hoare_assert_pure (EcbMod.get v'14 (pevent_block, Int.zero) = None). 
  {
    get_hsat Hsat.
    unfold AECBList in Hsat.
    sep normal in Hsat.
    destruct Hsat.
    get_hsat Hsat.
    sep split in Hsat.
    eapply semcre_ecblist_star_not_inh with (s:= s0); eauto.
    sep pauto.
  }
  hoare_split_pure_all.
  rename H4 into Hnone.

  unfold AECBList.
  hoare unfold.
  unfold tcbllsegobjaux.
  hoare_lifts_trms_pre (llsegobjaux, AOSTCBList, p_local).
  eapply backward_rule1. 
  introv Hsat.
  eapply tcbllsegobjaux_split3_join2_frm''; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.

  hoare_assert_pure (~ ptr_in_ecblist (Vptr (pevent_block, Int.zero)) v'24 v'1).
  { destruct H14; simpljoin.
     unfolds. introv Hf. unfold ptr_in_ecblist in Hf. destruct v'1; tryfalse.
     get_hsat Hsat.
    sep_lifts_trms_in Hsat (Astruct, ecbf_sllseg). 
    apply hd_not_in_evt_freelist in Hsat; auto.
   }
  hoare_split_pure_all. rename H20 into Hnptr.

   assert (Hv: pevent_event_tbl = (pevent_block, Int.zero +ᵢ  ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero)))))) by
      (simpl in H5; inverts H5; auto).
  rewrite Hv.
 assert (Hv': pevent_event_ptbl = (pevent_block, Int.zero +ᵢ  ($ 1 +ᵢ  ($ 4 +ᵢ ($ 8 +ᵢ ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero)))))))))  by
      (simpl in H6; inverts H6; auto).
  rewrite Hv'.
  (* If (OSEventFreeList ′ !=ₑ NULL) *)
  lzh_hoare_if;
  match goal with
    | H: Vint32 (Int.notbool Int.zero) = Vint32 Int.zero \/
         Vint32 (Int.notbool Int.zero) = Vnull |- _ =>
      unfold Int.notbool in H; simpl in H;
      rewrite Int.eq_true in H; auto;
      destruct H; tryfalse
    | _ => idtac
  end.
  (* OSEventFreeList ′ =ₑ 〈 OS_EVENT ∗ 〉 OSEventFreeList ′ .. OSEventListPtr *)
  hoare forward.
  go.
  pure_auto.

  (* new add *)
  hoare_assert_pure ((pevent_block, Int.zero) <> vhold_addr).
  { get_hsat Hsat.
     unfold AOSTCBPrioTbl in Hsat.
     sep normal in Hsat.
     sep destruct Hsat.
     sep_lifts_trms_in Hsat (vhold_addr, Astruct (pevent_block, Int.zero)).
     sep remember (1 :: 2 :: nil)%nat in Hsat.
     clear -Hsat.
     simpl Astruct in Hsat.
     sep normal in Hsat.
    sep_lifts_trms_in Hsat (pevent_block, vhold_addr).
    eapply pv_false;eauto.
    unfold array_struct. introv Hf; destruct Hf as [ | [ | ]]; simpljoin; tryfalse.
    unfold array_struct. introv Hf; destruct Hf as [ | [ | ]]; simpljoin; tryfalse.
  }
  hoare_split_pure_all. rename H20 into Hvp_neq.
  (* end of new add *)

  hoare_lifts_trms_pre (Astruct (pevent_block, Int.zero), OS_EVENT_TBL_SIZE, petbl, OSEventList, p_local,objaux_node).
  hoare remember (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: nil)%nat pre.
  (* If (ptr ′ !=ₑ NULL) *)
  lzh_hoare_if;
  match goal with
    | H: Vint32 (Int.notbool Int.zero) = Vint32 Int.zero \/
         Vint32 (Int.notbool Int.zero) = Vnull |- _ =>
      unfold Int.notbool in H; simpl in H;
      rewrite Int.eq_true in H; auto;
      destruct H; tryfalse
    | _ => idtac
  end.
    instantiate(1:= 
    Astruct (pevent_block, Int.zero) OS_EVENT
    (V$ OS_EVENT_TYPE_SEM
     :: Vint32 Int.zero :: Vint32 i :: Vnull :: x1 :: v'17 :: Vint32 Int.zero :: x4 :: nil) **
  Aarray
    (pevent_block, Int.zero +ᵢ  ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero)))))
    (Tarray char_t ∘ OS_EVENT_TBL_SIZE) INIT_EVENT_TBL **
  Aarray
    (pevent_block,
    Int.zero +ᵢ
    ($ 1 +ᵢ  ($ 4 +ᵢ  ($ 8 +ᵢ  ($ 4 +ᵢ  ($ 2 +ᵢ  ($ 1 +ᵢ  ($ 1 +ᵢ  Int.zero))))))))
    (Tarray char_t ∘ OS_EVENT_TBL_SIZE) INIT_EVENT_TBL **
  GV OSEventList @ OS_EVENT ∗ |-> (Vptr (pevent_block, Int.zero)) **
  p_local OSLInv ct
    (logic_val (V$ 1) :: logic_val (V$ __Loc_objcre) :: logic_val (Vptr (pevent_block, Int.zero)) :: nil) **
  objaux_node ct (V$ __Loc_objcre) (Vptr (pevent_block, Int.zero)) ** H20
  ).
  subst.
  (* ptr ′ .. OSEventType =ₑ ′ OS_EVENT_TYPE_SEM;ₛ *)
  hoare forward.
  hoare forward.
  pure_auto.
  hoare forward.

  (* OS_EventWaitListInit (­ ptr ′­);ₛ *)
  hoare forward.
  sep cancel Aisr.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aie.
  sep cancel Aop.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel p_local.
  eauto.
  change (Int.unsigned ($ OS_EVENT_TYPE_SEM)) with 3.
  unfold isptr.
  splits; auto.
  pure_auto.

  intros. sep auto.
  intros. sep auto.

  unfold OS_EventWaitListInitPost.
  unfold OS_EventWaitListInitPost'.
  unfold getasrt.

  pure intro.
  inverts H31.  (* eq. on logicl *) 
  (* ptr ′ .. OSEventListPtr =ₑ OSEventList ′;ₛ *)
  hoare forward.
  pure_auto.
  (* OSEventList ′ =ₑ ptr ′;ₛ *)
  hoare forward.
  (* OSTCBCur ′ .. __OSTskLoc =ₑ ′ __Loc_objcre;ₛ *)

  hoare_assign_aux.
  unfold isloc. auto.
  eapply forward_rule1.
  2:{ hoare_assign_aux.
        unfold isloc. auto. }
  introv Hsat.
  sep pauto.
  sep cancel Aop.
  unfold p_local. unfold LINV. unfold OSLInv.
  sep cancel CurTid.
  sep_lifts_trms_in Hsat (get_off_addr ct ptr_off).
  apply sep_combine_lemmas.PV_separate_rw_frm in Hsat.
  unfold objaux_node.
  sep auto.
  unfold isloc, isptr.
  splits; eauto.

  subst.
  hoare_lifts_trms_pre (Aop, absecblist).
  assert (Hvret: vsid = (Vptr (pevent_block, Int.zero)) \/ vsid <> (Vptr (pevent_block, Int.zero))) by tauto.
  destruct Hvret. 
  subst.
  2:{ (* vsid <> Vnull  *)
        eapply abscsq_rule.
        apply noabs_oslinv. 
        eapply kobjcre_absimp_ecb_activate_abt; pure_auto.
        eapply absinfer_eq.
        eapply absabort_rule.
   }
  (* vsid =Vnull  *)
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply kobjcre_absimp_ecb_activate; pure_auto.
  eapply absinfer_eq.
Ltac fold_aux' :=
  let Hsat := fresh in
  eapply backward_rule1;
   [ introv Hsat; eapply llsegobjaux_merge2_frm;
      [ sep cancel llsegobjaux; eapply llsegobjaux_merge_hd;
         [ sep cancel objaux_node; sep cancel llsegobjaux; eauto
         | eauto
         | eauto
         | eauto ]
      | eapply AuxLocMod.joinsig_set_set; eauto
      | eapply AuxPtrMod.joinsig_set_set; eauto ]
   |  ].
  fold_aux'.
  eapply join_lib.join_sig_set; eauto.
  eapply join_lib.join_sig_set; eauto.
  (* EXIT_CRITICAL;ₛ *)
    fold_AEventNode_r.
  hoare forward prim.
  sep cancel p_local.
  sep cancel tcbdllflag.
  unfold AOSEventFreeList.
  unfold ecbf_sll.
  unfold AECBList.
  sep pauto.
  sep cancel ecbf_sllseg.
  instantiate (5:= (((V$ OS_EVENT_TYPE_SEM
     :: Vint32 Int.zero
        :: Vint32 i :: Vnull :: x1 :: v'17 :: Vint32 Int.zero :: x4 :: nil), INIT_EVENT_TBL,INIT_EVENT_PTBL) :: v'5)).
  instantiate (4:= (DSem i) :: v'4).
  simpl evsllseg at 1.
  unfold AEventNode.
  unfold AOSEvent.
  unfold AEventData.
  unfold AOSEventTbl.
  unfold AOSPostEventTbl.
  unfold AOBJ.
  unfold AObjs in *.
  unfold tcbllsegobjaux.
  sep pauto; auto.
  sep cancel Aarray.
  sep cancel Aarray.
  sep cancel evsllseg.
  sep cancel llsegobjaux.
  sep cancel AObjArr.
  eauto.

  clear -H1.
  int auto.
  unfold V_OSEventListPtr. simpl. auto.
  eapply semcre_RL_Tbl_init_prop.
  unfolds; simpl; auto.
  eauto.
  unfold array_type_vallist_match.
  splits; pauto.
  eapply semcre_RL_Tbl_init_prop.
  unfold V_OSEventGrp; simpl; auto.
  auto.
  unfold array_type_vallist_match.
  splits; pauto.
  6:{ eapply semcre_ECBList_P; eauto. }
  6: { eapply semcre_RH_TCBList_ECBList_P; eauto. }
  eapply objdel_nodup_cre_preserve; eauto.
  eapply objcre_nodup_cre_preserve; eauto.
  eapply not_in_els_notcre; eauto.
  eapply obj_aux_cre_preserve; eauto.
  eapply join_get_r; eauto.
  eapply join_sig_get; eauto.
  lets Hf: Hnone.
  eapply not_in_els_notcre in Hf; eauto.
  introv Hf'; simpljoin. eapply Hf; eauto.
  lets Hf: Hnone.
  eapply not_in_els_notdel in Hf; eauto.
  introv Hf'; simpljoin. eapply Hf; eauto.
  eapply RH_OBJ_ECB_P_semcre_preserve; eauto.
  auto.
  pure_auto.
  (* RETURN *)
  assert (Hvp_neq': Vptr (pevent_block, Int.zero) <> Vptr vhold_addr).
  { clear -Hvp_neq. pure_auto. }
  hoare forward.
  Unshelve.
  exact Afalse. exact Afalse. trivial.
Qed.
