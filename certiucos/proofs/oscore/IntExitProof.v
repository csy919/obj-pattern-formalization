(**************************  uc/OS-II  *******************************)
(*************************** OS_CORE.C *******************************)
(**Proof of Internal Fucntion:  void OS_IntExit (int x)***)
(************************** Code:*************************************)
(***
void OS_IntExit(int x)
1   ENTER_CRITICAL;ₛ
2   x <-CHECKIS;ₛ
3   If(x ′ ==ₑ ′1)
    {
4     OSIntExitY ′ =ₑ OSUnMapTbl ′ [OSRdyGrp ′];ₛ
5     OSPrioHighRdy ′ =ₑ
6     (OSIntExitY ′ ≪ ′3) +ₑ OSUnMapTbl ′ [OSRdyTbl ′ [OSIntExitY ′]];ₛ
7     OSPrioCur ′ =ₑ OSTCBCur ′ → OSTCBPrio;ₛ
8     If(OSPrioHighRdy ′ !=ₑ OSPrioCur ′)
      {
9       OSTCBHighRdy ′ =ₑ OSTCBPrioTbl ′ [OSPrioHighRdy ′];ₛ
10      OSCtxSwCtr ′ =ₑ OSCtxSwCtr ′ +ₑ ′1;ₛ
11      SWITCH
      };ₛ
12    EXIT_CRITICAL;ₛ
13    RETURN
   };ₛ
14 EXIT_CRITICAL;ₛ
15 RETURN
****)

Require Import ucos_include.
Require Import OSIntExitPure.
Require Import oscore_common.
Require Import os_ucos_h.
Require Import symbolic_lemmas.
Require Import Lia.

Import DeprecatedTactic.

Require Import seplog_pattern_tacs. 

Open Scope code_scope.

Open Scope list_scope.

Open Scope Z_scope.
Lemma OSIntExit_proof:
    forall  vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OSIntExit
                  vl logicl OSIntExitPre ct->
      Some r =
      BuildRetI os_internal OSIntExit vl logicl OSIntExitPost ct->
      exists t d1 d2 s,
        os_internal OSIntExit = Some (t, d1, d2, s) /\
        {|OS_spec, GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof. 
  init spec.
  (*----------------en_crit---------------------*)
  pure intro.
  rename H2 into Hirange.
  rename H3 into Hisrinv.
  eapply backward_rule1.
  intros.
  sep lift 6%nat in H.
  apply disj_split in H.
  exact H.
  apply disj_rule.
  pure intro.
  assert (Htoy: invlth_isr' I 1 v'3 = Aemp \/ invlth_isr' I 1 v'3 = atoy_inv').
  {
    unfold invlth_isr'.
    destruct (leb 1 v'3);auto.
  }
  (* rename H2 into Htoy. *)
  unfolds in Hirange.
  destruct Hirange;subst v'4.
  eapply backward_rule1.
  intros.

  sep_lifts_trms_in H2 (AOSTCBList', AOSTCBFreeList', p_local).
  (* sep lifts (9::10::24::nil)%nat in H2. *)
  apply inv_change_aux in H2.
  exact H2.
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop, Aisr, Aie, Ais, Acs, Alvarmapsto).
  (* hoare lifts (25::21::22::23::24::26::nil)%nat pre. *)
  eapply encrit2_rule'.
  intros.
  exact H2.
  apply GoodI_I.  (* GoodI *)
  destruct Htoy;rewrite H2;go.
  Ltac p_local_go:=
  try solve [
    unfold p_local;
    unfold CurTid;
    unfold LINV;
    unfold OSLInv;
    go].
  (* p_local_go. *)
  (* p_local_go. *)

  (*---------------check is-------------------------*)
  eapply seq_rule.
  (* apply checkis_rule' with (v:=v') (lg:=(logic_val (V$ 1) :: nil)). *)
  apply checkis_rule' with (v:=v') (lg:=(logic_val (V$ 1) :: v'5)).
  intros.
  exact H2.
  apply GoodI_I. (* Good I *)
  destruct Htoy;rewrite H2.
  p_local_go.
  p_local_go.
  intros.
  sep auto.
  
  hoare forward.
  unfold is_length.
  destruct v'2;simpl;auto.
  unfold val_inj.
  unfold is_length.
  destruct v'2;simpl;auto.
  
  instantiate (1:= Afalse).
  pure intro.
  apply is_length_neq_zero_elim in H2.
  subst v'2.
  clear H3 H4.
  apply isr_is_prop_emp in H0.
  rename H0 into Hempisr.
  (*---------------get y------------------------*)
  
  hoare unfold.
  rename H3 into Hidle.
  unfold AGVars.
  unfold AOSUnMapTbl.
  hoare forward.
  rtmatch_solve.
  
  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H6.
  simpl.
  rtmatch_solve.
  
  (*--------------get highest prio--------------*)
  unfold AOSRdyTbl.
  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H3.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true)%Z.
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H4.
  apply Zle_is_le_bool.
  lia.
  auto.
  pure intro.
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H8.
  rewrite H9.
  apply Zle_bool_imp_le in H4.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'17) as X.
  destruct X;tryfalse.

  hoare forward.  
  rtmatch_solve.
  apply Zle_bool_imp_le in H4.
    
  rtmatch_solve.
  apply Zle_bool_imp_le in H4.



  sep lift 2%nat in H10.
  unfold OS_RDY_TBL_SIZE in H9.
  eapply GAarray_imp_length_P in H10.
  rewrite H10.
  simpl.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255)%Z);tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;auto.
  rtmatch_solve.

  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;intro;tryfalse.
  hoare unfold.
  hoare forward.
  go.
  hoare unfold.
 

  (*----check if current task is highest ready----*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H4 H12.
  apply Zle_bool_imp_le in Hran.
  
  eapply abscsq_rule';eauto.
  apply noabs_oslinv.
  eapply absinfer_choice1;eauto.
  destruct Htoy;rewrite H19;go.
  destruct Htoy;rewrite H19;go.

  hoare_forward_stmts_nsepauto.

  assert ( Int.unsigned ((x<<ᵢ$ 3)+ᵢ x0) <= Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H34.  
  rewrite H34;auto.
  assert ( Int.unsigned i5 <=? Byte.max_unsigned =true)%Z.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H34;auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x0) i5);auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x0) i5);simpl;auto.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3) +ᵢ x0) <= Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H35.  
  rewrite H35;auto.
  destruct H30;auto.

  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H35.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H36.
  eapply int_unsigned_le_z2nat_lt.
  auto.
  
  hoare forward;eauto.
  pure intro.

  lets Hinrtbl:unmap_inrtbl H2 H0 H3 H11;auto.

  lets Hhastid:prio_in_rtbl_has_tid H30 Hinrtbl.
  rewrite Int.unsigned_repr.
  split;try solve [lia].
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx0).
  lia.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx0).
  unfold Int.max_unsigned.
  lia.

  destruct Hhastid.

  eapply abscsq_rule';eauto.
  apply noabs_oslinv.
  unfold isched.
  eapply absinfer_seq;eauto.
  destruct Htoy;rewrite H38;go.
  2:apply absinfer_choice1;eauto.
  destruct Htoy;rewrite H38;go.
  destruct Htoy;rewrite H38;go.
  destruct Htoy;rewrite H38;go.
 
  
  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply sc_isched_step;eauto.
  destruct Htoy;rewrite H38;go.
  intros.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H37;eauto.
  
  instantiate (2:=  (v'44, Int.zero)).
  instantiate (3:= ((v'43
               :: v'39
                  :: x8
                     :: x7
                        :: Vint32 i7
                           :: Vint32 i6
                              :: Vint32 i5
                                 :: Vint32 i4
                                    :: Vint32 i3
                                       :: Vint32 i2 :: Vint32 i1 :: nil):: v'16) %list).
  instantiate (3:=v'14).
  unfold AOSTCBList.

  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel OSTCBList.
  unfold p_local in H38.
  unfold CurTid in H38.
  sep normal in H38.
  sep destruct H38.
  sep lifts (7::1::nil)%nat%list in H38.
  apply read_only_merge_vptr in H38.
  destruct H38.
  clear H39.
  apply read_only_split_vptr in H38.
  sep cancel 1%nat 1%nat.
  sep cancel OSTCBCur.
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.
  sep auto.
  eapply prio_neq_tid_neq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H37;eauto.
  clear -H33.
  destruct (Int.eq ((x<<ᵢ$ 3)+ᵢx0) i5);simpl in H33;auto.
  unfold Int.notbool in H33.
  int auto.
  instantiate (2:=(v'44, Int.zero)).
  sep auto.
  eauto.
  eauto.
  eauto.
  split;auto.
  go.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq;eauto.
  3:eapply absinfer_seq_end;eauto.
  destruct Htoy;rewrite H38;go.
  destruct Htoy;rewrite H38;go.
  destruct Htoy;rewrite H38;go.
  destruct Htoy;rewrite H38;go.
  
  hoare remember (1::2::18::nil)%nat%list pre.
  apply backward_rule1 with (<|| sched;; END None ||>  **
                                 
                                 ( A_dom_lenv ((os_code_defs.x, Int32u) :: nil) **
                                              LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil))**
                                 H38).
  intros.
  sep normal.
  auto.
  subst H38.
  eapply frame_rule' with (frm:=
     A_dom_lenv  ((os_code_defs.x, Int32u) :: nil)**
     LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) ).
  apply GoodI_I. (* GoodI *)
  simpl;auto.
  simpl;auto.
  sep auto.
  unfold p_local.
  eapply switch_rule' with (Px:=LINV OSLInv (v'44, Int.zero) (* init_lg *)(logic_val (V$1) :: v'5)).
  intros.
  sep cancel LINV.
  exact H38.
  intros.
  unfold SWINVt.
  unfold CurTid in H38.
  sep normal in H38.
  sep destruct H38.
  sep normal.
  exists x2.
  sep cancel 1%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists v'3.
  sep lifts (3::2::nil)%nat.
  eapply imp_isrclr.
  
  eapply simpl_inv_excrit'.
  unfold OSInv.
  unfold A_isr_is_prop.
  unfold AGVars.
  sep semiauto;eauto.
  sep cancel 1%nat 2%nat.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  sep cancel OSPlaceHolder.
  sep cancel ACNU.
  (* sep cancel 8%nat 1%nat. *)
  unfold AOSTCBList'.
  apply disj_split.
  left.
  sep normal.
  sep eexists.
  unfold AOSTCBFreeList'.
  sep lift 12%nat.
  apply disj_split.
  left.
  unfold TCBFree_Not_Eq.
  unfold AOSTCBFreeList in H38.
  sep normal.
  sep cancel tcbdllflag.
  sep auto;eauto.
  unfold tcbdllseg.
  sep cancel sll.
  sep cancel sllfreeflag.
  unfold1 dllseg.
  unfold node.
  sep auto;eauto.
  split;auto.
  go.
  intro;subst.
  
  sep lifts (1::7::nil)%nat in H38.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  intro;subst.
  sep lifts (1::7::nil)%nat in H38.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  simpl;auto.
  rewrite Int.repr_unsigned in H37.
  eauto.
  destruct_s s.
  simpl in H42;subst i10.
  simpl.
  auto.
  rewrite <- Hempisr.
  auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.
  auto.
  simpl in H17.
  clear -H17;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  destruct_s s.
  
  simpl in H42,H40.
  subst.
  simpl.
  rewrite Hempisr.
  unfolds.
  intros.
  unfold empisr;auto.
  
  intros.
  unfold SWPRE_NDEAD.
  split.
  unfold SWPRE.
  rewrite Int.unsigned_repr in H37.
  rewrite H37 in *.
  exists x1.
  sep lift 2%nat.
  apply imp_isrclr.
  
  sep remember (6::7::8::9::10::nil)%nat in H38.
  assert(s|=AOSTCBList v'12 (Vptr (v'44, Int.zero)) v'14 ((v'43
              :: v'39
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil) :: v'16) v'17 (v'44, Int.zero) v'20 ** H39).
  unfold AOSTCBList.
  sep normal.
  clear HeqH39.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.
  split;auto.
  go.
  clear H38.
  subst H39.
  rewrite <- Hempisr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 4%nat 2%nat.
  sep_lifts_trms_in H40 (AOSTCBList, Aabsdata abstcblsid, CurTid).
  (* sep lifts (1::27::13::nil)%nat in H39. *)
  unfold CurTid in H40.
  eapply highest_rdy_eq in H40;eauto.
  clear -Hran.
  remember ( ((x<<ᵢ$ 3) +ᵢ  x0) ) as X.
  clear HeqX.
  int auto.

  exists v'20.
  sep auto.
  clear -H15 H17.
  simpl in H17.
  mytac.
  inverts H.
  assert (join (sig (v'44, Int.zero) x2) x1 v'42).
  auto.
  clear H1.
  clear -H H15.
  assert (get (sig (v'44, Int.zero) x2) (v'44, Int.zero) = Some x2). 
  apply map_get_sig.
  eapply join_get_l in H;eauto.
  eapply join_get_r in H15;eauto.
  unfolds;eauto.
  p_local_go.
  intros.
  sep cancel 1%nat 1%nat.
  simpl;auto.
  intros.
  exact H19.
  apply disj_rule.
  eapply backward_rule1.
  instantiate (1:= (<|| END None ||>  **
                        A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** 
                        Aisr (isrupd v'0 v'3 false) **
                        Aie false **
                        Ais (v'3 :: nil) **
                        Acs (false :: nil) **
                        LV os_code_defs.x @ Int32u |-> is_length (0%nat :: nil) ** OSInv ** invlth_isr' I 1 v'3 ** 
                        p_local OSLInv (v'44, Int.zero) (logic_val (V$ 1) :: v'5))).  
  intros.
  ssplit_apure_in H19.
  unfold SWINVt in H19.
  unfold SWINV in H19.  
  sep normal in H19.
  sep destruct H19.
  sep lifts (2::3::9::7::nil)%nat in H19.
  apply invlth_isr_invlth_isr'_imp in H19.
  sep cancel 1%nat 8%nat.
  sep cancel 1%nat 8%nat.
  unfold p_local.
  unfold CurTid.
  sep auto.
  rewrite Hempisr;auto.

  unfold OSInv.
  hoare normal pre.
  pure intro.
  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop, Aop, A_dom_lenv, Aie, Acs).
  (* hoare lifts (21::23::18::19::20::22::24::nil)%nat pre. *)
  eapply backward_rule1.
  intros.  
  apply elim_a_isr_is_prop' in H30.
  exact H30.
  rewrite Hempisr.
  unfolds;simpl;auto. 
  hoare lifts (3::1::5::2::6::nil)%nat pre.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I. (* GoodI *)
  destruct Htoy;rewrite H30;pauto.
  (* p_local_go. *)
  (* p_local_go. *)
  apply ret_rule'.
  intros.
  assert (v'60 = (v'44, Int.zero)).
  sep_lifts_trms_in H30 (p_local, AOSTCBList').
  (* sep lifts (26::15::nil)%nat in H30. *)
  eapply p_local_ostcblist_eq_ct in H30.
  auto.
  subst v'60. 
  sep normal.
  do 4 eexists.
  exists v'3.
  exists (V$ 1).
  exists v'5. (* added by CNU *) 
  sep split.
  3:eauto.
  sep normal.
  sep split.
  sep cancel (Alvarmapsto os_code_defs.x).
  (* sep cancel 24%nat 2%nat. *)
  left.
  sep lift 8%nat.
  apply disj_split.
  left.
  unfold AOSTCBPrioTbl in H30.
  unfold AGVars in H30.
  sep normal in H30.
  sep destruct H30.
  sep normal.
  sep eexists.
  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel p_local.
  sep cancel ACNU. (* added by CNU *)
  sep semiauto;eauto.
  
  rewrite Hempisr;unfolds;simpl;auto.
  sep split in H30.
  auto.

  lets Hinrtbl:unmap_inrtbl H2 H0 H3 H11;auto.
  pure intro.
  lets Hhastid:prio_in_rtbl_has_tid H30 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx0).
  split;lia.
  destruct Hhastid.
  hoare lifts (2::18::3::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  unfold isched.
  
  instantiate (1:= <|| ASSUME nsc;;END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H36).
  apply absinfer_seq;auto.
  destruct Htoy;subst H36;rewrite H37;go. 
  destruct Htoy;subst H36;rewrite H37;go. 
  
  apply absinfer_choice2;auto.
  destruct Htoy;subst H36;rewrite H37;go. 
  destruct Htoy;subst H36;rewrite H37;go. 
  
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| spec_done None;;END None||>  **
                        LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
                        A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H36).

  eapply nsc_isched_step with (t:=x1) (ct:=(v'44, Int.zero));eauto.
  subst H36.
  destruct Htoy;rewrite H36;go.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H35;auto.
  instantiate (2:=  (v'44, Int.zero)).
  instantiate (2:=  (v'43
               :: v'39
                  :: x8
                     :: x7
                        :: Vint32 i7
                           :: Vint32 i6
                              :: Vint32 i5
                                 :: Vint32 i4
                                    :: Vint32 i3
                                       :: Vint32 i2 :: Vint32 i1 :: nil):: v'16).
  instantiate (2:=v'14).
  instantiate (2:=v'12).
  subst H36.
  unfold p_local in H37.
  unfold CurTid in H37.
  sep normal in H37.
  sep destruct H37.
  unfold AOSTCBList.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel OSTCBCur.
  
  sep cancel OSTCBCur.
  sep cancel OSTCBList.
  sep cancel (Aabsdata abstcblsid).
  (* sep cancel 29%nat 9%nat. *)
  sep split;eauto.
  split;auto.
  go.
  subst H36.
  sep auto.
  eapply prio_eq_tid_eq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H35;eauto.
  clear -H33.
  destruct (Int.eq ((x<<ᵢ$ 3)+ᵢx0) i5);simpl in H33;destruct H33;auto;tryfalse.
  instantiate (2:=(v'44, Int.zero)).
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <||END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H36).
  apply absinfer_seq_end;auto.
  destruct Htoy;subst H36;rewrite H37;go.
  destruct Htoy;subst H36;rewrite H37;go.
  
  apply backward_rule1 with ( <|| END None ||>  ** OSInv ** invlth_isr' I 1 v'3 ** Aie false ** Ais (v'3::nil) ** Acs (false::nil) ** Aisr empisr ** LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
                                  A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** p_local OSLInv (v'44, Int.zero) (* init_lg *) (logic_val (V$ 1) :: v'5)). 
  
  intros.
  subst H36.
  sep remember (6::7::8::9::10::nil)%nat in H37.
  assert(s |= AOSTCBList v'12 (Vptr (v'44, Int.zero)) v'14 ( (v'43
              :: v'39
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil)  :: v'16) v'17 (v'44, Int.zero) v'20 ** H36).
  unfold AOSTCBList.
  sep normal.
  clear HeqH36.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.
  split;auto.
  go.
  clear H37.
  subst H36.
  unfold OSInv.
  unfold A_isr_is_prop.
  sep lifts (1::15::16::17::nil)%nat in H38.
  rewrite <- inv_change_aux in H38.
  sep semiauto;eauto.
  sep cancel 3%nat 2%nat.
  sep cancel AOSTCBList'.
  (* sep cancel 1%nat 6 %nat. *)
  sep cancel AOSTCBFreeList'.
  (* sep cancel 1%nat 6%nat. *) 
  exact H38.  
  simpl;auto.
  rewrite <- Hempisr;auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.
  
  simpl in H17.
  clear -H17;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  rewrite H39, H41.
  rewrite Hempisr;unfolds;simpl;auto.
  unfold OSInv.
  hoare normal pre.
  pure intro.
  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop, Aop, invlth_isr', Aie, Acs).
  (* hoare lifts (24::22::18::19::20::21::23::nil)%nat pre. *) 
  eapply backward_rule1.
  intros.
  apply elim_a_isr_is_prop' in H36.
  exact H36.
  unfolds;simpl;auto.
  hoare lifts (3::1::5::2::6::nil)%nat pre.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I. (* GoodI *)
  destruct Htoy;rewrite H36;go.
  (* p_local_go. *)
  (* p_local_go. *)
  apply ret_rule'. 
  intros.
  sep normal.
  do 4 eexists.
  exists v'3.
  exists (V$ 1).
  exists v'5.  (* added by CNU *) 
  assert (v'60 = (v'44, Int.zero)). 
  sep_lifts_trms_in H36 (p_local, AOSTCBList'). 
  (* sep lifts (26::15::nil)%nat in H35. *) 
  eapply p_local_ostcblist_eq_ct in H36.
  auto.
  subst v'60. 
  sep split.
  3:eauto.
  apply disj_split.
  left.
  sep normal.
  sep semiauto;eauto.
  (* sep cancel p_local. *)
  left.
  sep normal.
  sep eexists.
  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel invlth_isr'.
  sep cancel ACNU. (* added by CNU *) 
  sep semiauto;eauto.
  rewrite H48;auto.
  rewrite Hempisr;unfolds;simpl;auto.
  sep split in H36;auto.
  
  hoare forward.
  pure intro.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  apply absinfer_choice2;eauto.
  destruct Htoy;rewrite H3;p_local_go.
  destruct Htoy;rewrite H3;p_local_go.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I. (* GoodI *)
  destruct Htoy;rewrite H3;p_local_go.
  apply ret_rule'.
  intros.
  sep normal.
  do 4 eexists.
  exists v'3.
  exists (V$ 1).
  exists v'5. (* added by CNU *) 
  sep split.
  3:eauto.

  apply disj_split.
  left.
  sep normal.
  sep lift 8%nat.
  apply disj_split.
  left.
  sep lifts (7::8::9::10::nil)%nat in H3.
  eapply inv_change_aux in H3.
  sep normal.
  sep eexists.
  sep cancel AOSTCBList'.
  sep cancel AOSTCBFreeList'.
  sep cancel p_local.
  sep auto.
  sep split in H3;auto.
  
  (*----------cur dead------------*)
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop, Aisr, Aie, Ais, Acs, Alvarmapsto x). 
  (* hoare lifts (23::19::20::21::22::25::nil)%nat pre. *)
  eapply encrit2_rule'.
  intros.
  exact H2.
  apply GoodI_I.  (* GoodI *)
  destruct Htoy;rewrite H2;go.
  (* p_local_go. *)
  (* p_local_go. *)
  (* check is*) 
  eapply seq_rule.
  apply checkis_rule' with (v:=v') (lg:=(logic_val ( V$ 0) :: (* nil *) v'5)).
  intros.
  exact H2.
  apply GoodI_I. (* Good I *)
  destruct Htoy;rewrite H2.
  p_local_go.
  p_local_go.
  intros.
  sep auto.
  
  hoare forward.
  unfold is_length.
  destruct v'2;simpl;auto.
  unfold val_inj.
  unfold is_length.
  destruct v'2;simpl;auto.
  
  instantiate (1:= Afalse).
  pure intro.
  apply is_length_neq_zero_elim in H2.
  subst v'2.
  clear H3 H4.
  apply isr_is_prop_emp in H0.
  rename H0 into Hempisr.
  (*---------------get y------------------------*)
  
  hoare unfold.
  rename H3 into Hidle.
  unfold AGVars.
  unfold AOSUnMapTbl.
  hoare forward.
  rtmatch_solve.
  
  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H6.
  simpl.
  rtmatch_solve.
  
  (*--------------get highest prio--------------*)
  unfold AOSRdyTbl.
  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H3.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true)%Z.
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H4.
  apply Zle_is_le_bool.
  lia.
  auto.
  pure intro.
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H8.
  rewrite H9.
  apply Zle_bool_imp_le in H4.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'17) as X.
  destruct X;tryfalse.

  hoare forward.  
  rtmatch_solve.
  
  apply Zle_bool_imp_le in H4.
  rtmatch_solve.
  
  apply Zle_bool_imp_le in H4.
  
  sep lift 2%nat in H10.
  unfold OS_RDY_TBL_SIZE in H9.
  eapply GAarray_imp_length_P in H10.
  rewrite H10.
  simpl.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255)%Z);tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;auto.
  rtmatch_solve.

  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;intro;tryfalse.
  hoare unfold.
  unfold AOSTCBList'.
  unfold AOSTCBFreeList'.
  hoare_lifts_trms_pre (Adisj, p_local).
  (* hoare lifts (21::33::nil)%nat pre. *)
  eapply backward_rule1.
  intros.
  apply disj_split in H10.
  destruct H10.
  unfold p_local in H10.
  unfold CurTid in H10.
  sep normal in H10.
  sep destruct H10.
  unfold tcbdllseg in H10.
  sep lifts (4::1::nil)%nat in H10.
  sep split in H10.
  destruct H11;subst.
  apply read_only_merge_vptr in H10.
  destruct H10.
  sep lifts (3::4::5::6::nil)%nat in H10.
  apply task_del_noexists in H10.
  unfolds in H10;false.
  sep_lifts_trms_in H10 Adisj.
  (* sep lift 24%nat in H10. *)
  apply disj_split in H10.
  unfold TCBFree_Not_Eq in H10.
  destruct H10.
  sep normal in H10.
  sep destruct H10.
  sep split in H10.
  destruct H11;tryfalse.
  exact H10.
  unfold TCBFree_Eq.
  unfold p_local,CurTid.
  hoare unfold.
  hoare lift 3%nat pre.
  hoare forward.
  go.
  unfold p_local.
  unfold CurTid.
  sep cancel LINV.
  sep auto.
  
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H15.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H4 H18.
  apply Zle_bool_imp_le in Hran.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3)+ᵢ x1) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H31.  
  rewrite H31;auto.
  assert ( Int.unsigned x0 <=? Byte.max_unsigned =true).
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H31;auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x1) x0);auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x1) x0);simpl;auto.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3) +ᵢ x1) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H32.  
  rewrite H32;auto.
  destruct H27.
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H32.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H33.
  eapply int_unsigned_le_z2nat_lt.
  auto.
  unfold p_local.
  unfold CurTid.
  sep normal.
  exists OS_TCB.
  sep cancel LINV.
  sep cancel 4%nat 1%nat.
  simpl;auto.
  hoare forward;eauto.
  unfold p_local.
  unfold CurTid.
  sep normal.
  exists OS_TCB.
  sep cancel LINV.
  sep cancel 5%nat 1%nat.
  simpl;auto.
  instantiate (1:=Afalse).
  pure intro.
  lets Hinrtbl:unmap_inrtbl Hidle H2 H3 H15;auto.
  lets Hhastid:prio_in_rtbl_has_tid H27 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx1).
  split;lia.
  destruct Hhastid.
  hoare_lifts_trms_pre (Aop, Alvarmapsto os_code_defs.x, A_dom_lenv).
  (* hoare lifts (1::24::2::nil)%nat pre. *)
  hoare remember (1::2::3::nil) pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_choice1;eauto.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  unfold isched.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  
  instantiate (1:= <|| (ASSUME sc;; sched);;  END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) ** A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).
  apply absinfer_seq;auto.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  apply absinfer_choice1;auto.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (spec_done None;;sched);; END None ||>  **
                        LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) ** A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).
  eapply sc_isched_step with (t:=x2) (ct:=ct);eauto.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go. 
  split.
  eapply highest_rdy_eq_dead;eauto.
  rewrite Int.repr_unsigned in H34;auto.

  subst H35.
  sep cancel tcblist.
  sep cancel (Aabsdata abstcblsid).
  (* sep cancel 37%nat 1%nat. *) 
  sep lifts (7::8::nil)%nat in H36.
  apply read_only_merge_vptr in H36.
  destruct H36.
  exact H35.
  subst H35.
  sep auto.
  sep lifts (7::8::nil)%nat in H36.
  apply read_only_merge_vptr in H36.
  destruct H36.
  sep_lifts_trms_in H36 (tcblist, TCB_Not_In, abstcblsid, Agvarmapsto OSTCBCur).
  (* sep lifts (9::10::32::1::nil)%nat in H35. *) 
  eapply  highest_ct_dead_neq in H36;eauto.
  rewrite Int.repr_unsigned in H34;auto.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| sched;; END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil)  ** H35).
  apply absinfer_seq;auto.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  apply absinfer_seq_end;auto.

  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  
  apply backward_rule1 with ( <|| sched;; END None ||>  **
                                  ( LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
     A_dom_lenv ((os_code_defs.x, Int32u) :: nil)) ** H35).
  intros.
  sep normal.
  auto.
  subst H35.

  Set Printing Depth 99.
  eapply switchdead_rule with (Px:=LINV OSLInv ct  (logic_val (V$ 0) :: v'5) **  LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
     A_dom_lenv ((os_code_defs.x, Int32u) :: nil)).
  p_local_go.
  intros.
  sep cancel LINV.
  sep cancel 2%nat 2%nat.
  sep cancel 2%nat 2%nat.
  exact H35.
  
  intros.
  unfold SWINVt.
  
  sep normal.
  exists v'47.
  sep cancel 7%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists v'3.
  sep lifts (4::2::nil)%nat.
  eapply imp_isrclr.
  eapply simpl_inv_excrit'.
  sep cancel invlth_isr'.
  unfold OSInv.
  unfold AGVars.
  unfold AOSTCBPrioTbl.
  unfold A_isr_is_prop.
  sep semiauto;eauto.
  sep cancel 1%nat 2%nat.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  sep cancel OSPlaceHolder.
  sep cancel ACNU. (* added by CNU *)
  (* sep cancel 10%nat 1%nat. *)
  unfold AOSTCBList'.
  apply disj_split.
  right.
  sep normal.
  exists v'46.
  sep cancel TCB_Not_In.
  unfold AOSTCBFreeList'.
  sep lift 8%nat.
  apply disj_split.
  right.
  unfold TCBFree_Eq.
  sep auto.
  go.
  eexists;split.
  unfolds;simpl;auto.
  auto.
  simpl;auto.
  rewrite Int.repr_unsigned in H34;eauto.
  rewrite H39;simpl;auto.
  rewrite <- Hempisr;auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.
  
  clear -H14.
  unfolds in H14.
  mytac.
  unfolds in H.
  simpl in H.
  inverts H;auto.
  clear -H13.
  int auto.
  rewrite H39,H37.
  rewrite Hempisr.
  unfolds;simpl;auto.
  intros.
  unfold SWPRE_DEAD.
  split.
  unfold SWPRE.
  rewrite Int.repr_unsigned in H34.
  rewrite H34 in *.

  exists x2.
  sep lift 2%nat.
  apply imp_isrclr.
  rewrite <- Hempisr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 3%nat 2%nat.
  assert ( s |= GV OSTCBCur @ OS_TCB ∗ |-> Vptr ct **  AHprio GetHPrio x2 ** Atrue).
  eapply highest_rdy_eq_dead;eauto.
  sep cancel tcblist.
  unfold TCB_Not_In in H35.
  sep split in H35.
  mytac.
  sep lifts (4::5::nil)%nat in H35.
  apply read_only_merge_vptr in H35;destruct H35.
  sep auto.
  auto.

  exists v'20.

  eapply dead_not_in;eauto.
  sep cancel tcblist.
  sep cancel TCB_Not_In.
  sep auto.
  intros.
  sep cancel LINV.
  simpl;auto.

  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H26;mytac.
  false.
  apply pfalse_rule.
  pure intro.
  destruct H30.
  remember (Int.eq ((x<<ᵢ$ 3) +ᵢ x1) x0) as X.
  destruct X.
  simpl in H30.
  assert (Int.eq ((x<<ᵢ$ 3) +ᵢ  x1) x0 =false).
  eapply dead_not_ready;eauto.
  eapply prio_not_in_tcbls_nready;eauto.
  clear -H14.
  unfolds in H14.
  mytac.
  unfolds in H;inverts H;auto.
  
  rewrite H32 in HeqX0;tryfalse.
  simpl in H30.
  clear -H30;int auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ  x1) x0);simpl in H30;tryfalse. 
  
  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H2;mytac.
  false.
  apply pfalse_rule.
  pure intro.

  destruct v'2.

  simpl in H2.
  assert (Int.eq Int.one ($ 1) = true) by tauto.
  rewrite H3 in H2;destruct H2;simpl in H2;tryfalse.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  apply absinfer_choice2;eauto.
  destruct Htoy;rewrite H3;p_local_go.
  destruct Htoy;rewrite H3;p_local_go.
  eapply seq_rule.
  eapply excrit2_rule';eauto.
  apply GoodI_I. (* GoodI *)
  destruct Htoy;rewrite H3;p_local_go.
  apply ret_rule'.
  intros. 
  sep normal.
  sep eexists.
  sep split;eauto.
  apply disj_split.
  left.
  sep normal.
  sep lift 8%nat.
  apply disj_split.
  left.
  sep normal. sep eexists. sep cancel ACNU. (* added by CNU *)
  sep semiauto;eauto.
  sep split in H3;auto.
  
  (* sub goal -------------------------------------------------------------- ie true *)
  
  pure intro.
  eapply seq_rule.
  hoare lifts (5::1::2::3::4::nil)%nat pre.
  eapply encrit1_rule'.
  instantiate (1:=LV x @ Int32u |-> v' ** A_dom_lenv ((x, Int32u) :: nil)  **
   p_local OSLInv ct (logic_val v'4 :: (* nil *) v'5) ).
  intros.
  instantiate (1:=v'3).
  sep auto;eauto.
  rewrite H4;simpl;auto.
  apply GoodI_I.
  p_local_go.
 
  
  hoare lifts (2::6::nil)%nat pre.
  eapply backward_rule1.
  intros.
  eapply simpl_inv_excrit'' in H;eauto.

 
  assert (invlth_isr' I 1 v'3 = Aemp \/ invlth_isr' I 1 v'3 = atoy_inv').
  unfold invlth_isr'.
  destruct (leb 1 v'3);auto.
  rename H into Htoy.
  hoare lifts (2::3::nil)%nat pre.
  hoare unfold.
  pure intro.
  (*---------------check is-------------------------*)
  
  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H2 (Aisr, Ais, A_isr_is_prop).
  (* sep lifts (20::23::18::nil)%nat in H2. *) 
  apply elim_a_isr_is_prop' in H2.
  sep_lifts_trms_in H2 (p_local, AOSTCBList').
  (* sep lifts (26::11::nil)%nat in H2. *)
  lets Hx: p_local_ostcblist_eq_ct H2.
  rewrite Hx in H2.
  exact H2.
  auto.
 
  unfolds in Hirange.
  destruct Hirange;subst.
  eapply backward_rule1.
  intros.
  sep_lifts_trms_in H2 (AOSTCBList', AOSTCBFreeList', p_local).
  (* sep lifts (2::13::1::nil)%nat in H2. *) 
  eapply inv_change_aux in H2.
  exact H2.
  
  hoare_lifts_trms_pre (Aop, Aisr, Aie, Ais, Acs, Alvarmapsto x). 
  (* hoare lifts (23::5::24::6::25::26::nil)%nat pre. *)
  eapply seq_rule.
  apply checkis_rule' with (v:=v') (lg:=(logic_val ( V$ 1) :: (* nil *) v'5)).
  intros.
  exact H2.
  apply GoodI_I. (* Good I *)
  destruct Htoy;rewrite H2.
  p_local_go.
  p_local_go.
  intros.
  sep auto.
  
  hoare forward.
  unfold is_length.
  destruct v'2;simpl;auto.
  unfold val_inj.
  unfold is_length.
  destruct v'2;simpl;auto.
  
  instantiate (1:= Afalse).
  pure intro.
  apply is_length_neq_zero_elim in H2.
  subst v'2.
  clear H3 H4.
  apply isr_is_prop_emp in H0.
  rename H0 into Hempisr.
  (*---------------get y------------------------*)
  
  hoare unfold.
  rename H3 into Hidle.
  unfold AGVars.
  unfold AOSUnMapTbl.
  hoare forward.
  rtmatch_solve.
  
  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H6.
  simpl.
  rtmatch_solve.
  
  (*--------------get highest prio--------------*)
  unfold AOSRdyTbl.
  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H3.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true)%Z.
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H4.
  apply Zle_is_le_bool.
  lia.
  auto.
  pure intro.
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H8.
  rewrite H9.
  apply Zle_bool_imp_le in H4.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'16) as X.
  destruct X;tryfalse.

  hoare forward.  
  rtmatch_solve.
  apply Zle_bool_imp_le in H4.
  rtmatch_solve.
  apply Zle_bool_imp_le in H4.
  
  sep lift 2%nat in H10.
  unfold OS_RDY_TBL_SIZE in H9.
  eapply GAarray_imp_length_P in H10.
  rewrite H10.
  simpl.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255)%Z);tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;auto.
  rtmatch_solve.

  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;intro;tryfalse.
  hoare unfold.
  hoare forward.
  go.
  hoare unfold.
 

  (*----check if current task is highest ready----*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H4 H12.
  apply Zle_bool_imp_le in Hran.
  
  eapply abscsq_rule';eauto.
  apply noabs_oslinv.
  eapply absinfer_choice1;eauto.
  destruct Htoy;rewrite H19;go.
  destruct Htoy;rewrite H19;go.

  hoare_forward_stmts_nsepauto.

  assert ( Int.unsigned ((x<<ᵢ$ 3)+ᵢ x0) <= Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H34.  
  rewrite H34;auto.
  assert ( Int.unsigned i5 <=? Byte.max_unsigned =true)%Z.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H34;auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x0) i5);auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x0) i5);simpl;auto.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3) +ᵢ x0) <= Byte.max_unsigned )%Z.
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H35.  
  rewrite H35;auto.
  destruct H30;auto.

  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H35.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H36.
  eapply int_unsigned_le_z2nat_lt.
  auto.
  
  hoare forward;eauto.
  pure intro.

  lets Hinrtbl:unmap_inrtbl H2 H0 H3 H11;auto.

  lets Hhastid:prio_in_rtbl_has_tid H30 Hinrtbl.
  rewrite Int.unsigned_repr.
  split;try solve [lia].
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx0).
  lia.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx0).
  unfold Int.max_unsigned.
  lia.

  destruct Hhastid.

  eapply abscsq_rule';eauto.
  apply noabs_oslinv.
  unfold isched.
  eapply absinfer_seq;eauto.
  destruct Htoy;rewrite H38;go.
  2:apply absinfer_choice1;eauto.
  destruct Htoy;rewrite H38;go.
  destruct Htoy;rewrite H38;go.
  destruct Htoy;rewrite H38;go.
 
  
  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply sc_isched_step;eauto.
  destruct Htoy;rewrite H38;go.
  intros.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H37;eauto.
  
  instantiate (2:=  (v'45, Int.zero)).
  instantiate (3:= ((v'44
            :: v'40
               :: x8
                  :: x7
                     :: Vint32 i7
                        :: Vint32 i6
                           :: Vint32 i5
                              :: Vint32 i4
                                 :: Vint32 i3
                                    :: Vint32 i2 :: Vint32 i1 :: nil) :: v'15) %list).
  instantiate (3:=v'13).
  unfold AOSTCBList.

  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel OSTCBList.
  unfold p_local in H38.
  unfold CurTid in H38.
  sep normal in H38.
  sep destruct H38.
  sep lifts (7::1::nil)%nat%list in H38.
  apply read_only_merge_vptr in H38.
  destruct H38.
  clear H39.
  apply read_only_split_vptr in H38.
  sep cancel 1%nat 1%nat.
  sep cancel OSTCBCur.
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.
  sep auto.
  eapply prio_neq_tid_neq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H37;eauto.
  clear -H33.
  destruct (Int.eq ((x<<ᵢ$ 3)+ᵢx0) i5);simpl in H33;auto.
  unfold Int.notbool in H33.
  int auto.
  instantiate (2:=(v'45, Int.zero)).
  sep auto.
  eauto.
  eauto.
  eauto.
  split;auto.
  go.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_seq;eauto.
  3:eapply absinfer_seq_end;eauto.
  destruct Htoy;rewrite H38;go.
  destruct Htoy;rewrite H38;go.
  destruct Htoy;rewrite H38;go.
  destruct Htoy;rewrite H38;go.
  
  hoare remember (1::2::18::nil)%nat%list pre.
  apply backward_rule1 with (<|| sched;; END None ||>  **
                                 
                                 ( A_dom_lenv ((os_code_defs.x, Int32u) :: nil) **
                                              LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil))**
                                 H38).
  intros.
  sep normal.
  auto.
  subst H38.
  eapply frame_rule' with (frm:=
     A_dom_lenv  ((os_code_defs.x, Int32u) :: nil)**
     LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) ).
  apply GoodI_I. (* GoodI *)
  simpl;auto.
  simpl;auto.
  sep auto.
  unfold p_local.
  eapply switch_rule' with (Px:=LINV OSLInv (v'45, Int.zero) (* init_lg *) (logic_val (V$1) :: v'5)).
  intros.
  sep cancel LINV.
  exact H38.
  intros.
  unfold SWINVt.
  unfold CurTid in H38.
  sep normal in H38.
  sep destruct H38.
  sep normal.
  exists x2.
  sep cancel 1%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists v'3.
  sep lifts (3::2::nil)%nat.
  eapply imp_isrclr.
  
  eapply simpl_inv_excrit'.
  unfold OSInv.
  unfold A_isr_is_prop.
  unfold AGVars.
  sep normal. sep eexists. sep cancel ACNU. (* added by CNU *) 
  sep semiauto;eauto.
  (* sep cancel 1%nat 1%nat. *)
  (* sep cancel AOSEventFreeList. *)
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  (* sep cancel 8%nat 1%nat. *)
  unfold AOSTCBList'.
  apply disj_split.
  left.
  sep normal.
  sep eexists.
  unfold AOSTCBFreeList'.
  sep lift 12%nat.
  apply disj_split.
  left.
  unfold TCBFree_Not_Eq.
  unfold AOSTCBFreeList in H38. 
  sep normal.
  sep cancel tcbdllflag.
  sep auto;eauto.
  unfold tcbdllseg.
  sep cancel sll.
  sep cancel sllfreeflag.
  unfold1 dllseg.
  unfold node.
  sep auto;eauto.
  split;auto.
  go.
  intro;subst.
  
  sep lifts (1::7::nil)%nat in H38.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  intro;subst.
  sep lifts (1::7::nil)%nat in H38.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  simpl;auto.
  rewrite Int.repr_unsigned in H37.
  eauto.
  destruct_s s.
  simpl in H42;subst i10.
  simpl.
  auto.
  rewrite <- Hempisr.
  auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.
  auto.
  simpl in H17.
  clear -H17;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  destruct_s s.
  
  simpl in H42, H40.
  subst.
  simpl.
  rewrite Hempisr.
  unfolds.
  intros.
  unfold empisr;auto.
  
  intros.
  unfold SWPRE_NDEAD.
  split.
  unfold SWPRE.
  rewrite Int.unsigned_repr in H37.
  rewrite H37 in *.
  exists x1.
  sep lift 2%nat.
  apply imp_isrclr.
  
  sep remember (6::7::8::9::10::nil)%nat in H38.
  assert(s|=AOSTCBList v'11 (Vptr (v'45, Int.zero)) v'13 ( (v'44
              :: v'40
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil)  :: v'15) v'16 (v'45, Int.zero) v'19 ** H39).
  unfold AOSTCBList.
  sep normal.
  clear HeqH39.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.
  split;auto.
  go.
  clear H38.
  subst H39.
  rewrite <- Hempisr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 4%nat 2%nat.
  sep_lifts_trms_in H40 (AOSTCBList, abstcblsid, CurTid).
  (* sep lifts (1::27::13::nil)%nat in H39. *)
  unfold CurTid in H40.
  eapply highest_rdy_eq in H40;eauto.
  clear -Hran.
  remember ( ((x<<ᵢ$ 3) +ᵢ  x0) ) as X.
  clear HeqX.
  int auto.
  exists v'19.
  sep auto.
  clear -H15 H17.
  simpl in H17;mytac.
  assert (join (sig x x2) x1 v'43) by auto.
  assert (get (sig x x2) x = Some x2).
  apply map_get_sig.
  eapply join_get_l in H4;eauto.
  eapply join_get_r in H15;eauto.
  inverts H;unfolds;eauto.
  
  p_local_go.
  intros.
  sep cancel 1%nat 1%nat.
  simpl;auto.
  intros.
  exact H19.
  apply disj_rule.
  eapply backward_rule1.
  instantiate (1:= (<|| END None ||>  **
                        A_dom_lenv ((os_code_defs.x, Int32u) :: nil) **
                        
                        Aisr (isrupd v'0 v'3 false) **
                        Aie false **
                        Ais (v'3 :: nil) **
                        Acs (true :: nil) **
                        LV os_code_defs.x @ Int32u |-> is_length (0%nat :: nil) ** OSInv ** invlth_isr' I 1 v'3 ** 
                        p_local OSLInv (v'45, Int.zero) (* init_lg *) (logic_val (V$1) :: v'5))).
  intros.
  ssplit_apure_in H19.
  unfold SWINVt in H19.
  unfold SWINV in H19.  
  sep normal in H19.
  sep destruct H19.
  sep lifts (2::3::9::7::nil)%nat in H19.
  apply invlth_isr_invlth_isr'_imp in H19.
  sep cancel 1%nat 8%nat.
  sep cancel 1%nat 8%nat.
  unfold p_local.
  unfold CurTid.
  sep auto.
  rewrite Hempisr;auto.

  unfold OSInv.
  hoare normal pre.
  pure intro.
  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop, Aop, A_dom_lenv, Aie, Acs).
  (* hoare lifts (21::23::18::19::20::22::24::nil)%nat pre. *) 
  eapply backward_rule1.
  intros.  
  apply elim_a_isr_is_prop' in H30.
  exact H30.
  rewrite Hempisr.
  unfolds;simpl;auto.
  hoare lifts (3::1::5::2::6::nil)%nat pre.
  eapply seq_rule.
  eapply excrit1_rule'.
  instantiate (1:= A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** LV os_code_defs.x @ Int32u |-> is_length (0%nat :: nil)  ** 
                             p_local OSLInv (v'45, Int.zero) (* init_lg *) (logic_val (V$ 1) :: v'5)).
  intros.
  sep lifts (1::6::nil)%nat.
  eapply simpl_inv_excrit''';eauto.
  unfold OSInv.
  unfold A_isr_is_prop.
  sep auto;eauto.
  rewrite H42;simpl;auto.
  rewrite H40,H42;auto.
  rewrite Hempisr;unfolds;simpl;auto.
  apply GoodI_I. (* GoodI *)
  p_local_go.
  intros;sep auto.
  apply ret_rule'.
  intros.
  sep normal.
  do 4 eexists.
  exists v'3.
  exists (V$ 1).
  exists v'5.
  sep split.
  3:eauto.
  sep normal.
  sep split.
  sep cancel 7%nat 2%nat.
  left.
  sep lift 8%nat.
  apply disj_split.
  right.
  sep auto.
  rewrite Hempisr;unfolds;simpl;auto.
  sep split in H30;auto.

  lets Hinrtbl:unmap_inrtbl H2 H0 H3 H11;auto.
  pure intro.
  lets Hhastid:prio_in_rtbl_has_tid H30 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx0).
  split;lia.
  destruct Hhastid.
  hoare lifts (2::18::3::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  unfold isched.
  
  instantiate (1:= <|| ASSUME nsc;;END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H36).
  apply absinfer_seq;auto.
  destruct Htoy;subst H36;rewrite H37;go. 
  destruct Htoy;subst H36;rewrite H37;go. 
  
  apply absinfer_choice2;auto.
  destruct Htoy;subst H36;rewrite H37;go. 
  destruct Htoy;subst H36;rewrite H37;go. 
  
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| spec_done None;;END None||>  **
                        LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
                        A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H36).

  eapply nsc_isched_step with (t:=x1) (ct:=(v'45, Int.zero));eauto.
  subst H36.
  destruct Htoy;rewrite H36;go.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H35;auto.
  instantiate (2:=  (v'45, Int.zero)).
  instantiate (2:=   (v'44
               :: v'40
                  :: x8
                     :: x7
                        :: Vint32 i7
                           :: Vint32 i6
                              :: Vint32 i5
                                 :: Vint32 i4
                                    :: Vint32 i3
                                       :: Vint32 i2 :: Vint32 i1 :: nil)
              :: v'15) .
  instantiate (2:=v'13).
  instantiate (2:=v'11).
  subst H36.
  unfold p_local in H37.
  unfold CurTid in H37.
  sep normal in H37.
  sep destruct H37.
  unfold AOSTCBList.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep cancel dllseg.
  sep cancel dllseg.
  sep cancel Astruct.
  sep cancel OSTCBCur.
  
  sep cancel OSTCBCur.
  sep cancel OSTCBList.

  sep cancel abstcblsid.
  (* sep cancel 29%nat 9%nat. *)
  sep split;eauto.
  split;auto.
  go.
  subst H36.
  sep auto.
  eapply prio_eq_tid_eq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H35;eauto.
  clear -H33.
  destruct (Int.eq ((x<<ᵢ$ 3)+ᵢx0) i5);simpl in H33;destruct H33;auto;tryfalse.
  instantiate (2:=(v'45, Int.zero)).
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.

  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <||END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H36).
  apply absinfer_seq_end;auto.
  destruct Htoy;subst H36;rewrite H37;go.
  destruct Htoy;subst H36;rewrite H37;go.
  
  apply backward_rule1 with ( <|| END None ||>  ** OSInv ** invlth_isr' I 1 v'3 ** Aie false ** Ais (v'3::nil) ** Acs (true::nil) ** Aisr empisr ** LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
                                  A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** p_local OSLInv (v'45, Int.zero) (* init_lg *) (logic_val (V$ 1) :: v'5) ).
  
  intros.
  subst H36.
  sep remember (6::7::8::9::10::nil)%nat in H37.
  assert(s |= AOSTCBList v'11 (Vptr (v'45, Int.zero)) v'13 (   (v'44
               :: v'40
                  :: x8
                     :: x7
                        :: Vint32 i7
                           :: Vint32 i6
                              :: Vint32 i5
                                 :: Vint32 i4
                                    :: Vint32 i3
                                       :: Vint32 i2 :: Vint32 i1 :: nil)
              :: v'15) v'16 (v'45, Int.zero) v'19 ** H36).
  unfold AOSTCBList.
  sep normal.
  clear HeqH36.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.
  split;auto.
  go.
  clear H37.
  subst H36.
  unfold OSInv.
  unfold A_isr_is_prop.
  sep lifts (1::15::16::17::nil)%nat in H38.
  rewrite <- inv_change_aux in H38.
  sep normal. sep eexists. sep cancel ACNU.
  sep semiauto;eauto.
  sep cancel 3%nat 1 %nat.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  (* sep cancel 1%nat 6 %nat. *)
  (* sep cancel 1%nat 6%nat. *)
  exact H38.   
  simpl;auto.
  rewrite <- Hempisr;auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.

  2: {
    simpl in H17.
    clear -H17;mytac.
    unfolds in H2.
    destruct x2.
    destruct p.
    mytac.
    unfolds in H5.
    mytac.
    unfolds in H5;simpl in H5;inverts H5.
    clear -H20.
    int auto.
  } 
  (* rewrite H38,H40. *)
  rewrite Hempisr;unfolds;simpl;auto.
  unfold OSInv.
  hoare normal pre.
  pure intro.
  hoare_lifts_trms_pre (Aisr, Ais, A_isr_is_prop, Aop, invlth_isr', Aie, Acs).
  (* hoare lifts (24::22::18::19::20::21::23::nil)%nat pre. *) 
  eapply backward_rule1.
  intros.
  apply elim_a_isr_is_prop' in H36.
  exact H36.
  unfolds;simpl;auto.
  hoare lifts (3::1::5::2::6::nil)%nat pre.
  eapply seq_rule.
  eapply excrit1_rule'.
  instantiate (1:= A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** LV os_code_defs.x @ Int32u |-> is_length (0%nat :: nil)  ** 
                             p_local OSLInv (v'45, Int.zero) (* init_lg *) (logic_val (V$ 1) :: v'5)).  
  intros.
  sep lifts (1::6::nil)%nat.
  eapply simpl_inv_excrit''';eauto.
  unfold OSInv.
  unfold A_isr_is_prop.
  sep auto;eauto.
  rewrite H49;simpl;auto.
  rewrite Hempisr;auto.
  rewrite H47,H49;auto.
  unfolds;simpl;auto.
  apply GoodI_I. (* GoodI *)
  p_local_go.
  intros;sep auto.
  apply ret_rule'.
  intros.
  sep normal.
  do 4 eexists.
  exists v'3.
  exists (V$ 1).
  exists v'5. 
  sep split.
  3:eauto.
  apply disj_split.
  left.
  sep normal. 
  sep semiauto;eauto.
  (* sep cancel p_local. *)
  right.
  simpl;auto.
  rewrite Hempisr;unfolds;simpl;auto.
  sep split in H36;auto.
  
  hoare forward.
  pure intro.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  apply absinfer_choice2;eauto.
  destruct Htoy;rewrite H3;p_local_go.
  destruct Htoy;rewrite H3;p_local_go.
  eapply seq_rule.
  eapply excrit1_rule'.
  instantiate (1:= A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** LV os_code_defs.x @ Int32u |-> is_length (v'3 :: v'2)  ** 
                             p_local OSLInv ct (* init_lg *) (logic_val (V$ 1) :: v'5)).
  intros.
  sep lifts (1::6::nil)%nat.
  eapply simpl_inv_excrit''';eauto.
  unfold OSInv.
  unfold A_isr_is_prop.
  sep lifts (6::7::8::9::nil)%nat in H3.
  eapply inv_change_aux in H3.
  sep auto;eauto.
  rewrite H15;simpl;auto.
  rewrite H13,H15;auto.
  apply GoodI_I. (* GoodI *)
  p_local_go.
  sep auto.
  apply ret_rule'.
  intros.
  sep normal.
  do 4 eexists.
  exists v'3.
  exists (V$ 1).
  exists v'5.
  sep split.
  3:eauto.

  apply disj_split.
  left.
  sep normal.
  sep lift 8%nat.
  apply disj_split.
  right.
  sep auto.
  sep split in H3;auto.

  (*----------cur dead------------*)
  
  eapply seq_rule.
  hoare_lifts_trms_pre (Aop, Aisr, Aie, Ais, Acs, Alvarmapsto x).
  (* hoare lifts (22::3::23::4::24::25::nil)%nat pre. *)
  apply checkis_rule' with (v:=v') (lg:=(logic_val (V$ 0) :: (* nil *) v'5)).
  intros.
  exact H2.
  apply GoodI_I. (* Good I *)
  destruct Htoy;rewrite H2;p_local_go.
  sep auto.
  
  hoare forward.
  unfold is_length.
  destruct v'2;simpl;auto.
  unfold val_inj.
  unfold is_length.
  destruct v'2;simpl;auto.
  
  instantiate (1:= Afalse).
  pure intro.
  apply is_length_neq_zero_elim in H2.
  subst v'2.
  clear H3 H4.
  apply isr_is_prop_emp in H0.
  rename H0 into Hempisr.
  (*---------------get y------------------------*)
  
  hoare unfold.
  rename H3 into Hidle.
  unfold AGVars.
  unfold AOSUnMapTbl.
  hoare forward.
  rtmatch_solve.
  
  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H6.
  simpl.
  rtmatch_solve.
  
  (*--------------get highest prio--------------*)
  unfold AOSRdyTbl.
  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H3.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true)%Z.
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H4.
  apply Zle_is_le_bool.
  lia.
  auto.
  pure intro.
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H8.
  rewrite H9.
  apply Zle_bool_imp_le in H4.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'16) as X.
  destruct X;tryfalse.

  hoare forward.  
  rtmatch_solve.
  apply Zle_bool_imp_le in H4.
  rtmatch_solve.
  apply Zle_bool_imp_le in H4.

  
  sep lift 2%nat in H10.
  unfold OS_RDY_TBL_SIZE in H9.
  eapply GAarray_imp_length_P in H10.
  rewrite H10.
  simpl.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned)%Z as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255)%Z);tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;auto.
  rtmatch_solve.

  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true)%Z as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255))%Z;tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H11.
  simpl;intro;tryfalse.
  hoare unfold.
  unfold AOSTCBList'.
  unfold AOSTCBFreeList'.
  hoare lifts (14::23::nil)%nat pre.
  eapply backward_rule1.
  intros.
  apply disj_split in H10.
  destruct H10.
  unfold p_local in H10.
  unfold CurTid in H10.
  sep normal in H10.
  sep destruct H10.
  unfold tcbdllseg in H10.
  sep lifts (4::1::nil)%nat in H10.
  sep split in H10.
  destruct H11;subst.
  apply read_only_merge_vptr in H10.
  destruct H10.
(* ** ac:   Check task_del_noexists. *)
  sep lifts (3::4::5::13::nil)%nat in H10.
  apply task_del_noexists in H10.
  unfolds in H10;false.
  (* sep lift 24%nat in H10. *)
  sep_lifts_trms_in H10 Adisj.
  apply disj_split in H10.
  unfold TCBFree_Not_Eq in H10.
  destruct H10.
  sep normal in H10.
  sep destruct H10.
  sep split in H10.
  destruct H11;tryfalse.
  exact H10.
  unfold TCBFree_Eq.
  unfold p_local,CurTid.
  hoare unfold.
  hoare lift 3%nat pre.
  hoare forward.
  go.
  unfold p_local.
  unfold CurTid.
  sep cancel LINV.
  sep auto.
  
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H15.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H4 H18.
  apply Zle_bool_imp_le in Hran.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3)+ᵢ x1) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H31.   
  rewrite H31;auto.
  assert ( Int.unsigned x0 <=? Byte.max_unsigned =true).
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H31;auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x1) x0);auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x1) x0);simpl;auto.
 
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3) +ᵢ x1) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H32.  
  rewrite H32;auto.
  destruct H27.
  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H32.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H33.
  eapply int_unsigned_le_z2nat_lt.
  auto.
  unfold p_local.
  unfold CurTid.
  sep normal.
  exists OS_TCB.
  sep cancel LINV.
  sep cancel 4%nat 1%nat.
  simpl;auto.
  hoare forward;eauto.
  unfold p_local.
  unfold CurTid.
  sep normal.
  exists OS_TCB.
  sep cancel LINV.
  sep cancel 5%nat 1%nat.
  simpl;auto.
  instantiate (1:=Afalse).
  pure intro.
  lets Hinrtbl:unmap_inrtbl Hidle H2 H3 H15;auto.
  lets Hhastid:prio_in_rtbl_has_tid H27 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx1).
  split;lia.
  destruct Hhastid.
  hoare_lifts_trms_pre (Aop, Alvarmapsto os_code_defs.x, A_dom_lenv).
  (* hoare lifts (1::24::2::nil)%nat pre. *) 
  hoare remember (1::2::3::nil) pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  eapply absinfer_choice1;eauto.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  unfold isched.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  
  instantiate (1:= <|| (ASSUME sc;; sched);;  END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) ** A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).
  apply absinfer_seq;auto.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  apply absinfer_choice1;auto.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (spec_done None;;sched);; END None ||>  **
                        LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) ** A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** H35).
  eapply sc_isched_step with (t:=x2) (ct:=ct);eauto.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  split.
  eapply highest_rdy_eq_dead;eauto.
  rewrite Int.repr_unsigned in H34;auto.

  subst H35.
  sep cancel tcblist.
  sep cancel abstcblsid.
  (* sep cancel 37%nat 1%nat. *) 
  sep lifts (7::8::nil)%nat in H36.
  apply read_only_merge_vptr in H36.
  destruct H36.
  exact H35.
  subst H35.
  sep auto.
  sep lifts (7::8::nil)%nat in H36.
  apply read_only_merge_vptr in H36.
  destruct H36.
  sep_lifts_trms_in H36 (tcblist, TCB_Not_In, abstcblsid, Agvarmapsto OSTCBCur).
  (* sep lifts (9::10::32::1::nil)%nat in H35. *) 
  eapply  highest_ct_dead_neq in H36;eauto.
  rewrite Int.repr_unsigned in H34;auto.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| sched;; END None ||>  **
                       LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
                       A_dom_lenv ((os_code_defs.x, Int32u) :: nil)  ** H35).
  apply absinfer_seq;auto.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  apply absinfer_seq_end;auto.

  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  
  subst H35.
  destruct Htoy;rewrite H35; unfold tcblist;p_local_go.
  
  apply backward_rule1 with ( <|| sched;; END None ||>  **
                                  ( LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
     A_dom_lenv ((os_code_defs.x, Int32u) :: nil)) ** H35).
  intros.
  sep normal.
  auto.
  subst H35.

  
  eapply switchdead_rule with (Px:=LINV OSLInv ct  (logic_val (V$ 0) :: (* nil *) v'5) **  LV os_code_defs.x @ Int32u |-> is_length (v'3 :: nil) **
     A_dom_lenv ((os_code_defs.x, Int32u) :: nil)).
  p_local_go.
  intros.
  sep cancel LINV.
  sep cancel 2%nat 2%nat.
  sep cancel 2%nat 2%nat.
  exact H35.
  
  intros.
  unfold SWINVt.
  
  sep normal. 
  exists v'48. 
  sep cancel 7%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists v'3.
  sep lifts (4::2::nil)%nat.
  eapply imp_isrclr.
  eapply simpl_inv_excrit'.
  sep cancel invlth_isr'.
  unfold OSInv.
  unfold AGVars.
  unfold AOSTCBPrioTbl.
  unfold A_isr_is_prop.
  sep normal. sep eexists. sep cancel ACNU. (* added by CNU *) 
  sep semiauto;eauto.
  (* sep cancel 1%nat 1%nat. *)
  (* sep cancel AOSEventFreeList. *)
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  (* sep cancel 11%nat 1%nat. *)
  unfold AOSTCBList'.
  apply disj_split.
  right.
  sep normal.
  exists v'47. 
  sep cancel TCB_Not_In.
  unfold AOSTCBFreeList'.
  sep lift 8%nat.
  apply disj_split.
  right.
  unfold TCBFree_Eq.
  sep auto.
  go.
  eexists;split.
  unfolds;simpl;auto.
  auto.
  simpl;auto.
  rewrite Int.repr_unsigned in H34;eauto.
  rewrite H39;simpl;auto.
  rewrite <- Hempisr;auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.
  
  clear -H14.
  unfolds in H14.
  mytac.
  unfolds in H.
  simpl in H.
  inverts H;auto.
  clear -H13.
  int auto.
  (* rewrite H38,H36. *) 
  rewrite Hempisr.
  unfolds;simpl;auto.
  intros.
  unfold SWPRE_DEAD.
  split.
  unfold SWPRE.
  rewrite Int.repr_unsigned in H34.
  rewrite H34 in *.

  exists x2.
  sep lift 2%nat.
  apply imp_isrclr.
  rewrite <- Hempisr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 3%nat 2%nat.
  assert ( s |= GV OSTCBCur @ OS_TCB ∗ |-> Vptr ct **  AHprio GetHPrio x2 ** Atrue).
  eapply highest_rdy_eq_dead;eauto.
  sep cancel tcblist.
  unfold TCB_Not_In in H35.
  sep split in H35.
  mytac.
  sep lifts (4::5::nil)%nat in H35.
  apply read_only_merge_vptr in H35;destruct H35.
  sep auto.
  auto.

  exists v'19.

  eapply dead_not_in;eauto.
  sep cancel tcblist.
  sep cancel TCB_Not_In.
  sep auto.
  intros.
  sep cancel LINV.
  simpl;auto.

  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H26;mytac.
  false.
  apply pfalse_rule.
  pure intro.
  destruct H30.
  remember (Int.eq ((x<<ᵢ$ 3) +ᵢ x1) x0) as X.
  destruct X.
  simpl in H30.
  assert (Int.eq ((x<<ᵢ$ 3) +ᵢ  x1) x0 =false).
  eapply dead_not_ready;eauto.
  
  eapply prio_not_in_tcbls_nready;eauto.
  clear -H14.
  unfolds in H14.
  mytac.
  unfolds in H;inverts H;auto.
  
  rewrite H32 in HeqX0;tryfalse.
  simpl in H30.
  clear -H30;int auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ  x1) x0);simpl in H30;tryfalse.
 
  apply disj_rule.
  eapply backward_rule1 with Afalse.
  intros.
  simpl in H2;mytac.
  false.
  apply pfalse_rule.
  pure intro.

  destruct v'2.

  simpl in H2.
  assert (Int.eq Int.one ($ 1) = true) by tauto.
  rewrite H3 in H2;destruct H2;simpl in H2;tryfalse.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  apply absinfer_choice2;eauto.
  destruct Htoy;rewrite H3;p_local_go.
  destruct Htoy;rewrite H3;p_local_go.
  eapply seq_rule.
  eapply excrit1_rule'.
  instantiate (1:= A_dom_lenv ((os_code_defs.x, Int32u) :: nil) ** LV os_code_defs.x @ Int32u |-> is_length ( v'3 :: h :: v'2)  ** 
                             p_local OSLInv ct (logic_val (V$ 0) :: v'5) ).
  intros.
  sep lifts (1::6::nil)%nat.
  eapply simpl_inv_excrit''';eauto.
  unfold OSInv.
  unfold A_isr_is_prop.
  sep auto;eauto.
  rewrite H15;simpl;auto.
  rewrite H13,H15;auto.
  apply GoodI_I. (* GoodI *)
  p_local_go.
  sep auto.
  apply ret_rule'.
  intros. 
  sep normal.
  sep eexists.
  sep split;eauto.
  apply disj_split.
  left.
  sep normal.
  sep lift 8%nat.
  apply disj_split.
  right.
  sep auto.
  sep split in H3;auto.
Qed.

Close Scope code_scope.
