(**************************  uc/OS-II  ****************************)
(*************************** OS_CORE.C *******************************)
(*********Proof of Internal Fucntion:  void OS_Sched (void)***********)
(************************ Code:****************************)
(*** 
void  OS_Sched (void)
{
    INT8U      y;
1   OS_ENTER_CRITICAL();
2   y = OSUnMapTbl[OSRdyGrp];
3   OSPrioHighRdy = (INT8U)((y << 3) + OSUnMapTbl[OSRdyTbl[y]]);
4    OSPrioCur ′ =ₑ OSTCBCur ′ → OSTCBPrio;ₛ
5   if (OSPrioHighRdy != OSPrioCur)
    {                                              
6      OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];
7      OSCtxSwCtr++;                               
8      OSCtxSw();                                  
    }
9      OS_EXIT_CRITICAL();
}
***)

Require Import ucos_include.
Require Import absop_rules.
Require Import symbolic_lemmas.
Require Import os_ucos_h.
Require Import oscore_common.
Require Import Lia.

Open Scope code_scope.


Import DeprecatedTactic.

Lemma OSSched_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI os_internal OS_Sched
                  vl logicl OS_SchedPre ct->
      Some r =
      BuildRetI os_internal OS_Sched vl logicl OS_SchedPost ct->
      exists t d1 d2 s,
        os_internal OS_Sched = Some (t, d1, d2, s) /\
        {|OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init spec.
  hoare_split_pure_all.
  subst.
  (*----------------en_crit---------------------*)
  unfolds in  H0.
  destruct H0;subst.
  hoare forward prim.
  (*---------------get y------------------------*)

  hoare unfold.
  unfold AOSUnMapTbl.
  hoare forward;pauto.
  lets Hx:osunmapvallist_prop H1.
  mytac.
  rewrite H5.
  simpl.
  rtmatch_solve.
  
  (*--------------get highest prio--------------*)
  unfold AGVars.
  unfold AOSRdyTbl.

  lets Hiprop: osunmapvallist_prop H1.
  mytac.
  rewrite H4.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true).
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H5.
  apply Zle_is_le_bool.
  lia.
  auto.
  pure intro.
  
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H9.
  rewrite H10.
  apply Zle_bool_imp_le in H5.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'13) as X.
  destruct X;tryfalse.

  hoare forward.
  rewrite H6.
  auto.
  rewrite H6.
  auto.

  assert (Int.unsigned x <= 7).
  apply Zle_bool_imp_le;auto.



  sep lift 2%nat in H11.
  unfold OS_RDY_TBL_SIZE in H10.
  eapply GAarray_imp_length_P in H11.
  rewrite H11.
  simpl.
  apply Zle_bool_imp_le in H5.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  simpl;auto.
  rtmatch_solve.

  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  simpl;auto.
  (* get current task prio *)

  hoare unfold.
  hoare forward.
  go.
  
  (*----check if current task is highest ready----*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H5 H13.
  apply Zle_bool_imp_le in Hran.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3)+ᵢ x0) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H35.  
  rewrite H35;auto.
  assert ( Int.unsigned i5 <=? Byte.max_unsigned =true).
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool.
  lia.
  rewrite H35;auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x0) i5);auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ x0) i5);simpl;auto.
  hoare forward.
  assert ( Int.unsigned ((x<<ᵢ$ 3) +ᵢ x0) <= Byte.max_unsigned ).
  rewrite byte_max_unsigned_val.
  lia.
  apply Zle_is_le_bool in H36.  
  rewrite H36;auto.
  destruct H31;auto.

  eapply array_type_vallist_match_imp_rule_type_val_match;eauto.
  rewrite H36.

  assert (64%nat = Z.to_nat (63+1)).
  simpl;auto.
  rewrite H37.
  eapply int_unsigned_le_z2nat_lt.
  auto.
  
  hoare forward;eauto.
  pure intro.

  lets Hinrtbl:unmap_inrtbl H2 H1 H4 H12;auto.
  lets Hhastid:prio_in_rtbl_has_tid H31 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx0).
  split;lia.
  destruct Hhastid.
  Require Import List.
  hoare lifts (1::14::2::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.

 
  eapply abscsq_rule'.
  apply noabs_oslinv.
  unfold isched.
  
  instantiate (1:= <|| (ASSUME sc;; sched);; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H39).
  apply absinfer_seq;auto.
  subst H39.
  go.
  subst H39.
  can_change_aop_solver.
  apply absinfer_choice1;auto.
  subst H39.
  can_change_aop_solver.
  subst H39.
  can_change_aop_solver.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (spec_done None;;sched);; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H39).
  
  eapply sc_isched_step with (t:=x1) (ct:=(v'34, Int.zero));eauto.
  subst H39.
  can_change_aop_solver.
  split.

  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H38;auto.

  instantiate (2:=  (v'34, Int.zero)).
  instantiate (2:= (v'33
              :: v'29
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil):: v'12).
  instantiate (2:=v'10).
  instantiate (2:=v'8).
  subst H39.
  unfold p_local in H40.
  unfold CurTid in H40.
  unfold LINV in H40.
  Set Printing Depth 99.
  unfold AOSTCBList.
  sep normal in H40.
  sep destruct H40.
  sep split in H40.
  sep lift 11%nat in H40.
  apply read_only_merge_vptr in H40.
  destruct H40.
  clear H46.
  sep normal.
  sep eexists.
  sep split.
  unfold tcbdllseg.
  sep cancel 10%nat 3%nat.
  sep cancel 9%nat 2%nat.
  apply read_only_split_vptr.
  sep cancel 1%nat 1%nat.
  sep cancel 26%nat 2%nat. 
  unfold1 dllseg.
  unfold node.
  sep normal.
  sep eexists.
  sep split;eauto.
  sep cancel Astruct.
  sep cancel dllseg.
  exact H40.
  unfolds;simpl;auto.
  split;auto.
  go.
  eauto.
  eauto.
  auto.
  split;auto.
  subst H39.
  sep auto.

  eapply prio_neq_tid_neq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H38;eauto.
  clear -H34.
  destruct (Int.eq ((x<<ᵢ$ 3)+ᵢx0) i5);simpl in H34;auto.
  unfold Int.notbool in H34.
  int auto.
  instantiate (2:=(v'34, Int.zero)).
  sep auto.
  eauto.
  eauto.
  eauto.
  split;auto.
  go.

  eapply abscsq_rule'.
   apply noabs_oslinv.
  instantiate (1:= <|| sched;; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H39).
  apply absinfer_seq;auto.
  subst H39.
  can_change_aop_solver.
  subst H39.
  can_change_aop_solver.
  apply absinfer_seq_end;auto.
  subst H39.
  can_change_aop_solver.
  subst H39.
  can_change_aop_solver.
  
  apply backward_rule1 with ( <|| sched;; v'0 ||>  **
                                  (LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil)) ** H39).
  intros.
  sep normal.
  auto.
  subst H39.

  eapply frame_rule' with (frm:=  LV y @ Int8u |-> Vint32 x **  
                                     A_dom_lenv ((y, Int8u) :: nil) ).

  apply GoodI_I. (* GoodI *)
  simpl;auto.
  simpl;auto.
  intros;sep auto.
  eapply switch_rule'.
  instantiate (1:= LINV OSLInv (v'34, Int.zero) (logic_val (V$ 1) :: v'2)).
  intros.
  unfold p_local in H39.
  sep cancel OSLInv.
  exact H39.
  intros.
  unfold SWINVt.
  unfold CurTid in H39.
  sep normal in H39.
  sep destruct H39.
  
  sep normal.
  exists x2.
  sep cancel 1%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists INUM.
  sep lifts (3::2::nil)%nat.
  eapply imp_isrclr.
  apply simpl_inv_excrit.

  unfold OSInv.
  unfold AGVars.
  unfold AOSTCBPrioTbl.
  sep semiauto;eauto.
  sep cancel AOBJ. 
  sep cancel 1%nat 1%nat.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  sep cancel 6%nat 1%nat.
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
  unfold AOSTCBFreeList in H39.
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
  intro.
  subst.

  sep lifts (1::7::nil)%nat in H39.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  intro;subst.
  sep lifts (1::7::nil)%nat in H39.
  eapply Astruct_sll_OS_TCB_dup_false;eauto.
  simpl;auto.
  rewrite Int.repr_unsigned in H38.
  eauto.
  destruct_s s.
  simpl in H43;subst i10.
  simpl.
  auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H1.
  rewrite H1;auto.

  simpl in H18.
  clear -H18;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  
  intros.
  unfold SWPRE_NDEAD.
  split.
  unfold SWPRE.
  rewrite Int.repr_unsigned in H38.
  rewrite H38 in *.

  exists x1.

  sep lift 2%nat.
  apply imp_isrclr.

  sep remember (6::7::8::9::10::nil)%nat in H39.
  assert(s|=AOSTCBList v'8 (Vptr (v'34, Int.zero)) v'10 (  (v'33
              :: v'29
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil) :: v'12) v'13 (v'34, Int.zero) v'16 ** H40).
  unfold AOSTCBList.
  sep normal.
  clear HeqH40.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.

  split;auto.
  go.
  clear H39.
  subst H40.
  
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 4%nat 2%nat.

  Require Import seplog_pattern_tacs.
  sep_lifts_trms_in H41 (AOSTCBList, abstcblsid, CurTid).
  (* sep lifts (1::22::28::nil)%nat in H41. *) 
  unfold CurTid in H41.
  eapply highest_rdy_eq in H41;eauto.
  unfold LINV.
  exists v'16.
  sep auto.
  unfolds in H0.
  unfold indom.
  mytac;eauto.
  
  simpl;auto. (* splits; auto. intros; auto. splits; auto.  *)
  intros.
  sep cancel 1%nat 1%nat.
  simpl;auto.
  
  apply disj_rule.
  pure intro.
  
  apply backward_rule1 with (<|| v'0 ||>  ** OSInv ** atoy_inv' ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** LV y @ Int8u |-> Vint32 x  ** A_dom_lenv ((y, Int8u) :: nil) ** GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr (v'34, Int.zero) **  LINV OSLInv (v'34, Int.zero) (logic_val (V$ 1) :: v'2) (* init_lg *)).
  intros.
  unfold SWINVt in H33.
  unfold SWINV in H33.
  sep normal in H33.
  sep destruct H33.

  sep lifts (2::9::nil)%nat in H33.  
  lets Hi:topis_nil H33.
  subst x1.
  sep lifts (8::4::nil)%nat in H33.
  apply isrclr_imp  in H33.
  apply simpl_inv_encrit in H33.

  clear -H33.

  sep lifts (4::7::2::3::10::5::11::1::nil)%nat in H33.  

  apply atopis_pure in H33.

  sep lifts (2::8::nil)%nat in H33.
  
  apply ostcbcur_tp_os_tcb in H33.
  sep lifts (2::10::nil)%nat.
  auto.
  hoare lifts (1::7::4::5::6::2::3::nil)%nat pre.
  eapply seq_rule.

  eapply excrit1_rule'_ISnil_ISRemp;eauto.
  go.
  unfold LINV.
  unfold OSLInv.
  go.
  intros.
  unfold p_local.
  unfold CurTid.
  sep auto.
  hoare forward.
  unfold p_local.
  unfold CurTid.
  sep auto.

  lets Hinrtbl:unmap_inrtbl H2 H1 H4 H12;auto.
  pure intro.
  lets Hhastid:prio_in_rtbl_has_tid H31 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx0).
  split;lia.
  destruct Hhastid.
  hoare lifts (2::14::3::nil)%nat pre.
  hoare remember (1::2::3::nil) pre.

  eapply abscsq_rule'.
   apply noabs_oslinv.
  unfold isched.
  
  instantiate (1:= <|| ASSUME nsc;;v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H37).
  apply absinfer_seq;auto.
  subst H37;can_change_aop_solver.
  subst H37;can_change_aop_solver.
  
  apply absinfer_choice2;auto.
  subst H37;can_change_aop_solver.
  subst H37;can_change_aop_solver.

  eapply abscsq_rule'.
   apply noabs_oslinv.
  instantiate (1:= <|| spec_done None;;v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H37).

  eapply nsc_isched_step with (t:=x1) (ct:=(v'34, Int.zero));eauto.
  subst H37.
  can_change_aop_solver.
  split.
  eapply highest_rdy_eq;eauto.
  rewrite Int.repr_unsigned in H36;auto.

  instantiate (2:=  (v'34, Int.zero)).
  instantiate (2:= (v'33
              :: v'29
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil):: v'12).
  instantiate (2:=v'10).
  instantiate (2:=v'8).
  subst H37.
  unfold p_local in H38.

  unfold CurTid in H38.
  sep normal in H38.
  sep normal.
  sep destruct H38.
  exists x2.
  sep cancel 1%nat 1%nat.
  (* sep cancel 28%nat 2%nat. *)
  sep cancel abstcblsid.
  unfold AOSTCBList.
  unfold tcbdllseg.
  unfold1 dllseg.
  unfold node.
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.

  subst H37.
  sep auto.
  eapply prio_eq_tid_eq with (s:=s) (p_ct:=i5);eauto.
  rewrite Int.repr_unsigned in H36;eauto.
  clear -H34.
  destruct (Int.eq ((x<<ᵢ$ 3)+ᵢx0) i5);simpl in H34;destruct H34;auto;tryfalse.
  instantiate (2:=(v'34, Int.zero)).
  sep auto.
  eauto.
  eauto.
  auto.
  split;auto.
  go.

  eapply abscsq_rule'.
   apply noabs_oslinv.
  instantiate (1:= <||v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H37).
  apply absinfer_seq_end;auto.
  subst H37;can_change_aop_solver.
  subst H37;can_change_aop_solver.
  
  apply backward_rule1 with ( <|| v'0 ||>  ** OSInv ** atoy_inv' ** Aie false ** Ais nil ** Acs (true::nil) ** Aisr empisr ** LV y @ Int8u |-> Vint32 x  ** A_dom_lenv ((y, Int8u) :: nil) ** p_local OSLInv (v'34, Int.zero) ((logic_val (V$ 1) :: v'2))). 
  intros.
  subst H37.
  sep remember (6::7::8::9::10::nil)%nat in H38.
  assert(s |= AOSTCBList v'8 (Vptr (v'34, Int.zero)) v'10 (  (v'33
              :: v'29
                 :: x8
                    :: x7
                       :: Vint32 i7
                          :: Vint32 i6
                             :: Vint32 i5
                                :: Vint32 i4
                                   :: Vint32 i3
                                      :: Vint32 i2 :: Vint32 i1 :: nil)  :: v'12) v'13 (v'34, Int.zero) v'16 ** H37).
  unfold AOSTCBList.
  sep normal.
  clear HeqH37.
  sep semiauto;eauto.
  unfold tcbdllseg.
  simpl dllseg at 2.
  unfold node.
  sep auto.
  split;auto.
  go.
  clear H38.
  subst H37.
  sep lifts (2::10::nil)%nat.
  apply inv_change.
  unfold OldOSInvWL.
  sep semiauto;eauto.
  sep cancel AOBJ. 
  sep cancel 2%nat 1 %nat.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AOSTCBList.
  exact H39.   
  simpl;auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H1.
  rewrite H1;auto.
  auto.

  simpl in H18.
  clear -H18;mytac.
  unfolds in H2.
  destruct x2.
  destruct p.
  mytac.
  unfolds in H5.
  mytac.
  unfolds in H5;simpl in H5;inverts H5.
  clear -H20.
  int auto.
  hoare lifts (1::7::4::5::6::2::3::nil)%nat pre.
  eapply seq_rule.
  eapply excrit1_rule'_ISnil_ISRemp;eauto.
  unfold p_local.
  unfold CurTid.
  unfold LINV.
  unfold OSLInv.
  go.
  intros;sep auto.
  hoare forward.

  (***************************** self deleted case *****************************)
  hoare forward prim.
  hoare unfold.
  unfold AOSTCBList'.
  hoare_lifts_trms_pre Adisj. 
  (* hoare lift 9%nat pre. *)
  eapply backward_rule1.
  intros.
  apply disj_split in H3.
  eauto.
  apply disj_rule.
  unfold p_local.
  unfold CurTid.
  pure intro.
  eapply backward_rule1.
  intros.
  sep lifts (4::1::nil)%nat in H8.
  apply read_only_merge_vptr in H8.
  destruct H8.
  eapply astar_l_apure_intro; eauto.
  hoare_split_pure_all.
  subst v'18.
  unfold tcbdllseg.
  unfold tcbdllflag.

  hoare_lifts_trms_pre (dllseg v'8, dllseg (Vptr ct), dllsegflag, OSLInv).
  (* hoare lifts (3::4::5::30::nil)%nat pre. *)
  eapply backward_rule1.
  intros.
  eapply task_del_noexists in H8.
  exact H8.
  apply pfalse_rule.
  (*************)
  hoare unfold.
  unfold AOSUnMapTbl.
  hoare forward.
  pauto.
  lets Hx:osunmapvallist_prop H0.
  mytac.
  rewrite H5.
  simpl.
  rtmatch_solve.
  
  (*--------------get highest prio--------------*)
  unfold AGVars.
  unfold AOSRdyTbl.

  lets Hiprop: osunmapvallist_prop H0.
  mytac.
  rewrite H4.
  assert (Int.unsigned x <=? Byte.max_unsigned  =true).
  rewrite byte_max_unsigned_val.
  assert (Int.unsigned x <=? 255 =true).
  apply Zle_bool_imp_le in H5.
  apply Zle_is_le_bool.
  lia.
  auto.
  pure intro.
  
  lets Hxprop: array_type_vallist_match_imp_rule_type_val_match H9.
  rewrite H10.
  apply Zle_bool_imp_le in H5.
  instantiate (1:= Z.to_nat (Int.unsigned x)).
  unfold OS_RDY_TBL_SIZE.
  apply  Z2Nat.inj_lt.
  apply Int.unsigned_range.
  lia.
  lia.
  unfolds in Hxprop.
  remember (nth_val' (Z.to_nat (Int.unsigned x)) v'13) as X.
  destruct X;tryfalse.

  hoare forward.
  rewrite H6.
  auto.
  
  rewrite H6.
  auto.
  assert (Int.unsigned x <= 7).
  apply Zle_bool_imp_le;auto.

  sep lift 2%nat in H11.
  unfold OS_RDY_TBL_SIZE in H10.
  eapply GAarray_imp_length_P in H11.
  rewrite H11.
  simpl.
  apply Zle_bool_imp_le in H5.
  lia.
  rewrite <- HeqX.
  simpl;auto.
  eauto.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  remember (Int.unsigned i0 <=? Byte.max_unsigned) as Y.
  destruct Y;tryfalse.
  symmetry in HeqY.
  rewrite  byte_max_unsigned_val in HeqY.
  apply Zle_bool_imp_le in HeqY.
  lia.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  simpl;auto.
  rtmatch_solve.

  rewrite int_iwordsize_gt_3.
  simpl.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H12.
  simpl;auto.
  (* get current task prio *)
  unfold AOSTCBFreeList'.
  hoare normal pre.
  (* hoare lift 23%nat pre. *)
  hoare_lifts_trms_pre Adisj. 
  eapply backward_rule1.
  intros.
  apply disj_split in H11.
  destruct H11.
  unfold TCBFree_Not_Eq in H11.
  sep split in H11;tryfalse.
  eauto.
  unfold TCBFree_Eq.
  unfold p_local.
  unfold CurTid.
  hoare unfold.
  eapply backward_rule1.
  intros.
  sep lifts (17::1::nil)%nat in H14.

  Set Printing Depth 999.
  apply read_only_merge_vptr in H14.
  destruct H14.
  eapply astar_l_apure_intro; eauto.
  hoare_split_pure_all.
  subst v'18.
  
  hoare forward.
  go.
  unfold p_local.
  unfold CurTid.
  sep normal.
  sep eexists.
  sep cancel LINV.
  sep lift 2%nat in H14.
  apply read_only_split_vptr in H14.
  sep cancel 1%nat 1%nat.
  simpl;auto.

  (*----check if current task is highest ready----*)
  rewrite int_iwordsize_gt_3.
  simpl add.
  assert ((Int.unsigned i0 <=? 255) = true) as Hx.
  rewrite byte_max_unsigned_val in Hxprop.
  destruct ((Int.unsigned i0 <=? 255));tryfalse.
  auto.
  apply Zle_bool_imp_le in Hx.
  apply osunmapvallist_prop in Hx.
  mytac.
  rewrite H14.
  unfold AOSTCBPrioTbl.
  lets Hran:shl3_add_range H5 H17.
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
  lets Hinrtbl:unmap_inrtbl H2 H1 H4 H14;auto.
  lets Hhastid:prio_in_rtbl_has_tid H27 Hinrtbl.
  rewrite Int.repr_unsigned.
  lets Hx:Int.unsigned_range ((x<<ᵢ$ 3)+ᵢx1).
  split;lia.
  destruct Hhastid.
  hoare_lifts_trms_pre (Aop, Alvarmapsto y, A_dom_lenv). 
  (* hoare lifts (1::14::2::nil)%nat pre. *)
  hoare remember (1::2::3::nil) pre.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  unfold isched.
  instantiate (1:= <|| (ASSUME sc;; sched);; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H35).
  apply absinfer_seq;auto.
  subst H35.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  go.
  subst H35.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  apply absinfer_choice1;auto.
  subst H35.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  subst H35.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| (spec_done None;;sched);; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H35).
  
  eapply sc_isched_step with (t:=x2) (ct:=ct);eauto.
  subst H35.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  split.

  eapply highest_rdy_eq_dead;eauto.
  rewrite Int.repr_unsigned in H34;auto.

  subst H35.
  sep cancel tcblist.
  (* sep cancel 31%nat 1%nat. *)
  sep cancel abstcblsid. 
  sep cancel  7%nat 1%nat.
  exact H36.
  subst H35.
  sep auto.

  (* sep lifts (15::16::31::7::nil)%nat in H36. *)
  sep_lifts_trms_in H36 (tcblist, TCB_Not_In, abstcblsid, _N_ 7). 
  eapply  highest_ct_dead_neq in H36;eauto.
  rewrite Int.repr_unsigned in H34;auto.
  eapply abscsq_rule'.
  apply noabs_oslinv.
  instantiate (1:= <|| sched;; v'0 ||>  **
                       LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ** H35).
  apply absinfer_seq;auto.
  subst H35.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  subst H35.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  apply absinfer_seq_end;auto.
  subst H35.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  subst H35.
  unfold tcblist.
  unfold LINV.
  unfold OSLInv.
  can_change_aop_solver.
  
  apply backward_rule1 with ( <|| sched;; v'0 ||>  **
                                  (LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil)) ** H35).
  intros.
  sep normal.
  auto.
  subst H35.

  eapply switchdead_rule with (Px:=LINV OSLInv ct  (logic_val (V$ 0) :: v'2) ** LV y @ Int8u |-> Vint32 x ** A_dom_lenv ((y, Int8u) :: nil) ).
  unfold LINV,OSLInv.
  simpl;auto.
  splits; auto. (* splits; auto.  intros; splits; auto.  *)
  intros.
  sep cancel LINV.
  sep cancel 2%nat 2%nat.
  sep cancel 2%nat 2%nat.
  exact H35.
  
  intros.
  unfold SWINVt.
  
  sep normal.
  exists OS_TCB.
  sep cancel 6%nat 1%nat.
  unfold SWINV.
  sep normal.
  exists INUM.
  sep lifts (4::2::nil)%nat.
  eapply imp_isrclr.
  apply simpl_inv_excrit.

  unfold OSInv.
  unfold AGVars.
  unfold AOSTCBPrioTbl.
  
  sep semiauto;eauto.
  sep cancel AOBJ. 
  sep cancel 2%nat 1%nat.
  sep cancel AOSEventFreeList.
  sep cancel AOSQFreeList.
  sep cancel AOSQFreeBlk.
  sep cancel AECBList.
  (* sep cancel 10%nat 1%nat. *)
  sep cancel OSPlaceHolder.
  unfold AOSTCBList'.
  apply disj_split.
  right.
  sep normal.
  exists v'14.
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
  destruct_s s.
  simpl;simpl in H39;subst;auto.
  simpl;auto.
  rewrite byte_max_unsigned_val.
  apply Zle_is_le_bool in H0.
  rewrite H0;auto.

  clear -H13.
  unfolds in H13.
  mytac.
  unfolds in H.
  simpl in H.
  inverts H;auto.
  clear -H13.
  int auto.
  intros.
  unfold SWPRE_DEAD.
  split.
  unfold SWPRE.
  rewrite Int.repr_unsigned in H34.
  rewrite H34 in *.

  exists x2.
  sep lift 2%nat.
  apply imp_isrclr.
  sep cancel Aisr.
  sep normal.
  exists OS_TCB.
  exists OS_TCB.
  sep cancel 3%nat 2%nat.
  assert ( s |= GV OSTCBCur @ OS_TCB ∗ |-> Vptr ct **  AHprio GetHPrio x2 ** Atrue).
  eapply highest_rdy_eq_dead;eauto.
  sep cancel tcblist.
  sep auto.
  auto.

  exists v'16.

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
  clear -H13.
  unfolds in H13.
  mytac.
  unfolds in H;inverts H.
  auto.
  rewrite H32 in HeqX0;tryfalse.
  simpl in H31.
  clear -H30;int auto.
  destruct (Int.eq ((x<<ᵢ$ 3) +ᵢ  x1) x0);simpl in H30;tryfalse.
Qed. 


