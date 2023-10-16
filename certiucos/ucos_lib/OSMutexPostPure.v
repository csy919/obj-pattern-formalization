Require Import include_frm.
Require Import math_auto.
Require Import ucos_include.
Require Import os_ucos_h.
Require Import OSTimeDlyPure.
Require Import Lia.

Require Import protect.
Require Import OSQPostPure.
Require Import OSMutex_common.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Lemma post_exwt_succ_pre_mutex''
  : forall (v'36 v'13 : vallist) (v'12 : int32) 
           (v'32 : block) (v'15 : int32) (v'24 : block) 
           (v'35 v'0 : val) (v'8 : tid) (v'9 v'11 : EcbMod.map)
           (x : val) (x0 : maxlen) (x1 : waitset)
           (v'6 v'10 : EcbMod.map) (v'38 v'69 v'39 : int32) 
           (v'58 : block) (b : taskstatus) 
           (c :msg) (v'62 v'7 : TcbMod.map) 
           (vhold : addrval) pr o a ptbl,
       v'12 <> Int.zero ->
       R_PrioTbl_P v'36 v'7 vhold ->
       RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
       R_ECB_ETbl_P (v'32, Int.zero)
         (V$OS_EVENT_TYPE_MUTEX
          :: Vint32 v'12
             :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: nil,
         v'13, ptbl) v'7 ->
       RH_TCBList_ECBList_P v'11 v'7 v'8 ->
       EcbMod.join v'9 v'10 v'11 ->
       EcbMod.joinsig (v'32, Int.zero) (absmutexsem pr o , x1) v'6 v'10 ->
       Int.unsigned v'12 <= 255 ->
       array_type_vallist_match Int8u v'13 ->
       length v'13 = ∘OS_EVENT_TBL_SIZE ->
       nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
       Int.unsigned v'38 <= 7 ->
       nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
       Int.unsigned v'69 <= 255 ->
       nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
       Int.unsigned v'39 <= 7 ->
       nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
       Vptr (v'58, Int.zero) ->
       TcbJoin (v'58, Int.zero) (a, b, c) v'62 v'7 ->

       a = (v'38<<ᵢ$ 3)+ᵢv'39 /\ b<> rdy /\ x1 <> nil /\    
       GetHWait v'7 x1 (v'58, Int.zero) /\
       TcbMod.get v'7 (v'58, Int.zero) = Some (a, b, c).
Proof.
(*  eapply post_exwt_succ_pre_mutex; eauto.
  rewrite H126 in H61.
  inverts H61.
  rewrite H128 in H63.
  inverts H61.
  H128 : nth_val' (Z.to_nat (Int.unsigned x2)) v'50 = Vint32 v'63
  H134 : nth_val' (Z.to_nat (Int.unsigned x2)) OSMapVallist = Vint32 v'66
  H128 : nth_val' (Z.to_nat (Int.unsigned v'62)) v'50 = Vint32 v'63
 nth_val' (Z.to_nat (Int.unsigned v'57)) OSUnMapVallist = Vint32 x2
 nth_val' (Z.to_nat (Int.unsigned v'57)) OSUnMapVallist = Vint32 v'62
 nth_val' (Z.to_nat (Int.unsigned x2)) v'50 = Vint32 x4
 nth_val' (Z.to_nat (Int.unsigned x4)) OSUnMapVallist = Vint32 x5
*)
  intros.
  lets Hs :  tcbjoin_get_a  H16.
  unfolds in H3.
  unfolds in H1.
  unfolds in H0.
  unfolds in H2.
  destruct H2.
  destruct H17 as (H17&Htype).
  unfolds in H2.
  unfolds in H17.
  lets Hg : EcbMod.join_joinsig_get H4 H5.
  clear H4 H5.
  clear H16.
  assert ( Int.unsigned v'38 < 8) as Hx by lia.
  assert (Int.unsigned v'39 < 8) as Hy by lia.
  clear H10 H12.
  lets Hrs : math_xy_prio_cons Hx Hy.
  unfold nat_of_Z in H0.
  destruct H0 as (Hpr1 & Hpr2).
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  destruct Hpr2.
  apply H0 in Hs.
  destruct Hs;auto.
  lets Hnth : nth_val'_imp_nth_val_vptr H15.
  lets Hsd : Hpr1 Hrs Hnth.
  destruct Hsd as (st & m & Hst);auto.
  unfold get in *; simpl in *.
  rewrite Hs in Hst.
  inverts Hst.
  split.
  auto.
  assert (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3)= v'38).
  eapply math_shrl_3_eq; eauto.
  eapply nat_8_range_conver; eauto.
  assert ( (Z.to_nat (Int.unsigned v'38))  < length v'13)%nat.
  rewrite H8.
  simpl.
  unfold Pos.to_nat; simpl.
  clear - Hx.
  mauto.
  lets Has : array_int8u_nth_lt_len H7 H4.
  destruct Has as (i & Hnthz & Hinsa).
  rewrite H11 in Hnthz.
  inverts Hnthz.
  assert ((((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7) = v'39).
  eapply math_8range_eqy; eauto.
  eapply  nat_8_range_conver; eauto.
  apply nth_val'_imp_nth_val_int in H11.
  assert ( Vint32 v'12 = Vint32 v'12) by auto.
  lets Hzs : H1 H11 H10.
  eapply  nat_8_range_conver; eauto.
  destruct Hzs.
  lets Has : math_8_255_eq H6 H9 H.
  assert (i <> $ 0).
  assert ($ 1<<ᵢ$ Z.of_nat ∘(Int.unsigned v'38) = $ 1<<ᵢv'38).
  clear -Hx.
  mauto.
  rewrite H18 in H16.
  apply H16 in Has.
  apply ltu_eq_false in Has.
  pose (Int.eq_spec i ($0)).
  rewrite Has in y.
  auto.
  assert (PrioWaitInQ (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39)) v'13).
  unfolds.
  rewrite Int.repr_unsigned in *.
  exists ( ((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7 ).
  exists (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3) ).
  rewrite H0 in *.
  exists i.
  splits; eauto.
  rewrite H5.
  eapply math_8_255_eq; eauto.
  destruct H2 as (H2'&H2''&Hres&H2).
  lets Hes : H2 H19.
  unfold V_OSEventType in Hes.
  simpl nth_val in Hes.
  assert (Some (V$OS_EVENT_TYPE_MUTEX) = Some (V$OS_EVENT_TYPE_MUTEX)) by auto.
  apply Hes in H20.
  clear Hes.
  rename H20 into Hes.
  destruct Hes as (td & nn &mm & Hge).
  destruct Hpr2 as (Hpr2 & Hpr3).
  unfolds in Hpr3.
  assert (td = (v'58, Int.zero)  \/ td <> (v'58, Int.zero) ) by tauto.
  destruct H20.
  Focus 2.
  lets Hass : Hpr3 H20 Hge Hs.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  rewrite Int.repr_unsigned in *.
  subst td.
  unfold get in *; simpl in *.
  rewrite Hs in Hge.
  inverts Hge.
  destruct H3 as (H3'&H3''&Hres'&H3).
  destruct H3 as (Heg1 & Heg2 & Heg3).
  lets Hrgs : Heg2 Hs.
  destruct Hrgs as (xx & z &  qw & Hem & Hin).
  unfold get in *; simpl in *.
  rewrite Hg in Hem.
  inverts Hem.



  assert (qw = nil \/ qw <> nil) by tauto.
  destruct H3.
  subst qw.
  simpl in Hin; tryfalse.
  split.
  intro; tryfalse.
  auto.
  splits; auto.
  unfolds.
  splits; auto.
  do 3 eexists; splits; eauto.
  intros.
  assert (EcbMod.get v'11 (v'32, Int.zero) = Some (absmutexsem xx z, qw) /\ In t' qw) .
  splits; auto.
  lets Habs : Heg1 H22.
  destruct Habs as (prio' & m' & n' & Hbs).
  do 3 eexists; splits; eauto.
  destruct H17 as (H17'&H17''&Hres''&H17).
  lets Hpro : H17 Hbs.
  destruct Hpro as (Hpro&Hss).
  clear Hss.
  unfolds in Hpro.
  destruct Hpro as (xa & xb & zz & Hran & Hxx & Hyy & Hnths & Hzz).
  subst xa xb.
  rewrite Int.repr_unsigned in *.
  lets Hat : math_highest_prio_select H13 H9 H11 Hnths  Hzz;
    try eapply int_usigned_tcb_range; try lia;
    eauto.
  assert (Vint32 v'12 = Vint32 v'12) by auto.
  lets Hzs : H1 Hnths H23.
  eapply nat_8_range_conver; eauto.
  try eapply int_usigned_tcb_range; eauto.  
  destruct Hzs.
  assert (zz = $ 0 \/ zz <> $ 0) by tauto.
  destruct H26.
  subst zz.
  rewrite Int.and_commut in Hzz.
  rewrite Int.and_zero in Hzz.
  unfold Int.one in *.
  unfold Int.zero in *.
  assert ($ 1<<ᵢ(prio'&ᵢ$ 7) <> $ 0 ).
  eapply math_prop_neq_zero2; eauto.
  tryfalse.
  assert (Int.ltu ($ 0) zz = true).
  clear - H26.
  int auto.
  assert (0<=Int.unsigned zz ).
  int auto.
  assert (Int.unsigned zz = 0).
  lia.
  rewrite <- H0 in H26.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  apply H25 in H27.
  assert ($ Z.of_nat ∘(Int.unsigned (Int.shru prio' ($ 3))) = (Int.shru prio' ($ 3))).
  clear -Hran.
  mauto.
  rewrite H28 in *.
  auto.
  lets Hasss : Hpr3 H20 Hs Hbs; eauto.
  unfolds.
  rewrite zlt_true; auto.
  assert (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < Int.unsigned prio' \/
          Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) = Int.unsigned prio').
  lia.
  destruct H23; auto; tryfalse.
  false.
  apply Hasss.
  apply unsigned_inj; eauto.
Qed.

Lemma post_exwt_succ_pre_mutex_new
     : forall (v'36 v'13 : vallist) (v'12 : int32) 
         (v'32 : block) (v'15 : int32) (v'24 : block) 
         (v'35 v'0 : val) (v'8 : tid) (v'9 v'11 : EcbMod.map)
         (x : val) (x0 : maxlen) (x1 : waitset)
         (v'6 v'10 : EcbMod.map) (v'38 v'69 v'39 : int32) 
         (v'58 : block) (b : taskstatus) 
         (c :msg) (v'62 v'7 : TcbMod.map) 
         (vhold : addrval) pr o a ptbl,
       v'12 <> Int.zero ->
       R_PrioTbl_P v'36 v'7 vhold ->
       RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
       R_ECB_ETbl_P (v'32, Int.zero)
         (V$OS_EVENT_TYPE_MUTEX
          :: Vint32 v'12
             :: Vint32 v'15 :: Vptr (v'24, Int.zero) :: v'35 :: v'0 :: nil,
         v'13, ptbl) v'7 ->
       RH_TCBList_ECBList_P v'11 v'7 v'8 ->
       EcbMod.join v'9 v'10 v'11 ->
       EcbMod.joinsig (v'32, Int.zero) (absmutexsem pr o , x1) v'6 v'10 ->
       Int.unsigned v'12 <= 255 ->
       array_type_vallist_match Int8u v'13 ->
       length v'13 = ∘OS_EVENT_TBL_SIZE ->
       nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
       Int.unsigned v'38 <= 7 ->
       nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
       Int.unsigned v'69 <= 255 ->
       nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
       Int.unsigned v'39 <= 7 ->
       nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
       Vptr (v'58, Int.zero) ->
       TcbJoin (v'58, Int.zero) (a, b, c) v'62 v'7 ->
       a = (v'38<<ᵢ$ 3)+ᵢv'39/\ x1 <> nil /\
       (exists b' b'', b = (wait (os_stat_mutexsem b') b'')) /\
       GetHWait v'7 x1 (v'58, Int.zero) /\
       TcbMod.get v'7 (v'58, Int.zero) = Some (a, b, c)
.
Proof.
(*  eapply post_exwt_succ_pre_mutex; eauto.
  rewrite H126 in H61.
  inverts H61.
  rewrite H128 in H63.
  inverts H61.
  H128 : nth_val' (Z.to_nat (Int.unsigned x2)) v'50 = Vint32 v'63
  H134 : nth_val' (Z.to_nat (Int.unsigned x2)) OSMapVallist = Vint32 v'66
  H128 : nth_val' (Z.to_nat (Int.unsigned v'62)) v'50 = Vint32 v'63
 nth_val' (Z.to_nat (Int.unsigned v'57)) OSUnMapVallist = Vint32 x2
 nth_val' (Z.to_nat (Int.unsigned v'57)) OSUnMapVallist = Vint32 v'62
 nth_val' (Z.to_nat (Int.unsigned x2)) v'50 = Vint32 x4
 nth_val' (Z.to_nat (Int.unsigned x4)) OSUnMapVallist = Vint32 x5
*)
  intros.
  lets Hs :  tcbjoin_get_a  H16.
  unfolds in H3.
  unfolds in H1.
  unfolds in H0.
  unfolds in H2.
  destruct H2.
  destruct H17 as (H17&Htype).
  unfolds in H2.
  unfolds in H17.
  lets Hg : EcbMod.join_joinsig_get H4 H5.
  clear H4 H5.
  clear H16.
  assert ( Int.unsigned v'38 < 8) as Hx by lia.
  assert (Int.unsigned v'39 < 8) as Hy by lia.
  clear H10 H12.
  lets Hrs : math_xy_prio_cons Hx Hy.
  unfold nat_of_Z in H0.
  destruct H0 as (Hpr1 & Hpr2).
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  destruct Hpr2.
  apply H0 in Hs.
  destruct Hs;auto.
  lets Hnth : nth_val'_imp_nth_val_vptr H15.
  lets Hsd : Hpr1 Hrs Hnth.
  destruct Hsd as (st & m & Hst);auto.
  unfold get in *;simpl in *.
  rewrite Hs in Hst.
  inverts Hst.
  split.
  auto.
  assert (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3)= v'38).
  eapply math_shrl_3_eq; eauto.
  eapply nat_8_range_conver; eauto.
  assert ( (Z.to_nat (Int.unsigned v'38))  < length v'13)%nat.
  rewrite H8.
  simpl.
  unfold Pos.to_nat; simpl.
  clear - Hx.
  mauto.
  lets Has : array_int8u_nth_lt_len H7 H4.
  destruct Has as (i & Hnthz & Hinsa).
  rewrite H11 in Hnthz.
  inverts Hnthz.
  assert ((((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7) = v'39).
  eapply math_8range_eqy; eauto.
  eapply  nat_8_range_conver; eauto.
  apply nth_val'_imp_nth_val_int in H11.
  assert ( Vint32 v'12 = Vint32 v'12) by auto.
  lets Hzs : H1 H11 H10.
  eapply  nat_8_range_conver; eauto.
  destruct Hzs.
  lets Has : math_8_255_eq H6 H9 H.
  assert (i <> $ 0).
  assert ($ 1<<ᵢ$ Z.of_nat ∘(Int.unsigned v'38) = $ 1<<ᵢv'38).
  clear -Hx.
  mauto.
  rewrite H18 in H16.
  apply H16 in Has.
  apply ltu_eq_false in Has.
  pose (Int.eq_spec i ($0)).
  rewrite Has in y.
  auto.
  assert (PrioWaitInQ (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39)) v'13).
  unfolds.
  rewrite Int.repr_unsigned in *.
  exists ( ((v'38<<ᵢ$ 3)+ᵢv'39)&ᵢ$ 7 ).
  exists (Int.shru ((v'38<<ᵢ$ 3)+ᵢv'39) ($ 3) ).
  rewrite H0 in *.
  exists i.
  splits; eauto.
  rewrite H5.
  eapply math_8_255_eq; eauto.
  destruct H2 as (H2'&H2''&Hres&H2).
  lets Hes : H2 H19.
  unfold V_OSEventType in Hes.
  simpl nth_val in Hes.
  assert (Some (V$OS_EVENT_TYPE_MUTEX) = Some (V$OS_EVENT_TYPE_MUTEX)) by auto.
  apply Hes in H20.
  clear Hes.
  rename H20 into Hes.
  destruct Hes as (td & nn &mm & Hge).
  destruct Hpr2 as (Hpr2 & Hpr3).
  unfolds in Hpr3.
  assert (td = (v'58, Int.zero)  \/ td <> (v'58, Int.zero) ) by tauto.
  destruct H20.
  Focus 2.
  lets Hass : Hpr3 H20 Hge Hs.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  rewrite Int.repr_unsigned in *.
  subst td.
    unfold get in *; simpl in *.

  rewrite Hs in Hge.
  inverts Hge.
  destruct H3 as (H3'&H3''&Hres'&H3).
  destruct H3 as (Heg1 & Heg2 & Heg3).
  lets Hrgs : Heg2 Hs.
  destruct Hrgs as (xx & z &  qw & Hem & Hin).
  unfold get in *; simpl in *.

  rewrite Hg in Hem.
  inverts Hem.



  assert (qw = nil \/ qw <> nil) by tauto.
  destruct H3.
  subst qw.
  simpl in Hin; tryfalse.
  splits; auto.
  eauto.
  unfolds.
  splits; auto.
  do 3 eexists; splits; eauto.
  intros.
  assert (EcbMod.get v'11 (v'32, Int.zero) = Some (absmutexsem xx z, qw) /\ In t' qw) .
  splits; auto.
  lets Habs : Heg1 H22.
  destruct Habs as (prio' & m' & n' & Hbs).
  do 3 eexists; splits; eauto.
  destruct H17 as (H17'&H17''&Hres''&H17).
  lets Hpro : H17 Hbs.
  destruct Hpro as (Hpro&Hss).
  clear Hss.
  unfolds in Hpro.
  destruct Hpro as (xa & xb & zz & Hran & Hxx & Hyy & Hnths & Hzz).
  subst xa xb.
  rewrite Int.repr_unsigned in *.
  lets Hat : math_highest_prio_select H13 H9 H11 Hnths  Hzz;
    try eapply int_usigned_tcb_range; try lia;
    eauto.
  assert (Vint32 v'12 = Vint32 v'12) by auto.
  lets Hzs : H1 Hnths H23.
  eapply nat_8_range_conver; eauto.
  try eapply int_usigned_tcb_range; eauto.  
  destruct Hzs.
  assert (zz = $ 0 \/ zz <> $ 0) by tauto.
  destruct H26.
  subst zz.
  rewrite Int.and_commut in Hzz.
  rewrite Int.and_zero in Hzz.
  unfold Int.one in *.
  unfold Int.zero in *.
  assert ($ 1<<ᵢ(prio'&ᵢ$ 7) <> $ 0 ).
  eapply math_prop_neq_zero2; eauto.
  tryfalse.
  assert (Int.ltu ($ 0) zz = true).
  clear - H26.
  int auto.
  assert (0<=Int.unsigned zz ).
  int auto.
  assert (Int.unsigned zz = 0).
  lia.
  rewrite <- H0 in H26.
  rewrite Int.repr_unsigned in *.
  tryfalse.
  apply H25 in H27.
  assert ($ Z.of_nat ∘(Int.unsigned (Int.shru prio' ($ 3))) = (Int.shru prio' ($ 3))).
  clear -Hran.
  mauto.
  rewrite H28 in *.
  auto.
  lets Hasss : Hpr3 H20 Hs Hbs; eauto.
  unfolds.
  rewrite zlt_true; auto.
  assert (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < Int.unsigned prio' \/
          Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) = Int.unsigned prio').
  lia.
  destruct H23; auto; tryfalse.
  false.
  apply Hasss.
  apply unsigned_inj; eauto.
Qed.


        
Lemma rl_tbl_grp_p_set_hold:
  forall v'12 v'38 v'13 v'69 v'39 v'36 v'58 v'40 v'41,
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    Int.eq (v'69&ᵢInt.not v'40) Int.zero = true ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    RL_Tbl_Grp_P
      (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                      (Vint32 (v'69&ᵢInt.not v'40))) (Vint32 (v'12&ᵢInt.not v'41)).
Proof.
  intros.
  unfold Int.zero in *.
  pose (Int.eq_spec (v'69&ᵢInt.not v'40) ($ 0)) as Hps.
  rewrite H14 in Hps.
  unfolds in H15.
  unfolds.
  intros.
  assert (n =  (Z.to_nat (Int.unsigned v'38)) \/  n <>(Z.to_nat (Int.unsigned v'38))) as Hdisj.
  tauto.
  destruct Hdisj.
  subst n.
  apply nth_upd_eq in H17.
  inverts H17.
  assert (Int.unsigned v'38 < 8) as Ha by lia.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned v'38)) = v'38).
  clear - Ha.
  mauto.
  rewrite H17 in *.
  inverts H18.
  assert (   ($ 1<<ᵢv'38)&ᵢInt.not v'41 = $ 0) .
  clear - Ha H12.
  mautoext.
  splits.
  split.
  intros.
  auto.
  intros.
  lets Hzs : math_8_255_eq H0 H3 H.
  rewrite Int.and_commut.
  rewrite <-Int.and_assoc.
  assert ( v'12&ᵢ($ 1<<ᵢv'38) = ($ 1<<ᵢv'38)&ᵢv'12) .
  rewrite Int.and_commut; auto.
  rewrite H20 in Hzs.
  rewrite Hzs.
  auto.
  splits.
  rewrite Int.and_assoc.
  intros.
  assert (Int.not v'41&ᵢ($ 1<<ᵢv'38) = ($ 1<<ᵢv'38)&ᵢInt.not v'41).
  apply Int.and_commut.
  rewrite H20 in H19.
  rewrite H18 in H19.
  rewrite Int.and_zero in H19.
  unfold Int.zero in H19.
  false.
  clear -Ha H19.
  gen H19.
  mauto.
  intros.
  rewrite Hps in H19.
  false.
  eapply nth_upd_neq in H17; eauto.
  inverts H18.
  assert (Vint32 v'12 = Vint32 v'12) by auto.
  lets Hsa : H15 H16 H17 H18.
  destruct Hsa.
  lets Hasd : math_nth_8_neq_not  H12 H19; try lia; eauto.
  split.
  split;
    intros.
  apply H20.
  rewrite Int.and_assoc in H22.
  rewrite Hasd in H22.
  auto.
  intros.
  apply H20 in H22.
  assert (v'12&ᵢInt.not v'41 = Int.not v'41 &ᵢ v'12).
  apply Int.and_commut.
  rewrite H23.
  rewrite Int.and_assoc.
  rewrite H22.
  rewrite Int.and_zero; auto.
  split.
  intros.
  apply H21.
  rewrite Int.and_assoc in H22.
  rewrite Hasd in H22.
  auto.
  intros.
  apply H21 in H22.
  rewrite Int.and_assoc.
  rewrite Hasd.
  auto.
Qed.



Lemma rl_tbl_grp_p_set_hold':
  forall v'12 v'38 v'37 v'57 v'69 v'39 v'36 v'13 v'58 v'40 v'41,
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    array_type_vallist_match Int8u v'37 ->
    length v'37 =  ∘OS_RDY_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 = Vptr (v'58, Int.zero)->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) OSMapVallist = Vint32 v'41 ->
    Int.unsigned v'41 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    RL_Tbl_Grp_P v'37 (Vint32 v'57) ->
    RL_Tbl_Grp_P  (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                                  (val_inj
                                     (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))))
                  (Vint32 (Int.or v'57 v'41)).
Proof.
  intros.
  unfold Int.zero in *.
  unfolds in H16.
  unfolds in H17.
  unfolds.
  intros.
  inverts H20.
  assert (n =  (Z.to_nat (Int.unsigned v'38)) \/  n <>(Z.to_nat (Int.unsigned v'38))) as Hdisj.
  tauto.
  destruct Hdisj.
  subst n.
  apply nth_upd_eq in H19.
  unfolds in H19.
  remember (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40)) as vo.
  destruct vo; tryfalse.
  subst v0.
  assert ((Z.to_nat (Int.unsigned v'38)) < length v'37)%nat.
  rewrite H4.
  simpl.
  clear -H6.
  mauto.
  lets Hrs : array_int8u_nth_lt_len H19 ; eauto.
  destruct Hrs as (i & Hnth & Hr).
  rewrite Hnth in Heqvo.
  simpl in Heqvo.
  inverts Heqvo.
  assert (Int.unsigned v'38 < 8) as Ha by lia.
  assert ($ Z.of_nat (Z.to_nat (Int.unsigned v'38)) = v'38).
  clear - Ha.
  mauto.
  rewrite H20 in *.
  clear H20.
  split.
  split.
  intros.
  rewrite Int.and_commut in H20.
  rewrite  Int.and_or_distrib in H20.
  apply int_or_zero_split in H20.
  lets Hneq : math_nth_8_neq_zero  Ha H14.
  destruct H20.
  tryfalse.
  intros.
  apply int_or_zero_split in H20.
  destruct H20. subst.
  lets Hnz : math_nth_8_neq_zero' H12.
  lia.
  tryfalse.
  splits.
  assert (Int.unsigned v'40 <= Int.unsigned (Int.or i v'40)) .
  rewrite Int.or_commut.
  apply Int.or_le.
  lets Hgs : math_nth_8_gt_zero  H10 H12.
  assert (0 < Int.unsigned (Int.or i v'40)) by lia.
  intros.
  unfolds.
  rewrite zlt_true; auto.
  intros.
  rewrite Int.and_commut.
  rewrite Int.and_or_distrib.
  lets Has :   math_nth_8_eq_shl Ha H14.
  rewrite Has.
  rewrite Int.or_commut.
  rewrite Int.or_and_absorb.
  auto.
  apply nth_upd_neq in H19.
  assert ( Vint32 v'57 = Vint32 v'57) by auto.
  lets Hrs : H17 H18 H19 H21.
  destruct Hrs.
  splits.
  split;intros.
  apply H22.
  rewrite Int.and_commut in H24.
  rewrite Int.and_or_distrib in H24.
  apply int_or_zero_split in H24.
  destruct H24.
  rewrite Int.and_commut; auto.
  apply H22 in H24.
  rewrite Int.and_commut.
  rewrite Int.and_or_distrib .
  rewrite Int.and_commut in H24.
  rewrite H24.
  rewrite Int.and_commut.
  assert ($ 0 = Int.zero) by auto.
  rewrite H25.
  rewrite Int.or_commut.
  rewrite Int.or_zero.
  lets Hbc : math_nth_8_eq_zero H6 H14 H20; eauto.
  intros.
  split; intros.
  apply H23.
  lets Hbc : math_nth_8_eq_zero H6 H14 H20; eauto.
  rewrite Int.and_commut in H24.
  rewrite Int.and_or_distrib in H24.
  rewrite Int.and_commut in Hbc.
  rewrite Hbc in H24.
  rewrite Int.or_zero in H24.
  rewrite Int.and_commut.
  auto.
  apply H23 in H24.
  lets Hbc : math_nth_8_eq_zero H6 H14 H20; eauto.
  rewrite Int.and_commut .
  rewrite Int.and_or_distrib.
  rewrite Int.and_commut in Hbc.
  rewrite Hbc .
  rewrite Int.or_zero.
  rewrite Int.and_commut.
  auto.
  auto.
Qed.



Lemma prio_in_rtbl_hold:
  forall rtbl x y prio,
    Int.unsigned prio < 64 ->
    Int.unsigned x <= 7 ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    array_type_vallist_match Int8u rtbl ->
    prio_in_tbl prio rtbl ->
    prio_in_tbl prio
                (update_nth_val (Z.to_nat (Int.unsigned x)) rtbl
                                (val_inj
                                   (or (nth_val' (Z.to_nat (Int.unsigned x)) rtbl) (Vint32 y)))).
Proof.
  introv Hr1 Hr2 Hlen Har Hpro.
  unfolds.
  intros.
  subst.
  unfolds in Hpro.
  remember (val_inj
               (or (nth_val' (Z.to_nat (Int.unsigned x)) rtbl) (Vint32 y))) as Hx.
  assert ((Z.to_nat (Int.unsigned x)) < length rtbl)%nat.
  rewrite Hlen.
  clear - Hr2.
  mauto.
  lets Hsx : array_int8u_nth_lt_len Har H.
  simpljoin.
  rewrite H0 in H1.
  simpl in H1.
  remember (Int.shru prio ($3)) as py.
  assert (py = x \/ py <> x) by tauto.
  destruct H3.
  subst x.
  unfold nat_of_Z in H1.
  apply nth_upd_eq in H1.
  inverts H1.
  apply nth_val'_imp_nth_val_int in H0.
  lets Hsd : Hpro H0; eauto.
  rewrite Int.and_commut.
  rewrite Int.and_or_distrib.
  rewrite Int.and_commut in Hsd.
  rewrite Hsd.
  rewrite Int.or_and_absorb.
  auto.
  apply nth_upd_neq in H1.
  lets Hsd : Hpro H1; eauto.
  introv Hf.
  apply H3.
  unfold nat_of_Z in Hf.
  apply Z2Nat.inj_iff in Hf;  try apply Int.unsigned_range.
  apply unsigned_inj ; auto.
Qed.



Lemma idle_in_rtbl_hold':
  forall rtbl x y,
    Int.unsigned x <= 7 ->
    length rtbl = ∘OS_RDY_TBL_SIZE ->
    array_type_vallist_match Int8u rtbl ->
    prio_in_tbl ($ OS_IDLE_PRIO) rtbl ->
    prio_in_tbl ($ OS_IDLE_PRIO)
                (update_nth_val (Z.to_nat (Int.unsigned x)) rtbl
                                (val_inj
                                   (or (nth_val' (Z.to_nat (Int.unsigned x)) rtbl) (Vint32 y)))).
Proof.
  intros.
  eapply prio_in_rtbl_hold; eauto.
  unfold OS_IDLE_PRIO.
  unfold OS_LOWEST_PRIO.
  clear-x.
  int auto.
Qed.


Lemma tcb_inrtbl_not_vhold: forall v'42 v'62 v'93 v'57 v'81, RL_RTbl_PrioTbl_P v'42 v'62 v'93 ->  prio_in_tbl ((v'57)) v'42 -> nth_val' (Z.to_nat (Int.unsigned ((v'57)))) v'62 =  Vptr (v'81, Int.zero) ->   0 <= Int.unsigned v'57 < 64 -> (v'81, Int.zero) <> v'93.
Proof.
  introv H H0 H1 asdfasfd.
  unfolds in H.
  lets adaf: H H0.
  auto.
  simpljoin.
  apply nth_val_nth_val'_some_eq in H2.
  rewrite H1 in H2.
  inverts H2.
  auto.
Qed.

Lemma msglist_p_compose_mutex
: forall (p : val) (qid : addrval) (mqls : EcbMod.map)
         (qptrl1 qptrl2 : list EventCtr) (i i1 : int32) 
         (a : val) (x3 p' : val) (v'41 : vallist)
         (msgqls1 msgqls2 : list EventData) (msgq : EventData)
         (mqls1 mqls2 : EcbMod.map) (mq : absecb.B) 
         (mqls' : EcbMod.map) (tcbls : TcbMod.map) ptbl x4 x5,
    R_ECB_ETbl_P qid
                 (V$OS_EVENT_TYPE_MUTEX
                         :: Vint32 i :: Vint32 i1 ::  a :: x3 :: p' :: x3 :: x4 :: nil, v'41, ptbl) tcbls ->
    R_ECB_PETbl_P qid
  (V$ OS_EVENT_TYPE_MUTEX
   :: Vint32 i :: Vint32 i1 :: a :: x3 :: p' :: nil, v'41, ptbl) tcbls ->
    ECBList_P p (Vptr qid) qptrl1 msgqls1 mqls1 tcbls ->
    ECBList_P p' Vnull qptrl2 msgqls2 mqls2 tcbls ->
    RLH_ECBData_P msgq mq ->
    EcbMod.joinsig qid mq mqls2 mqls' ->
    EcbMod.join mqls1 mqls' mqls ->
    ECBList_P p Vnull
              (qptrl1 ++
                      ((V$OS_EVENT_TYPE_MUTEX
                         :: Vint32 i :: Vint32 i1 ::  a :: x3 :: p' :: x4 :: x5 :: nil, v'41, ptbl)
                         :: nil) ++ qptrl2) (msgqls1 ++ (msgq :: nil) ++ msgqls2) mqls
              tcbls.
Proof.
  intros.
  simpl.
  eapply ecblist_p_compose; eauto.
  simpl.
  eexists; splits; eauto.
  unfold R_ECB_PETbl_P in *.
  do 3 eexists; splits; eauto.
  unfolds; simpl; auto.
Qed.
Ltac mytac :=
  heat; jeauto2.
Require Import Mbox_common.
Lemma ECBList_P_Set_Rdy_hold_mutex
: forall (a : list EventCtr) (tcbls : TcbMod.map) 
         (tid : tidspec.A) (prio : priority) (msg0 msg' : msg) 
         (x y : val) (b : list EventData) (c : EcbMod.map) 
         (eid : ecbid) (nl : int32),
    TcbMod.get tcbls tid = Some (prio, wait (os_stat_mutexsem eid) nl, msg0) ->
    EcbMod.get c eid = None ->
    ECBList_P x y a b c tcbls ->
    ECBList_P x y a b c (TcbMod.set tcbls tid (prio, rdy, msg')).
Proof.
  inductions a; intros.
  simpl in *; auto.
  simpl in H1.
  mytac.
  destruct b; tryfalse.
  destruct a.
  destruct p. (* new add *)
  rename H3 into Hpetbl; rename H4 into H3. (* new add *)
  mytac.
  simpl.
  eexists.
  splits; eauto.
  unfolds.
  unfolds in H2.

  splits.
  
  destructs H2.
  unfolds in H2.
  mytac.
  unfolds.
  splits; unfolds;intros.

  apply H2 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.
  
  
  apply H8 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H9 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  
  apply H10 in H11.
  apply H11 in H12.
  mytac.
  assert (tid = x3 \/ tid <> x3) by tauto.
  destruct H13.
  subst tid.
  unfold get in *; simpl in *.
  rewrite H12 in H.
  inverts H.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  exists x3 x4 x5.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false; eauto.

  unfolds.
  destructs H2;unfolds in H6;destructs H6.
  splits;intros prio' mg ng x3 Hti;
  assert (tid = x3
          \/ tid <> x3) by tauto.
  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H6; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H8; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H9; eauto.

  destruct H11.
  subst tid.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti;  auto.
  rewrite H in Hti.
  inverts Hti.
  apply ecbmod_joinsig_get in H3.
  tryfalse.
  rewrite tidspec.eq_beq_true in Hti; tryfalse; auto.
  rewrite TcbMod.set_sem in Hti.
  rewrite tidspec.neq_beq_false in Hti; auto.
  eapply H10; eauto.

  mytac;auto.

  (* new add about petbl *)
  eapply R_ECB_PETbl_P_set_tcb_rdy_hold; eauto.
  introv Hf. destruct Hf as (qd & wt & Hf). inverts Hf.
  (* end of new add *)

  do 3 eexists; splits; eauto.
  eapply IHa; eauto.
  eapply ecbmod_joinsig_get_none; eauto.
Qed.

Lemma ecblist_p_post_exwt_hold_mutex_new'
: forall (v'36 : vallist) (v'12 : int32) (v'13 : vallist)
         (v'38 v'69 v'39 : int32) (v'58 : block) (v'40 : int32)
         (v'32 : block) (v'15 : int32)
         (v'35 v'16 v'18 v'19 v'20 v'34 : val) (v'21 v'22 : int32)
         (v'23 : block) (v'25 v'26 : val) (v'27 : vallist)
       (x0 : maxlen) (x1 : waitset) 
         (v'0 : val) (v'1 : list EventCtr) (v'5 : list EventData)
         (v'6 : EcbMod.map) (v'7 : TcbMod.map) (x00 : addrval)
         (v'11 : EcbMod.map) (v'31 : list EventData) 
         (v'30 : list EventCtr) (v'29 : val) (v'10 v'9 : EcbMod.map)
         (prio : priority) (v'62 : TcbMod.map) (st : taskstatus)
         (msg0 : msg) (y : int32) (vhold : addrval) tag (a_very_long_name : Int.ltu (tag>>ᵢ$ 8) prio = true )  
         optr ptbl x2 x3,
    True ->
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
    Vptr (v'58, Int.zero) ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (optr, $ 0) :: v'35 :: v'0 :: x2 :: x3 :: nil,
                  v'13, ptbl) v'7 ->
    R_ECB_PETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (optr, $ 0) :: v'35 :: v'0 :: x2 :: x3 :: nil,
                  v'13, ptbl) v'7 ->
    RLH_ECBData_P
      (DMutex (Vint32 tag) (Vptr (optr, $0))) (absmutexsem (tag>>ᵢ$ 8) (Some (optr, $ 0, tag&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) , x1) ->
    ECBList_P v'0 Vnull v'1 v'5 v'6 v'7 ->
    ECBList_P v'29 (Vptr (v'32, Int.zero)) v'30 v'31 v'9 v'7 ->
    EcbMod.joinsig (v'32, Int.zero) (absmutexsem  (tag>>ᵢ$ 8) (Some (optr,$ 0,  tag&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), x1) v'6 v'10 ->
    EcbMod.join v'9 v'10 v'11 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg0) v'62 v'7 ->
    R_PrioTbl_P v'36 v'7 vhold ->
    x1 <> nil ->
    ECBList_P v'29 Vnull
              (v'30 ++
                    ((V$OS_EVENT_TYPE_MUTEX
                       :: Vint32 y
                       :: Vint32 v'15 ::Vptr( v'58, $0) :: v'35 :: v'0 :: x2 :: x3 :: nil,
                      update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                                     (Vint32 (v'69&ᵢInt.not v'40)), ptbl) :: nil) ++ v'1)
              (v'31 ++
                    (DMutex  (Vint32 (Int.or (tag&ᵢ$ OS_MUTEX_KEEP_UPPER_8) prio)) (Vptr (v'58, $0)) ::nil)
                    ++ v'5)
              (EcbMod.set v'11 (v'32, Int.zero)
                          (absmutexsem  (tag>>ᵢ$ 8) (Some (v'58, $ 0,  prio )), remove_tid (v'58, Int.zero) x1))
              (TcbMod.set v'7 (v'58, Int.zero) (prio, rdy, Vnull))
.
Proof.
  intros.
  protect H.

  unfolds in H22.
  destruct H22 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H5 H9.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H10.
  lets Hps : Ha1 H22 H10.
  apply tcbjoin_get_a in H21.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in H21.
  destruct H21;auto.
  destruct Hps as (sts & mg & Hget);auto.
    unfold get in *; simpl in *.

  rewrite Hget in H21.
  inverts H21.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  unfolds in H14.
  destruct H14 as (Ha & Hb & Hc).
  destruct Ha as (Ha''&Ha'&Ha'''&Ha).
  destruct Hb as (Hb''&Hb'&Hb'''&Hb).
  lets Hz : math_unmap_get_y H1 H4.
  lets Heq1 :  math_mapval_core_prop H11; eauto.
  lia.
  subst v'40.
  assert (v'38 = Int.shru prio ($3)).
  subst.
  clear -Hz H9.
  mauto.
  assert (py = prio &ᵢ $ 7).
  subst prio. 
  rewrite Heqpx.
  clear -Hz H9.
  mauto.
  rewrite H14 in H6.
  assert (PrioWaitInQ (Int.unsigned prio) v'13) as Hcp.
  unfolds.
  do 3 eexists; splits; eauto.
  rewrite Int.repr_unsigned.
  eapply nth_val'_imp_nth_val_int; eauto.
  rewrite Int.repr_unsigned.
  rewrite <- H21.
  unfold Int.one.
  eapply math_8_255_eq; eauto.
  
  unfold Int.zero in H0.
  rewrite <-H14 in *.
  lets Hneq :  rl_tbl_grp_neq_zero H1 H0  H4 H6 H13.
  lia.
  auto.
  lets Hecp : Ha Hcp.
  unfold V_OSEventType in Hecp.
  simpl nth_val in Hecp.
  assert (Some (V$OS_EVENT_TYPE_MUTEX) = Some (V$OS_EVENT_TYPE_MUTEX)) by auto.
  apply Hecp in H24.
  clear Hecp.
  rename H24 into Hecp.
  destruct Hecp as (ct & nl & mg & Hcg).
  assert (ct = tid) as Hed.
  assert (ct = tid \/ ct <> tid)  by tauto.
  destruct H24; auto.
  lets Heqs : Ha3 H24 Hcg Hget.
  rewrite Int.repr_unsigned in Heqs.
  tryfalse.
  subst ct.
    unfold get in *; simpl in *.

  rewrite Hget in Hcg.
  inversion Hcg.
  subst mg st .
  clear Hcg.
  
  lets Hsds : ecb_set_join_join  (absmutexsem  (tag>>ᵢ$ 8)
             (Some (v'58, $ 0, prio)), remove_tid tid x1)  H19  H20.
  destruct Hsds as ( vv & Hsj1 & Hsj2).

  eapply msglist_p_compose_mutex.
  instantiate (1:= (v'32, Int.zero)).
  unfolds.
  splits.
  unfolds.
  splits;unfolds.
  Focus 4.
  introv Hprs Hxx.
  clear Hxx.
  apply prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).
  rewrite H14 in Hprs1.
  rewrite H21 in Hprs1.
  lets Hrs : prio_wt_inq_tid_neq  H6 H22.
  destruct Hrs as (Hrs & _).
  apply Hrs in Hprs1.
  destruct Hprs1 as (Hpq & Hneq).
  lets Hxs : Ha Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H24.
  subst tid'.
  unfold get in *; simpl in *.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  intros.
  unfolds in H26;simpl in H26;tryfalse.
  intros.
  unfolds in H26;simpl in H26;tryfalse.
  intros.
  unfolds in H26;simpl in H26;tryfalse.

  unfolds.
  splits;
    intros prio' mm nn tid'.
  Focus 4.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H24.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  lets Hga : Hb Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H24 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.

  lets Hrs : prio_wt_inq_tid_neq  H6 H22.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H26.
  rewrite H21.
  rewrite H14.
  auto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H24.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  lets Hga : Hb'' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H24 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H24.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  lets Hga : Hb' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H24 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H24.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H24 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  simpl fst in Hc;simpl;auto.
  2:{
  instantiate (1:=v'9).
  eapply ECBList_P_Set_Rdy_hold_mutex;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply joinsig_join_getnone; eauto. }
  2:{
  instantiate (1:=v'6).
  eapply ECBList_P_Set_Rdy_hold_mutex;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply  joinsig_get_none; eauto. }
  4:rewrite Int.repr_unsigned.
  4:eauto.
  3:eauto.
  2:{
  unfolds.
  split.
  unfolds.
  repeat tri_exists_and_solver1.
  apply acpt_intlemma6.
  clear -H22.
  mauto.
  rewrite acpt_intlemma4.
  auto.
  simpljoin.
  unfolds in H16.
  simpljoin.
  inverts H16.
    auto.
  clear -H22.
  mauto.
  intro.
  false.
  eapply acpt_intlemma5.
  2:exact H24.
  clear -H22.
  mauto.
  intros.
  repeat tri_exists_and_solver1.
  rewrite acpt_intlemma3.
  clear -H22.
  mauto.
  clear -H22.
  mauto.
  unfolds.
  repeat tri_exists_and_solver1.
  intro.
  tryfalse.
  intros.
  inverts H24.

  simpljoin.
  unfolds in H16.
  simpljoin.

  Focus 2.
  simpljoin.
  unfolds in H16.
  simpljoin.
  inverts H16.
  auto.
  split.
  auto.
  lia. }
  (*R_ECB_PETbl_P*)
  rewrite <- H25. 
  eapply R_ECB_PETbl_P_set_tcb_rdy_hold; eauto.
  unfolds; intros.
  do 2 destruct H24. inverts H24.
Qed.

Lemma ecblist_p_post_exwt_hold_mutex
: forall (v'36 : vallist) (v'12 : int32) (v'13 : vallist)
         (v'38 v'69 v'39 : int32) (v'58 : block) (v'40 : int32)
         (v'32 : block) (v'15 : int32)
         (v'35 v'16 v'18 v'19 v'20 v'34 : val) (v'21 v'22 : int32)
         (v'23 : block) (v'25 v'26 : val) (v'27 : vallist)
       (x0 : maxlen) (x1 : waitset) 
         (v'0 : val) (v'1 : list EventCtr) (v'5 : list EventData)
         (v'6 : EcbMod.map) (v'7 : TcbMod.map) (x00 : addrval)
         (v'11 : EcbMod.map) (v'31 : list EventData) 
         (v'30 : list EventCtr) (v'29 : val) (v'10 v'9 : EcbMod.map)
         (prio : priority) (v'62 : TcbMod.map) (st : taskstatus)
         (msg0 : msg) (y : int32) (vhold : addrval) tag (a_very_long_name : Int.ltu (tag>>ᵢ$ 8) prio = true )  
          optr ptbl x2 x3,
    RL_RTbl_PrioTbl_P v'13 v'36 vhold ->
    v'12 <> Int.zero ->
    Int.unsigned v'12 <= 255 ->
    array_type_vallist_match Int8u v'13 ->
    length v'13 = ∘OS_EVENT_TBL_SIZE ->
    nth_val' (Z.to_nat (Int.unsigned v'12)) OSUnMapVallist = Vint32 v'38 ->
    Int.unsigned v'38 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'38)) v'13 = Vint32 v'69 ->
    Int.unsigned v'69 <= 255 ->
    nth_val' (Z.to_nat (Int.unsigned v'69)) OSUnMapVallist = Vint32 v'39 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
    Vptr (v'58, Int.zero) ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    Int.unsigned v'40 <= 128 ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (optr, $ 0) :: v'35 :: v'0 ::  x2 :: x3 :: nil,
                  v'13, ptbl) v'7 ->
    R_ECB_PETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 v'12
                   :: Vint32 v'15 :: Vptr (optr, $ 0) :: v'35 :: v'0 :: x2 :: x3 :: nil,
                  v'13, ptbl) v'7 ->
    RLH_ECBData_P
      (DMutex (Vint32 tag) (Vptr (optr, $0))) (absmutexsem (tag>>ᵢ$ 8) (Some (optr, $ 0, tag&ᵢ$ OS_MUTEX_KEEP_LOWER_8)) , x1) ->
    ECBList_P v'0 Vnull v'1 v'5 v'6 v'7 ->
    ECBList_P v'29 (Vptr (v'32, Int.zero)) v'30 v'31 v'9 v'7 ->
    EcbMod.joinsig (v'32, Int.zero) (absmutexsem  (tag>>ᵢ$ 8) (Some (optr,$ 0,  tag&ᵢ$ OS_MUTEX_KEEP_LOWER_8)), x1) v'6 v'10 ->
    EcbMod.join v'9 v'10 v'11 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg0) v'62 v'7 ->
    R_PrioTbl_P v'36 v'7 vhold ->
    x1 <> nil ->
    ECBList_P v'29 Vnull
              (v'30 ++
                    ((V$OS_EVENT_TYPE_MUTEX
                       :: Vint32 y
                       :: Vint32 v'15 ::Vptr( v'58, $0) :: v'35 :: v'0 ::  x2 :: x3 :: nil,
                      update_nth_val (Z.to_nat (Int.unsigned v'38)) v'13
                                     (Vint32 (v'69&ᵢInt.not v'40)), ptbl) :: nil) ++ v'1)
              (v'31 ++
                    (DMutex  (Vint32 (Int.or (tag&ᵢ$ OS_MUTEX_KEEP_UPPER_8) prio)) (Vptr (v'58, $0)) ::nil)
                    ++ v'5)
              (EcbMod.set v'11 (v'32, Int.zero)
                          (absmutexsem  (tag>>ᵢ$ 8) (Some (v'58, $ 0,  prio )), remove_tid (v'58, Int.zero) x1))
              (TcbMod.set v'7 (v'58, Int.zero) (prio, rdy, Vptr x00))
.
Proof.
  intros.
  protect H.

  unfolds in H22.
  destruct H22 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H5 H9.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H10.
  lets Hps : Ha1 H22 H10.
  apply tcbjoin_get_a in H21.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in H21.
  destruct H21;auto.
  destruct Hps as (sts & mg & Hget);auto.
    unfold get in *; simpl in *.

  rewrite Hget in H21.
  inverts H21.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  unfolds in H14.
  destruct H14 as (Ha & Hb & Hc).
  destruct Ha as (Ha''&Ha'&Ha'''&Ha).
  destruct Hb as (Hb''&Hb'&Hb'''&Hb).
  lets Hz : math_unmap_get_y H1 H4.
  lets Heq1 :  math_mapval_core_prop H11; eauto.
  lia.
  subst v'40.
  assert (v'38 = Int.shru prio ($3)).
  subst.
  clear -Hz H9.
  mauto.
  assert (py = prio &ᵢ $ 7).
  subst prio. 
  rewrite Heqpx.
  clear -Hz H9.
  mauto.
  rewrite H14 in H6.
  assert (PrioWaitInQ (Int.unsigned prio) v'13) as Hcp.
  unfolds.
  do 3 eexists; splits; eauto.
  rewrite Int.repr_unsigned.
  eapply nth_val'_imp_nth_val_int; eauto.
  rewrite Int.repr_unsigned.
  rewrite <- H21.
  unfold Int.one.
  eapply math_8_255_eq; eauto.
  
  unfold Int.zero in H0.
  rewrite <-H14 in *.
  lets Hneq :  rl_tbl_grp_neq_zero H1 H0  H4 H6 H13.
  lia.
  auto.
  lets Hecp : Ha Hcp.
  unfold V_OSEventType in Hecp.
  simpl nth_val in Hecp.
  assert (Some (V$OS_EVENT_TYPE_MUTEX) = Some (V$OS_EVENT_TYPE_MUTEX)) by auto.
  apply Hecp in H24.
  clear Hecp.
  rename H24 into Hecp.
  destruct Hecp as (ct & nl & mg & Hcg).
  assert (ct = tid) as Hed.
  assert (ct = tid \/ ct <> tid)  by tauto.
  destruct H24; auto.
  lets Heqs : Ha3 H24 Hcg Hget.
  rewrite Int.repr_unsigned in Heqs.
  tryfalse.
  subst ct.
    unfold get in *; simpl in *.

  rewrite Hget in Hcg.
  inversion Hcg.
  subst mg st .
  clear Hcg.
  
  lets Hsds : ecb_set_join_join  (absmutexsem  (tag>>ᵢ$ 8)
             (Some (v'58, $ 0, prio)), remove_tid tid x1)  H19  H20.
  destruct Hsds as ( vv & Hsj1 & Hsj2).

  eapply msglist_p_compose_mutex.
  instantiate (1:= (v'32, Int.zero)).
  unfolds.
  splits.
  unfolds.
  splits;unfolds.
  Focus 4.
  introv Hprs Hxx.
  clear Hxx.
  apply prio_wt_inq_convert in Hprs.
  destruct Hprs as (Hprs1 & Hprs2).
  rewrite H14 in Hprs1.
  rewrite H21 in Hprs1.
  lets Hrs : prio_wt_inq_tid_neq  H6 H22.
  destruct Hrs as (Hrs & _).
  apply Hrs in Hprs1.
  destruct Hprs1 as (Hpq & Hneq).
  lets Hxs : Ha Hpq.
  rewrite Int.repr_unsigned in Hxs.
  destruct Hxs as (tid' & nn & mm & Htg).
  unfolds;simpl;auto.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H24.
  subst tid'.
  unfold get in *; simpl in *.
  rewrite Hget in Htg.
  inversion Htg.
  tryfalse.
  exists tid' nn mm.
  rewrite TcbMod.set_sem.
  rewrite tidspec.neq_beq_false;eauto.

  intros.
  unfolds in H26;simpl in H26;tryfalse.
  intros.
  unfolds in H26;simpl in H26;tryfalse.
  intros.
  unfolds in H26;simpl in H26;tryfalse.

  unfolds.
  splits;
    intros prio' mm nn tid'.
  Focus 4.
  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H24.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  lets Hga : Hb Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H24 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.

  lets Hrs : prio_wt_inq_tid_neq  H6 H22.
  destruct Hrs as (_ & Hrs).
  apply Hrs in H26.
  rewrite H21.
  rewrite H14.
  auto.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H24.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  lets Hga : Hb'' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H24 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H24.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  lets Hga : Hb' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H24 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  assert (tid = tid' \/ tid <> tid') by tauto.
  destruct H24.
  subst tid'.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.eq_beq_true in Hgs; auto.
  inverts Hgs.
  introv Hgs.
  rewrite TcbMod.set_sem in Hgs.
  rewrite tidspec.neq_beq_false in Hgs; eauto.
  lets Hga : Hb''' Hgs.
  destruct Hga as (Hga & Hx).
  unfolds in Ha3.
  lets Hneqp: Ha3 H24 Hget Hgs.
  assert ( PrioWaitInQ (Int.unsigned prio') v'13 /\ prio' <> prio) .
  splits; auto.
  unfolds in Hx;simpl in Hx;tryfalse.

  simpl fst in Hc;simpl;auto.
  2:{
  instantiate (1:=v'9).
  eapply ECBList_P_Set_Rdy_hold_mutex;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply joinsig_join_getnone; eauto. }
  2:{
  instantiate (1:=v'6).
  eapply ECBList_P_Set_Rdy_hold_mutex;eauto.
  rewrite Int.repr_unsigned.  
  eauto.
  eapply  joinsig_get_none; eauto. }
  4:rewrite Int.repr_unsigned.
  4:eauto.
  3:eauto.
  2:{
  unfolds.
  split.
  unfolds.
  repeat tri_exists_and_solver1.
  apply acpt_intlemma6.
  clear -H22.
  mauto.
  rewrite acpt_intlemma4.
  auto.
  simpljoin.
  unfolds in H16.
  simpljoin.
  inverts H16.
    auto.
  clear -H22.
  mauto.
  intro.
  false.
  eapply acpt_intlemma5.
  2:exact H24.
  clear -H22.
  mauto.
  intros.
  repeat tri_exists_and_solver1.
  rewrite acpt_intlemma3.
  clear -H22.
  mauto.
  clear -H22.
  mauto.
  unfolds.
  repeat tri_exists_and_solver1.
  intro.
  tryfalse.
  intros.
  inverts H24.

  simpljoin.
  unfolds in H16.
  simpljoin.

  Focus 2.
  simpljoin.
  unfolds in H16.
  simpljoin.
  inverts H16.
  auto.
  split.
  auto.
  lia. }
  (*R_ECB_PETbl_P*)
  rewrite <- H25. 
  eapply R_ECB_PETbl_P_set_tcb_rdy_hold; eauto.
  unfolds; intros.
  do 2 destruct H24. inverts H24.
Qed.

Lemma rh_tcblist_ecblist_p_post_exwt_aux_mbox
: forall (v'8 tid0 : tid) (v'11 : EcbMod.map) 
         (v'7 : TcbMod.map) (v'9 v'10 : EcbMod.map) 
         (eid : tidspec.A) 
         (x0 : maxlen) (x1 : waitset) (v'6 : EcbMod.map) 
         (prio : priority) (msg0 : msg) 
         (st : taskstatus) x y,
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig eid (absmutexsem x y, x1) v'6 v'10 ->
    In tid0 x1 ->
    TcbMod.get v'7 tid0 = Some (prio, st, msg0) ->
    exists xl, st = wait (os_stat_mutexsem eid) xl
.
  intros.
  unfolds in H.
  destruct H as (Hexaa & Hexa & Hex & Hexaaa).
  lets Hget : EcbMod.join_joinsig_get H0 H1.
  assert (EcbMod.get v'11 eid = Some (absmutexsem x y, x1) /\ In tid0 x1).
  split; auto.
  apply Hexaaa in H.
  simpljoin.
  unfold get in *; simpl in *.
  rewrite H3 in H.
  inverts H.
  eauto.
Qed.

Require Import OSTimeTickPure.
Lemma rh_tcblist_ecblist_p_post_exwt_mutex
: forall (v'8 tid : tid) (v'11 : EcbMod.map) 
         (v'7 : TcbMod.map) (v'9 v'10 : EcbMod.map) 
         (eid : tidspec.A) 
         (x0 : maxlen) (x1 : waitset) (v'6 : EcbMod.map) 
         (prio : priority) (msg0 : msg) 
         (xl : int32) x t op st m pt x00,
    TcbMod.get v'7 t = Some (op,st,m) ->
    op <> x ->
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig eid (absmutexsem x (Some (t, pt)), x1) v'6 v'10 ->
    In tid x1 ->
    TcbMod.get v'7 tid = Some (prio, wait (os_stat_mutexsem eid) xl, msg0) ->
    RH_TCBList_ECBList_P
      (EcbMod.set v'11 eid (absmutexsem x (Some (tid, prio)), remove_tid tid x1))
      (TcbMod.set v'7 tid (prio, rdy, Vptr x00)) v'8
.
Proof.
  introv ml Ht Hneq.
  intros.
  destruct H as (Hq & Hsem & Hmbox & Hmut).
  destruct Hq as (Hq1 & Hpostq1 & Hq2& Hpostq2).
  destruct Hsem as (Hsem1 & Hsem2).
  destruct Hmbox as (Hmbox1 & Hmbox2).
  destruct Hmut as (Hmut1 & Hmut2 & Hown & Howp).
  unfold get in *; unfold TcbMap, EcbMap in *.
  unfolds;splits.

  unfolds; splits; intros.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2.
   destruct H; inverts H. eapply Hq1 in H.
   destruct (tidspec.beq tid tid0) eqn: eq1; eauto.
   eapply tidspec.beq_true_eq in eq1. subst.
   do 3 destruct H. rewrite H3 in H. inverts H.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2. destruct H; inverts H.
  eapply Hpostq1 in H.  
   destruct (tidspec.beq tid tid0) eqn: eq1; eauto.
   eapply tidspec.beq_true_eq in eq1. subst.
   do 3 destruct H. rewrite H3 in H. inverts H.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq tid tid0) eqn: eq1.  inverts H.
  eapply Hq2 in H. destruct (tidspec.beq eid eid0) eqn: eq2.
  try eapply tidspec.beq_true_eq in eq2; subst.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.
  do 5 destruct H. rewrite H in H1; inverts H1. do 4 destruct H;
  repeat eexists; destruct H; eauto.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq tid tid0) eqn: eq1.  inverts H.
  eapply Hpostq2 in H. destruct (tidspec.beq eid eid0) eqn: eq2.
  try eapply tidspec.beq_true_eq in eq2; subst.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.
  do 5 destruct H. rewrite H in H1; inverts H1. do 4 destruct H;
  repeat eexists; destruct H; eauto.
  unfolds; splits; intros.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2.
   destruct H; inverts H. eapply Hsem1 in H.
   destruct (tidspec.beq tid tid0) eqn: eq1; eauto.
   eapply tidspec.beq_true_eq in eq1. subst.
   do 3 destruct H. rewrite H3 in H. inverts H.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
   destruct (tidspec.beq tid tid0) eqn: eq1; inverts H.
  destruct (tidspec.beq eid eid0) eqn: eq2.
  try eapply tidspec.beq_true_eq in eq2; subst.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.
  eapply Hsem2 in H5.
  destruct H5. do 2 destruct H. rewrite H in H1; inverts H1.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.
  unfolds; splits; intros.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2.
   destruct H; inverts H. eapply Hmbox1 in H.
   destruct (tidspec.beq tid tid0) eqn: eq1; eauto.
   eapply tidspec.beq_true_eq in eq1. subst.
   do 3 destruct H. rewrite H3 in H. inverts H.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
   destruct (tidspec.beq tid tid0) eqn: eq1; inverts H.
  destruct (tidspec.beq eid eid0) eqn: eq2.
  try eapply tidspec.beq_true_eq in eq2; subst.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.
  eapply Hmbox2 in H5.
  destruct H5. do 2 destruct H. rewrite H in H1; inverts H1.
  eapply go.ecbmod_joinsig_get in H1; eapply EcbMod.join_get_r in H1; eauto.
(*RH_TCBList_ECBList_MUTEX_P*)
  unfolds; splits; intros.
  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2.
  try eapply Hmut1 in H.
  (try destruct H; inverts H).
          mytac;
          destruct (tidspec.beq tid tid0) eqn: eq1; eauto;
          try (eapply tidspec.beq_true_eq in eq1;
          subst; rewrite H3 in H;
          inverts H).
   eapply tidspec.beq_true_eq in eq2. subst.
   eapply tidspec.beq_true_eq in eq1. subst.
   eapply in_remove_tid_false in H4; tryfalse.
   eapply tidspec.beq_true_eq in eq2. subst.
   eapply go.ecbmod_joinsig_get in H1.
  eapply EcbMod.join_get_r in H1; eauto.
  eapply Hmut1. split; eauto.
  eapply in_remove_tid; eauto.
  destruct (tidspec.beq tid tid0) eqn: eq1.
   eapply tidspec.beq_true_eq in eq1. subst.
  eapply Hmut1 in H.
  rewrite H3 in H.
  do 3 destruct H. inverts H. rewrite TcbMod.beq_refl in eq2. tryfalse.
  eapply Hmut1 in H. 
  lets He: go.ecbmod_joinsig_get H1.
  eapply EcbMod.join_get_r in He; eauto.

  rewrite TcbMod.set_sem,EcbMod.set_sem in *.
  destruct (tidspec.beq tid tid0) eqn: eq1;
  inverts H; tryfalse.
  destruct (tidspec.beq eid eid0) eqn: eq2.
  eapply tidspec.beq_true_eq in eq2.
  subst.
  lets He: go.ecbmod_joinsig_get H1.
  eapply EcbMod.join_get_r in He; eauto.
  lets Hin: Hmut2 H5.
  destruct Hin as (en1 & en2 & ew & He' & Hin).
  rewrite He in He'. inverts He'.
  repeat eexists.
  eapply in_neq_remove_in; try eapply tidspec.beq_false_neq; eauto.
  eapply Hmut2; eauto.
  unfolds; intros.
  rewrite TcbMod.set_sem;
  destruct (tidspec.beq tid tid0) eqn: eq1; eauto;
   try eapply tidspec.beq_true_eq in eq1; subst;
  rewrite EcbMod.set_sem in H;
  destruct (tidspec.beq eid eid0) eqn: eq2;
  try eapply tidspec.beq_true_eq in eq2; subst.
  inverts H.
  split; try eapply in_wtset_rm_notin; eauto.
  lets Hin: Hown H.
  destruct Hin as (_ & Hin).
  splits; eauto.
  inverts H.
  rewrite TcbMod.beq_refl in eq1; tryfalse.
  eapply Hown; eauto.
  (*RH_TCBList_ECBList_MUTEX_OWNER_P *)
  lets He: EcbMod.join_joinsig_get H0 H1.
  lets Hot': Hown He.
  destruct Hot' as (_ & Hin).
Require Import OSTimeDlyPure.
  eapply RH_TCBList_ECBList_MUTEX_OWNER_P_hold_tcb; eauto.
  unfolds; splits; intros.
  rewrite EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2. inverts H; tryfalse.
  unfold RH_TCBList_ECBList_MUTEX_OWNER_P in Howp.
  destruct Howp as (Hno & Hpv & Hne).
  eapply Hno; eauto.
  rewrite EcbMod.set_sem in *.
  destruct (tidspec.beq eid eid0) eqn: eq2;  inverts H;
  unfold RH_TCBList_ECBList_MUTEX_OWNER_P in Howp;
  destruct Howp as (Hno & Hpv & Hne);
  eapply Hpv; eauto.  
  rewrite EcbMod.set_sem in *.
  unfold RH_TCBList_ECBList_MUTEX_OWNER_P in Howp;
  destruct Howp as (Hno & Hpv & Hne).
  destruct (tidspec.beq eid eid1) eqn: eq1;  destruct (tidspec.beq eid eid2) eqn: eq2.
  eapply tidspec.beq_true_eq in eq1, eq2. subst. tryfalse.
  eapply tidspec.beq_true_eq in eq1. subst. inverts H.
  eapply go.ecbmod_joinsig_get in H1. eapply Hne; eauto.
  eapply tidspec.beq_true_eq in eq2. subst. inverts H4.
  eapply go.ecbmod_joinsig_get in H1; eauto.
  eapply Hne; eauto.
Qed.
Require Import sem_lab.
Lemma R_Prio_No_Dup_hold_gen
: forall p p' tls st st' m m' tid,
  prio_available p' tls ->
  TcbMod.get tls tid = Some (p, st, m) ->
  R_Prio_No_Dup tls ->
  R_Prio_No_Dup (TcbMod.set tls tid (p', st', m')).
Proof.
unfold R_Prio_No_Dup.
intros.
rewrite TcbMod.set_sem in *.
destruct (tidspec.beq tid tid0) eqn: eq1.
apply tidspec.beq_true_eq in eq1.
subst.
destruct (tidspec.beq tid0 tid') eqn: eq2;
try (apply tidspec.beq_true_eq in eq2; subst ; tryfalse).
inverts H3.
eapply semacc_int_eq_false.
eapply H; eauto.
destruct (tidspec.beq tid tid') eqn: eq2.
apply tidspec.beq_true_eq in eq2; subst.
inverts H4.
eapply semacc_int_eq_false.
rewrite Int.eq_sym.
eapply H; eauto.
eapply H1; eauto.
Qed.

Lemma TCBList_P_post_msg_gen
: forall (v'42 : val) (v'48 : list vallist) (v'47 : TcbMod.map)
         (v'60 : val) (v'50 : list vallist) (v'37 : vallist)
         (v'59 v'49 v'44 : TcbMod.map) (v'63 v'64 v'65 : val)
         (v'51 v'52 v'53 v'54 v'55 v'56 : int32) (x00 : addrval)
         (v'58 : block) (v'40 v'38 : int32) (prio : priority)
         (st : taskstatus) (msg : msg)
         (v'7 v'62 v'43 : TcbMod.map) (v'36 : vallist) 
         (v'39 : int32) (v'13 : vallist) (vhold : addrval) x,
    Int.unsigned v'38 <= 7 ->
    Int.unsigned v'39 <= 7 ->
    nth_val' (Z.to_nat (Int.unsigned v'39)) OSMapVallist = Vint32 v'40 ->
    prio_in_tbl ((v'38<<ᵢ$ 3)+ᵢv'39) v'13 ->
    RL_RTbl_PrioTbl_P v'13 v'36 vhold ->
    nth_val' (Z.to_nat (Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39))) v'36 =
    Vptr (v'58, Int.zero) ->
    R_PrioTbl_P v'36 v'7 vhold ->
    array_type_vallist_match Int8u v'37 ->
    length v'37 = ∘OS_RDY_TBL_SIZE ->
    TcbMod.join v'44 v'43 v'7 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg) v'62 v'7 ->
    get_last_tcb_ptr v'48 v'42 = Some (Vptr (v'58, Int.zero)) ->
    TCBList_P v'42 v'48 v'37 v'47 ->
    TCBList_P v'60 v'50 v'37 v'59 ->
    TcbJoin (v'58, Int.zero) (prio, st, msg) v'59 v'49 ->
    TcbMod.join v'47 v'49 v'44 ->
    TCBNode_P
      (v'60
         :: v'63
         :: v'64
         :: v'65
         :: Vint32 v'51
         :: Vint32 x
         :: Vint32 v'52
         :: Vint32 v'53
         :: Vint32 v'54
         :: Vint32 v'55 :: Vint32 v'56 :: nil) v'37
      (prio, st, msg) ->
    TCBList_P v'42
              (v'48 ++
                    (v'60
                       :: v'63
                       :: Vnull
                       :: Vptr x00
                       :: V$0
                       :: Vint32 ($ OS_STAT_RDY)
                       :: Vint32 v'52
                       :: Vint32 v'53
                       :: Vint32 v'54
                       :: Vint32 v'55 :: Vint32 v'56 :: nil)
                    :: v'50)
              (update_nth_val (Z.to_nat (Int.unsigned v'38)) v'37
                              (val_inj
                                 (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37)
                                     (Vint32 v'40))))
              (TcbMod.set v'44 (v'58, Int.zero) (prio, rdy, Vptr x00)).
Proof.
  intros.
  unfolds in H5.
  destruct H5 as (Ha1 & Ha2 & Ha3).
  assert ( 0 <= Int.unsigned ((v'38<<ᵢ$ 3)+ᵢv'39) < 64).
  clear -H H0.
  mauto.
  unfold nat_of_Z in Ha1.
  eapply nth_val'_imp_nth_val_vptr in H4.
  lets Hps : Ha1 H5 H4.
  
  lets Hgs : tcbjoin_get_a H9.
  assert ((v'58, Int.zero) <> vhold) as Hnvhold.
  apply Ha2 in Hgs.
  destruct Hgs;auto.
  apply Hps in Hnvhold.
  clear Hps.
  simpljoin.
  unfold get in *; simpl in *.
  rewrite H16 in Hgs.
  inverts Hgs.
  remember ((v'38<<ᵢ$ 3)) as px.
  remember (v'39) as py.
  clear Heqpy.
  remember (px+ᵢpy) as prio.
  remember ( (v'58, Int.zero)) as tid.
  lets Hps : tcbjoin_set_ex (prio,st,msg) (prio,rdy,Vptr x00)  H14;eauto.
  destruct Hps as (b&Htx & Hty).
  remember (val_inj
              (or (nth_val' (Z.to_nat (Int.unsigned v'38)) v'37) (Vint32 v'40))) as Hv.
  assert (0<= Z.to_nat (Int.unsigned v'38) <8)%nat.
  clear -H.
  mauto.
  lets Hsx : n07_arr_len_ex H6 H7; eauto.
  destruct Hsx as (vx & Hnth & Hi).
  lets Hns :  nth_val_nth_val'_some_eq  Hnth.
  rewrite Hns in HeqHv.
  simpl in HeqHv.
  subst Hv.
  assert (v'38 = Int.shru prio ($ 3)).
  subst.
  clear - H H0.
  mauto.
  rewrite H19.
  assert (v'40 = ($ 1<<ᵢ(prio &ᵢ$ 7))).  
  rewrite Heqprio.
  rewrite Heqpx.
  assert ((((v'38<<ᵢ$ 3)+ᵢpy)&ᵢ$ 7) = py).
  clear -H H0.
  mauto.
  rewrite H20.
  clear -H0 H1.
  mautoext.
  rewrite H20.
  eapply TCBList_P_Combine; eauto.
  eapply TCBList_P_rtbl_add_simpl_version; eauto.
  rewrite <-H19.
  auto.
  intros.
  unfolds in Ha3.
  lets Hsx : tcbjoin_join_get_neq H13 H14 H21.
  destruct Hsx.
  eapply Ha3; eauto.
  lets Hacb  :  TcbMod.join_get_l H8 H23; eauto.
  simpl.
  do 4 eexists; splits; eauto.
  unfolds; simpl; eauto.
  unfold sig in *; simpl in *.
  eauto.
  unfolds.
  fsimpl.
  usimpl H15.
  usimpl H22.
  splits.
  unfolds; simpl; auto.
  unfolds; simpl; auto.
  funfold H23.
  unfolds.
  do 6 eexists; splits; try solve [unfolds; simpl;auto].
  lia.
  splits; eauto.
  eexists.
  split.
  unfolds;simpl; eauto.
  auto.
  unfolds.
  splits.
  unfolds.
  intros.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  splits; try solve [unfolds; simpl;auto].
  eexists; eauto.
  unfolds.
  intros.
  inverts H15.
  splits; try solve [unfolds; simpl;auto].
  unfolds.
  splits; try solve [unfolds; simpl;auto].
  apply prio_in_tbl_orself ; auto.
  unfolds.
  splits.
  unfolds.
  intros.
  usimpl H22.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  usimpl H25.
  false.
  rewrite H26 in H19.
  rewrite H19 in Hnth.
  rewrite H26 in H17.
  rewrite H26 in H22.
  lets Hfs :  prio_notin_tbl_orself  H17 Hnth.
  tryfalse.

  unfolds.
  intros.
  usimpl H22.
  unfolds.
  intros.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  usimpl H25.

  unfolds.
  intros.
  usimpl H22.
  unfolds.
  intros.
  unfolds in H15.
  fsimpl.
  usimpl H15.
  usimpl H25.
  
  unfolds.
  intros. unfolds in H25; tryfalse.
  unfolds.
  splits; try solve [
                unfolds;
                introv Hf; inverts Hf].
  eapply TCBList_P_rtbl_add_simpl_version; eauto.
  rewrite <-H19.
  auto.
  intros.
  lets Hnas : tcbjoin_tid_neq H13 H21.
  unfolds in Ha3.
  eapply Ha3; eauto.
  lets Haxc  : TcbMod.join_get_r H13 H21.
  lets Haa : TcbMod.join_get_r H14 Haxc.
  lets Ad :  TcbMod.join_get_l H8 Haa; eauto.
Qed.

    Lemma return_rh_ctcb :forall v'52 v'39 a b c, RH_CurTCB (v'52, Int.zero) (TcbMod.set v'39 (v'52, Int.zero) (a, b, c)).
    Proof.
      intros.
      unfold RH_CurTCB in *.
      rewrite TcbMod.set_a_get_a.
      eauto.
      go.
    Qed.

Lemma rg1 :  forall x2 x6 ,  0 <= Int.unsigned x2 < 64->
                             x6 = $ Int.unsigned x2&ᵢ$ 7 ->
                             0<= Int.unsigned x6 < 8.
Proof.
  intros.
  subst x6.

  mauto.
Qed.

Lemma rg2 :  forall x2 x7 ,  0 <= Int.unsigned x2 < 64->
                             x7 = Int.shru ($ Int.unsigned x2) ($ 3) ->
                             0<= Int.unsigned x7 < 8.
Proof.
  intros.
  subst x7.
  mauto.
Qed.


Lemma something_in_not_nil : forall (T:Type) (y: @list T), y<>nil -> exists x, In x y.
Proof.
  intros T y.
  elim y.
  intro; tryfalse.
  intros.
  exists a.
  simpl.
  left; auto.
Qed.

Lemma post_exwt_succ_pre_mutex'
: forall (v'36 v'13 : vallist) (v'12 : int32) 
         (v'32 : block) (v'15 : int32) (v'24 : val) 
         (v'35 v'0 : val) (v'8 : tid) (v'9 v'11 : EcbMod.map)
         x  (x1 : waitset)
         (v'6 v'10 : EcbMod.map) (v'38 v'69 v'39 : int32) 
         (v'58 : block) (a : priority)
         (c : msg) (v'62 v'7 : TcbMod.map) 
         (vhold : addrval) y petbl pegrp petbl_addr,
    v'12 = Int.zero ->
    R_PrioTbl_P v'36 v'7 vhold ->
    RL_Tbl_Grp_P v'13 (Vint32 v'12) ->
    R_ECB_ETbl_P (v'32, Int.zero)
                 (V$OS_EVENT_TYPE_MUTEX
                   :: Vint32 v'12
                   :: Vint32 v'15 :: v'24 :: v'35 :: v'0 :: Vint32 pegrp :: petbl_addr :: nil,
                  v'13, petbl) v'7 ->
    RH_TCBList_ECBList_P v'11 v'7 v'8 ->
    EcbMod.join v'9 v'10 v'11 ->
    EcbMod.joinsig (v'32, Int.zero) (absmutexsem x y , x1) v'6 v'10 ->
    x1 = nil
.
Proof.
  intros.
  unfolds in H2.
  destruct H2 as (H2 & H2' & _).
  destruct H2 as (_ & _ & _ & H2).
  destruct H2' as (_ & _ & _ & H2').
  unfolds in H2.
  unfolds in H2'.
  

  unfolds in H3.
  unfolds in H1.
  unfolds in H0.
  destruct H3 as (_ & _ & _ & H3).
  unfolds in H3.
  destruct H3 as (H3 & H3').

  lets Hg : EcbMod.join_joinsig_get H4 H5.
  clear H4 H5.
  assert ( x1 = nil \/ x1 <> nil) by tauto.
  destruct H4; intros; auto.

  idtac.
  apply something_in_not_nil in H4.
  inversion H4.
  assert (EcbMod.get v'11 (v'32, Int.zero) = Some (absmutexsem x y, x1) /\ In x0 x1) by tauto.
  lets aadf : H3 H6.
  mytac.
  lets bbdf : H2' H13.
  destruct bbdf.
  unfolds in H.
  do 3 destruct H.
  destruct H as (Ha & Hb & Hc & Hd& He).
  cut ( 0<=(∘(Int.unsigned x7)) <8)%nat.
  intro.
  assert (V$0 = V$0) by auto.
  lets adfafd : H1 H Hd H15. (* change H14 -> H15 *)
  destruct adfafd.
  destruct H14. (* change H13 -> H14 *)
  destruct H15. (* change H14 -> H15 *)
  cut ( $ 0&ᵢ($ 1<<ᵢ$ Z.of_nat ∘(Int.unsigned x7)) = $ 0).
  intro.
  apply H16 in H14. (* change H13, H15 -> H14, H16 *)
  subst x8.

  lets rg : rg1 Ha Hb.
  clear -He rg.
  false.
  gen He.
  mauto.

  lets rg : rg2 Ha Hc.
  clear -rg.
  mauto.

  lets rg : rg2 Ha Hc.
  clear -rg.
  mauto.
Qed.

Lemma mutexandnotmutex :  Int.eq ($ OS_STAT_MUTEX&ᵢInt.not ($ OS_STAT_MUTEX)) ($ OS_STAT_RDY) = true.
Proof.
  rewrite Int.and_not_self.
  int auto.
  unfold OS_STAT_RDY.
  lia.
Qed.
