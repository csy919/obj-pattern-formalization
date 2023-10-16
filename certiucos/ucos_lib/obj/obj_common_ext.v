Require Import ucos_include.
Require Import os_ucos_h.
Require Import symbolic_lemmas.
Require Import Aarray_new_common.
Require Import Aarray_new_common_extend.  
Require Import obj_common.

Require Import seplog_pattern_tacs. 

Open Scope code_scope.
Open Scope int_scope.
Open Scope Z_scope.

Definition ObjArr_full_P objvl := 
  forall i vl1,
    (0 <= i /\ i < Z.of_nat (length objvl)) ->
    nth_vallist (nat_of_Z i) objvl = Some vl1 ->
    ~(V_ObjPtr vl1 = Some Vnull).

Definition nth_ObjArr_free_P i objvl :=
  exists vl1,
    0 <= i /\ i < Z.of_nat (length objvl) /\ 
      nth_vallist (nat_of_Z i) objvl = Some vl1 /\
      V_ObjPtr vl1 = Some Vnull.

Lemma aobjarr_len: 
  forall s vl, s |= AObjArr vl -> length vl = ∘ (MAX_OBJ_NUM).
Proof.  
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  auto.
Qed. 

Lemma AObjArr_unfold_any_idx: 
  forall s objvl idxv,
    s |= AObjArr objvl ->
    (idxv < length objvl)%nat ->
    s |= EX vll1 vll2 b i vl ,
        GV obj_arr @ service_obj_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray service_obj_t idxv) vll1 ** 
          Astruct (b, i +ᵢ $ Z.of_nat (idxv * (typelen service_obj_t))) service_obj_t vl ** 
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idxv) * (typelen service_obj_t))))
          (Tarray service_obj_t (∘ (MAX_OBJ_NUM - Z.of_nat (S idxv)))) vll2 ** 
          [| new_array_type_vallist_match service_obj_t objvl |] **
          [| length objvl = ∘ (MAX_OBJ_NUM) |] **
          [| objvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idxv /\ length vll2 = ∘ (MAX_OBJ_NUM - Z.of_nat (S idxv)) |] **
          [| Z.of_nat (S idxv) <= MAX_OBJ_NUM |].  
Proof. 
  introv Hsat.
  assert (Hlengt: Z.of_nat (length objvl * typelen service_obj_t) <= Int.max_unsigned). 
  { erewrite aobjarr_len; eauto.  simpl. mauto. }
  introv Hlenle. 
  unfold AObjArr in Hsat.
  simpl_sat Hsat. 
  simpljoin1.
  rewrite <- H11 in *.
  assert (Hlen: (length objvl = idxv + (length objvl - idxv))%nat) 
    by auto with arith.
  lets Hsplit: (firstn_skipn idxv objvl). 
  rewrite <- Hsplit in H8 at 2.
  rewrite Hlen in H8. 
  destruct x.
  lets Harrs0: Aarray_new_split_strong H8.
  assert (HSidx: (S idxv <= length objvl)%nat) by auto with arith.
  assert (Harith: Z.of_nat (S idxv * typelen service_obj_t) <= Int.max_unsigned). 
  {
    apply Z.le_trans with (m:=Z.of_nat (length objvl * typelen service_obj_t));
      auto.
    apply inj_le. 
    apply NPeano.Nat.mul_le_mono_r; auto.
  }
  lets Harrs00: Harrs0 Harith.
  clear Harrs0.
  assert (Hlens: length (firstn idxv objvl) = idxv /\ length (skipn idxv objvl) = (length objvl - idxv)%nat).
  {
    split. 
    apply firstn_length_le. auto with arith.
    apply skipn_length.
  }
  lets Harrs: Harrs00 Hlens.
  clear Harrs00.
  destruct Harrs.
  simpljoin1.
  destruct s as [[[[[[]]]]]].
  change_smo H12.
  change_smo H13.
  change_smo H3.

  assert (HlenS: (length objvl - idxv = S (length objvl - (S idxv)))%nat).
  {
    rewrite NPeano.Nat.sub_succ_r.
    rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
    rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
  }
  rewrite HlenS in H13.
  assert (Hln: (length (skipn idxv objvl) > 0)%nat).
  {
    rewrite skipn_length.  
    cut (0 < length objvl - idxv)%nat.
    auto with arith.
    rewrite <- NPeano.Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r. auto.
  }
  apply length_exists in Hln.
  destruct Hln as (vh & vlt & Hlst). rewrite Hlst in H13.
  apply Aarray_new'_succ_imp in H13.
  assert (Hsimp: $ Z.of_nat (idxv * typelen service_obj_t) +ᵢ  $ Z.of_nat (typelen service_obj_t) =
                                 $ Z.of_nat (S idxv * typelen service_obj_t)).
  {
    rewrite <- Nat.add_1_r.
    rewrite NPeano.Nat.mul_add_distr_r. 
    rewrite Nat2Z.inj_add.
    change (1 * typelen service_obj_t)%nat with (typelen service_obj_t).
    simpl. 
    assert (Ha: Z.of_nat (idxv * 8) = Int.unsigned ($ (Z.of_nat (idxv * 8)))). 
    {
      rewrite int_usign_eq; auto. auto with zarith.
      rewrite H11 in Hlen. unfold_usr_max_evts_in H11.
      simpl in H11.
      rewrite pos_to_nat_20 in H11.  
      rewrite H11 in Hlengt.
      apply lt_imply_le.
      apply Z.lt_le_trans with (m:=160). 
      mauto. mauto.
    }
    assert (Hb: 8 = Int.unsigned ($8)) by auto.
    rewrite Ha at 2. rewrite Hb at 2.
    rewrite <- Int.add_unsigned. auto.
  }
  rewrite Int.add_assoc in H13. rewrite Hsimp in H13.
  assert (Hc: (∘ (MAX_OBJ_NUM - Z.of_nat (S idxv)) = length objvl - S idxv)%nat).
  {
    rewrite H11.
    rewrite sub_Z_nat; auto. 
    rewrite <- H11. 
    auto.
  }
  rewrite Hc. 
  destruct H13.
  simpljoin1.
  change_smo H17.
  change_smo H18.
  unfold Aarray_new' in H17.
  unfold service_obj_t in H17. fold service_obj_t in H17.
  apply step_prop.StarEmpER in H17.

  simpl_sat_goal.

  exists (firstn idxv objvl). exists vlt. exists b. exists i.
  exists vh. exists x0. exists x1. exists m. exists x3. eexists. exists o.
  splits; eauto.
  
  simpl in H10. simpl in H5. 
  destruct H10 as (Hx7emp & Hx10emp).
  subst x7. unfold emposabst in Hx10emp. subst x10. 
  assert (x6 = x1). { apply map_join_emp' in H5. auto. }
  subst x6.
  simpl in H7. simpl in H2.
  assert (x9 = x4). { apply map_join_emp' in H7. auto. }
  subst x9.
  simpl in H6. 
  simpl in H1.

  exists x.  do 5 eexists. splits; eauto.
  eexists x5. do 2 eexists. exists x14. do 2 eexists. 
  splits; eauto.

  unfold Aarray_new.
  exists x12. do 2 eexists. exists x15. do 2 eexists.
  splits; eauto.
  instantiate (1:=empenv). join auto.
  instantiate (1:=emp). join auto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split; auto. simpl. split; auto. unfolds. auto.

  do 6 eexists. splits; eauto. 
  join auto. join auto.
  split; auto. simpl. split; auto. unfolds. eauto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split. 
  rewrite <- Hsplit at 1. rewrite Hlst. auto.
  simpl. split; auto. unfolds. auto.

  do 6 eexists. splits; eauto.
  join auto. join auto.
  split. split; auto.
  rewrite Hlst in H15. simpl in H15. 
  eapply sub_eq_succ; eauto.
  simpl. split; auto. unfolds. auto.
  rewrite H11 in HSidx.
  apply inj_le in HSidx. simpl in HSidx.
  unfold_usr_max_evts. simpl. 
  unfold MAX_OBJ_NUM.
  auto.
  simpl. split; auto. unfolds. auto.
Qed. 

Lemma AObjArr_unfold_any_idx_frm: 
  forall s objvl idxv P,
    s |= AObjArr objvl ** P ->
    (idxv < length objvl)%nat ->
    s |= (EX vll1 vll2 b i vl ,
        GV obj_arr @ service_obj_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray service_obj_t idxv) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idxv * (typelen service_obj_t))) service_obj_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idxv) * (typelen service_obj_t))))
            (Tarray service_obj_t (∘ (MAX_OBJ_NUM - Z.of_nat (S idxv)))) vll2 ** 
          [| new_array_type_vallist_match service_obj_t objvl |] ** 
          [| length objvl = ∘ (MAX_OBJ_NUM) |] ** 
          [| objvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idxv /\ length vll2 = ∘ (MAX_OBJ_NUM - Z.of_nat (S idxv)) |] ** 
          [| Z.of_nat (S idxv) <= MAX_OBJ_NUM |]) ** P.   
Proof. 
  introv Hsat Hlenle. 
  sep cancel 2%nat 2%nat.
  eapply AObjArr_unfold_any_idx; eauto.
Qed.

Lemma length_vll_aobj_objl: 
  forall s P objl absobjs ecbls (vhold: addrval) tcblh tcbvl fecbh fecbvl, 
    s |= AOBJ objl absobjs ecbls vhold tcblh tcbvl fecbh fecbvl ** P ->
    length objl = ∘ (MAX_OBJ_NUM).   
Proof.
  intros.
  destruct s as [[[[[[]]]]]].
  destruct H. simpljoin1.
  change_smo_hyps.
  unfold AOBJ in H3. 
  simpl_sat H3. simpljoin1.
  unfold AObjs in H11.
  simpl_sat H11. simpljoin1. 
  eapply aobjarr_len; eauto.
Qed.

Lemma AObjArr_select_sn_strong : 
  forall vll1 n vll2 b i s vl P, 
    Z.of_nat(S n) <= MAX_OBJ_NUM ->
    s |= GV obj_arr @ service_obj_t ∗ |-> Vptr (b,i) **
      Aarray_new (b, i) (Tarray service_obj_t n) vll1 **
      Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen service_obj_t)))) service_obj_t vl **
      Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen service_obj_t))))
        (Tarray service_obj_t (∘ (MAX_OBJ_NUM - Z.of_nat(S n)))) vll2 ** P ->
    new_array_type_vallist_match service_obj_t (vll1 ++ (vl::vll2)) ->
    length (vll1 ++ (vl::vll2)) = ∘ (MAX_OBJ_NUM) -> 
    s |= AObjArr (vll1 ++ (vl::vll2)) ** P.
Proof.
  intros.
  assert (Hrgn: Z.of_nat (S n * typelen service_obj_t) <= Int.max_unsigned).
  {
    remember (typelen service_obj_t) as X.  
    unfold service_obj_t in HeqX. simpl in HeqX.  
    rewrite HeqX.
    unfold_usr_max_evts_in H.
    simpl in H.
    unfold MAX_OBJ_NUM in H.
    int auto.
  }
  unfold AObjArr.
  sep pauto.
  assert (Heq: ∘ (MAX_OBJ_NUM) =  Nat.add n (S (∘ (MAX_OBJ_NUM - Z.of_nat(S n))) )).
  unfold nat_of_Z.
  assert (Heq1: Z.to_nat (MAX_OBJ_NUM - Z.of_nat (S n)) 
              = Nat.sub (Z.to_nat (MAX_OBJ_NUM))  (Z.to_nat (Z.of_nat (S n))) ).
  apply Z2Nat.inj_sub.
  eauto with zarith.
  rewrite Heq1.
  eauto with zarith.
  rewrite Heq.
  eapply Aarray_new_compose_strong; eauto.

  sep pauto.
  eapply Aarray_new_succ.
  rewrite Int.add_assoc.
  asserts_rewrite ($ Z.of_nat (n * typelen service_obj_t) +ᵢ  $ Z.of_nat (typelen service_obj_t) 
                   = $ Z.of_nat (S n * typelen service_obj_t)). 
  { int auto. }
  sep pauto.
  unfold service_obj_t. 
  unfold Aarray_new.
  unfold Aarray_new'.
  fold service_obj_t. 
  sep pauto.
Qed.

Lemma AObjArr_select_sn_ex_strong: 
  forall s P objvl,
     s |= EX vll1 n vll2 b i vl ,
             GV obj_arr @ service_obj_t ∗ |-> Vptr (b,i) ** 
             Aarray_new (b, i) (Tarray service_obj_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen service_obj_t)))) service_obj_t vl ** 
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen service_obj_t))))
               (Tarray service_obj_t (∘ (MAX_OBJ_NUM - Z.of_nat(S n)))) vll2 **  
             [| new_array_type_vallist_match service_obj_t objvl |] **  
             [| length objvl = ∘ (MAX_OBJ_NUM) |] **
             [| objvl = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (MAX_OBJ_NUM - Z.of_nat(S n)) |] ** 
             [| Z.of_nat(S n) <= MAX_OBJ_NUM |] ** 
              P ->
    s |= AObjArr objvl ** P.
Proof.
  intros.
  do 6 destruct H.
  sep split in H.
  subst.
  eapply AObjArr_select_sn_strong. 
  eauto.
  eauto.
  sep pauto.
  eauto.
Qed.

Lemma obj_corr': 
  forall vl vll1 vll2 absobjs hld v i, 
    ObjArray_P v (vll1 ++ vl :: vll2) absobjs hld -> 
    Int.ltu i Int.zero = false -> 
    length vll1 = Z.to_nat (Int.unsigned i) -> 
    (forall j, v = Vint32 j ->
               Int.ltu j Int.zero = false /\ Int.unsigned j + Int.unsigned i <= Int.max_unsigned) ->  
    exists j oid_opt att, 
      v = Vint32 j /\
      get absobjs (j +ᵢ i) = Some (oid_opt, att) /\
          V_ObjAttr vl = Some (Vint32 att) /\
           ((exists oid, oid_opt = objid oid /\ V_ObjPtr vl = Some (Vptr oid) /\ oid <> hld) \/
           (oid_opt = objholder /\ V_ObjPtr vl = Some (Vptr hld)) \/
              (oid_opt = objnull /\ V_ObjPtr vl = Some Vnull)).
Proof.
  inductions vll1.

  introv Harrp Hi Hlen Hsumrgn.
  simpl in Harrp.
  assert (Hiz: i = Int.zero).
  { 
    simpl in Hlen. destruct (Int.unsigned i) eqn: E.
    apply Int.unsigned_eq_zero; auto.
    int auto. int auto.
  }
  destruct Harrp as (idx & objs' & obj & v' & Hv & Hv' & Hjo & HP & H').
  unfold RHL_OBJ_P in HP.
  destruct obj as [eo kd].
  specialize (HP eo kd (eq_refl _)).
  destruct v eqn: E; try inverts Hv.
  exists idx.
  exists eo kd.
  splits; auto.
  assert (Heq: idx +ᵢ  i = idx). { rewrite Hiz. int auto. }
  rewrite Heq.
  eapply join_sig_get; eauto.
  destructs HP.
  auto. 
  destructs HP. auto.
  
  introv Harrp Hi Hlen Hsumrgn. 
  simpl in Harrp.
  simpl in Hlen.
  assert (Hige: Int.unsigned i >= 1). { auto with zarith. }
  destruct Harrp as (idx & objs' & absobj & v' & Hv & Hv' & Hjo & HP & H').
  eapply IHvll1 with (absobjs:=objs') (i:=Int.sub i ($1)) in H'; eauto.
  destruct H' as (j & eo & kd & H').
  exists idx eo kd.
  simpljoin1. splits; auto.
  inverts H.
  rewrite pos_add_sub_one in H0; auto.
  (* Print map_join_get_none'. *)
  eapply join_lib.map_join_get_none' with (m2:=objs'); eauto.
  apply get_a_sig_a'.
  specialize (Hsumrgn idx (eq_refl _)). 
  destruct Hsumrgn. apply pos_add_i_neq; auto.
  specialize (Hsumrgn idx (eq_refl _)).
  mytac.
  specialize (Hsumrgn idx (eq_refl _)).
  mytac.
  apply i_ge1_i_sub1_ge0. auto.
  int auto. int auto. 
  introv H_v'.
  subst v. subst v'. inverts H_v'.
  specialize (Hsumrgn idx (eq_refl _)).
  destruct Hsumrgn as (Hpos & Hadd).
  split. int auto. int auto.
  int auto. int auto. int auto.
Qed. 

Lemma obj_corr: 
  forall vl vll1 vll2 absobjs hld i, 
    ObjArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) absobjs hld -> 
    length vll1 = Z.to_nat (Int.unsigned i) -> 
    Int.ltu i Int.zero = false -> 
    Int.unsigned i <= Int.max_unsigned ->  
    exists oid_opt att, 
      get absobjs i = Some (oid_opt, att) /\ 
        V_ObjAttr vl = Some (Vint32 att) /\ 
        ((exists oid, oid_opt = objid oid /\ V_ObjPtr vl = Some (Vptr oid) /\ oid <> hld) 
         \/ (oid_opt = objholder /\ V_ObjPtr vl = Some (Vptr hld)) 
         \/ (oid_opt = objnull /\ V_ObjPtr vl = Some Vnull)).
Proof.
  introv HP Hvll1 Hlt Hle.
  eapply obj_corr' with (i:=i) in HP; eauto.
  2: {
    introv Hj0. 
    split. inv Hj0. int auto. inverts Hj0. int auto.
  }
  rewrite <- (Int.add_zero_l i).
  simpljoin1.
  do 2 eexists. splits; eauto.
  inverts H.
  auto.
Qed.


Lemma ObjArr_full_imp_no_free:
  forall objvl, ObjArr_full_P objvl -> ~(exists i, nth_ObjArr_free_P i objvl). 
Proof.
  unfold nth_ObjArr_free_P. 
  unfold ObjArr_full_P. 
  intros.
  do 2 (eapply Classical_Pred_Type.all_not_not_ex; intros).
  pure_auto.
Qed.

Lemma ObjArr_free_imp_no_full:
  forall objvl, (exists i, nth_ObjArr_free_P i objvl) -> ~(ObjArr_full_P objvl).  
Proof.
  unfold nth_ObjArr_free_P.
  unfold ObjArr_full_P. 
  intros.
  pure_auto.
  do 3 destruct H.
  destruct H1.
  destruct H2.
  eapply H0; eauto.
Qed.


Lemma ObjArr_free_dec :
  forall objvl, (exists i, nth_ObjArr_free_P i objvl) \/ ObjArr_full_P objvl.   
Proof.
  intros.
  assert (Ht: (ObjArr_full_P objvl) \/ ~(ObjArr_full_P objvl)) by tauto. 
  destruct Ht. pure_auto.
  left.
  unfold nth_ObjArr_free_P in *.
  unfold ObjArr_full_P in *. 
  eapply Classical_Pred_Type.not_all_ex_not in H.
  destruct H.
  eapply Classical_Pred_Type.not_all_ex_not in H.
  destruct H.
  eapply Classical_Prop.imply_to_and in H; destruct H.
  eapply Classical_Prop.imply_to_and in H0; destruct H0.
  destruct H.
  repeat eexists; eauto.
  tauto.
Qed.

Lemma ObjArr_select_sn_ex_strong_frm: 
  forall s objvl,
     s |= EX vll1 n vll2 b i vl ,
             GV obj_arr @ service_obj_t ∗ |-> Vptr (b,i) **
             Aarray_new (b, i) (Tarray service_obj_t n) vll1 **
             Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen service_obj_t)))) service_obj_t vl **
             Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen service_obj_t))))
               (Tarray service_obj_t (∘ (MAX_OBJ_NUM - Z.of_nat(S n)))) vll2 **
             [| new_array_type_vallist_match service_obj_t objvl |] **
             [| length objvl = ∘ (MAX_OBJ_NUM) |] **
             [| objvl = vll1 ++ (vl::vll2) |] ** 
             [| length vll1 = n /\ length vll2 = ∘ (MAX_OBJ_NUM - Z.of_nat(S n)) |] **
             [| Z.of_nat(S n) <= MAX_OBJ_NUM |] ->
    s |= AObjArr objvl.
Proof.
  intros.
  apply astar_r_aemp_elim.
  eapply AObjArr_select_sn_ex_strong.
  sep auto.
Qed.

Lemma ObjArr_full_P_nil : ObjArr_full_P nil.
Proof.
  unfold ObjArr_full_P.
  simpl. auto with zarith.
Qed.

Lemma ObjArr_full_P_succ : 
  forall a vl, ObjArr_full_P (a :: vl) <-> (ObjArr_full_P (a::nil) /\ ObjArr_full_P vl). 
Proof.
  unfold ObjArr_full_P. 
  (* simpl. *)
  split; intros.
  simpl in *.
  split; intros.
  eapply H. instantiate (1:= i). int auto.
  destruct (∘ i); tryfalse. auto.
  eapply H. instantiate (1:= (i + 1)). int auto.
  assert (Hi: (∘ (i + 1)) = ((∘ i) + (∘ 1))%nat).
  eapply nat_of_Z_plus; auto with zarith.
  rewrite Hi.
  change (∘ 1) with 1%nat.
  assert (Hi': (∘ i + 1)%nat = S (∘ i)).
  auto with zarith.
  rewrite Hi'. auto.
  destruct H.
  destruct H0.
  assert (Hi: i= 0 \/ i <> 0) by tauto.
  (* simpl in *. *)
  destruct Hi.
  eapply H. simpl in *. eauto with zarith. subst i. auto.
  eapply H2. instantiate (1:= i - 1). simpl in *. eauto with zarith.
  assert (Hsub: i = i - 1 +1).
  rewrite Z.sub_add. auto.
  rewrite Hsub in H1.
  assert (Hi: ∘ (i - 1 + 1) = ((∘ (i - 1)) + (∘ 1))%nat).
  eapply nat_of_Z_plus; auto with zarith.
  rewrite Hi in H1.
  change (∘ 1) with 1%nat in H1.
  assert (Hi': (∘ (i - 1) + 1)%nat = S (∘ (i - 1))) by auto with zarith.
  rewrite Hi' in H1.
  simpl in H1. auto.
Qed.

Lemma ObjArr_full_P_split:
  forall vl1 vl2, (ObjArr_full_P vl1 /\ ObjArr_full_P vl2)  <-> ObjArr_full_P (vl1 ++ vl2). 
Proof.
  induction vl1; intros.
  simpl. split; try pure_auto. apply ObjArr_full_P_nil.
  simpl.
  rewrite ObjArr_full_P_succ.
  rewrite ObjArr_full_P_succ with (vl:= vl1 ++ vl2).
  rewrite <- IHvl1.
  tauto.
Qed.

Lemma AObjArr_split: 
  forall s vll1 vl vll2,
    s |= AObjArr (vll1 ++ (vl :: vll2)) ->
    s |= EX idx b i,
           GV obj_arr @ service_obj_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray service_obj_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen service_obj_t))) service_obj_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen service_obj_t))))
          (Tarray service_obj_t (∘ (MAX_OBJ_NUM - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match service_obj_t (vll1 ++ (vl :: vll2)) |] **
          [| length (vll1 ++ (vl :: vll2)) = ∘ (MAX_OBJ_NUM) |] **
          [| length vll1 = idx /\ length vll2 = ∘ (MAX_OBJ_NUM - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= MAX_OBJ_NUM |].  
Proof.
  intros.
  unfold AObjArr in H.
  destruct H.
  destruct x.
  sep lift 2%nat in H.
  sep split in H.
  destruct H0.
  lets Hl: H1.
  rewrite app_length in Hl.
  rewrite <- Hl in H.
  assert ((length vll1 < ∘ (MAX_OBJ_NUM))%nat).
  rewrite <- Hl. simpl.
  auto with zarith.
  assert (Hl2: length vll2 = ∘ (MAX_OBJ_NUM - Z.of_nat (S (length vll1)))).
  {
    unfold nat_of_Z in *.
    assert (Z.to_nat (MAX_OBJ_NUM - Z.of_nat (S (length vll1))) =
              (Z.to_nat (MAX_OBJ_NUM) - Z.to_nat(Z.of_nat (S (length vll1))))%nat).
    eapply Z2Nat.inj_sub; auto with zarith.
    rewrite H3.
    rewrite <- Hl.
    rewrite Nat2Z.id.
    simpl.
    auto with zarith.
  }
  eapply Aarray_new_split_strong_frm in H; try (split; auto).
  2: { unfold service_obj_t. simpl typelen. 
       unfold MAX_OBJ_NUM in H2.
       assert (S (length vll1) < 21)%nat by auto with arith.
       clear -H3. int auto.
 }
  sep pauto.
  sep cancel 1%nat 1%nat.
  change (length (vl :: vll2)) with (S (length vll2)) in H.
  eapply Aarray_new_succ_imp in H.
  rewrite Int.add_assoc in H.
  assert (Hsuc: ($ Z.of_nat (length vll1 * typelen service_obj_t) +ᵢ
                                                                     $ Z.of_nat (typelen service_obj_t)) =
                  $ Z.of_nat (S (length vll1) * typelen service_obj_t) ).
  {
    clear -Hl H2.
    unfold service_obj_t. simpl typelen.
    assert ((S (length vll1) * 8)%nat = ((((length vll1) * 8)%nat + 8)%nat)).
    auto with zarith.
    rewrite H.
    rewrite Nat2Z.inj_add.
    change ∘ (MAX_OBJ_NUM) with 20%nat in H2.
    int auto.
  }
  rewrite Hsuc in H.
  rewrite <- Hl2.
  sep cancel 2%nat 2%nat.
  unfold Aarray_new in H.
  unfold Aarray_new' in H. unfold service_obj_t in H.
  fold service_obj_t in H.
  sep pauto.
  unfold MAX_OBJ_NUM in H2.
  unfold MAX_OBJ_NUM.
  clear -H2.
  assert (20 = Z.of_nat (∘ 20)) by mauto. 
  auto with zarith.
Qed. 

Lemma AObjArr_split_frm: 
  forall s vll1 vl vll2 P,
    s |= AObjArr (vll1 ++ (vl :: vll2)) ** P ->
    s |= EX idx b i,
           GV obj_arr @ service_obj_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray service_obj_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen service_obj_t))) service_obj_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen service_obj_t))))
          (Tarray service_obj_t (∘ (MAX_OBJ_NUM - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match service_obj_t (vll1 ++ (vl :: vll2)) |] **
          [| length (vll1 ++ (vl :: vll2)) = ∘ (MAX_OBJ_NUM) |] **
          [| length vll1 = idx /\ length vll2 = ∘ (MAX_OBJ_NUM - Z.of_nat (S idx)) |] **
          [| Z.of_nat (S idx) <= MAX_OBJ_NUM |] ** P.  
Proof.
  intros.
  unfold AObjArr in H.
  sep normal in H.
  destruct H.
  destruct x.
  sep lift 2%nat in H.
  sep split in H.
  destruct H0.
  lets Hl: H1.
  rewrite app_length in Hl.
  rewrite <- Hl in H.
  assert ((length vll1 < ∘ (MAX_OBJ_NUM))%nat).
  rewrite <- Hl. simpl.
  auto with zarith.
  assert (Hl2: length vll2 = ∘ (MAX_OBJ_NUM - Z.of_nat (S (length vll1)))).
  {
    unfold nat_of_Z in *.
    assert (Z.to_nat (MAX_OBJ_NUM - Z.of_nat (S (length vll1))) =
              (Z.to_nat (MAX_OBJ_NUM) - Z.to_nat(Z.of_nat (S (length vll1))))%nat).
    eapply Z2Nat.inj_sub; auto with zarith.
    rewrite H3.
    rewrite <- Hl.
    rewrite Nat2Z.id.
    simpl.
    auto with zarith.
  }
  eapply Aarray_new_split_strong_frm in H; try (split; auto).
  2: { unfold service_obj_t. simpl typelen. 
       unfold MAX_OBJ_NUM in H2.
       assert (S (length vll1) < 21)%nat by auto with arith.
       int auto. }
  sep pauto.
  sep cancel 1%nat 1%nat.
  change (length (vl :: vll2)) with (S (length vll2)) in H.
  eapply Aarray_new_succ_imp in H.
  rewrite Int.add_assoc in H.
  assert (Hsuc: ($ Z.of_nat (length vll1 * typelen service_obj_t) +ᵢ
                                                                     $ Z.of_nat (typelen service_obj_t)) =
                  $ Z.of_nat (S (length vll1) * typelen service_obj_t) ).
  {
    clear -Hl H2.
    unfold service_obj_t. simpl typelen.
    assert ((S (length vll1) * 8)%nat = ((((length vll1) * 8)%nat + 8)%nat)).
    auto with zarith.
    rewrite H.
    rewrite Nat2Z.inj_add.
    unfold MAX_OBJ_NUM in H2. 
    int auto.
    clear -H2. int auto. 
    cut (Z.of_nat (length vll1 * 8) < 4294967295).
    intro. int auto.
    apply Z.lt_le_trans with (m:=160).
    asserts_rewrite (160 = Z.of_nat (∘ 160)). auto with zarith.
    apply inj_lt. 
    asserts_rewrite (∘ 160 = (∘ 20) * 8)%nat. mauto.
    apply mult_lt_compat_r; auto. mauto. int auto.
  }
  rewrite Hsuc in H.
  rewrite <- Hl2.
  sep cancel 2%nat 2%nat.
  unfold Aarray_new in H.
  unfold Aarray_new' in H. unfold service_obj_t in H.
  fold service_obj_t in H.
  sep pauto.
  unfold MAX_OBJ_NUM in H2. 
  unfold MAX_OBJ_NUM. 
  clear -H2.
  asserts_rewrite (20 = Z.of_nat (∘ 20)). mauto.
  auto with zarith.
Qed.

Lemma new_array_type_vallist_match_sem_getp:
  forall vll1 vl vll2,
    new_array_type_vallist_match service_obj_t (vll1 ++ (vl :: vll2)) ->
    exists v, V_ObjPtr vl = Some v /\ isptr v.
Proof.
  intros.
  eapply new_array_type_vallist_match_split in H; eauto.
  destruct H as (_ & _ & Hsp).
  lets Hvl: struct_type_vallist_match_elim_2 Hsp.
  destruct Hvl. destruct H.
  subst vl.
  simpl in Hsp.
  destruct Hsp as (_ & Hk & _).
  exists x0.
  unfold V_ObjPtr. unfold isptr.
  simpl. split; auto.
  destruct x0; tryfalse; pure_auto.
Qed.

Lemma aobjarr_len_frm:  
  forall s vl P, s |= AObjArr vl ** P -> length vl = ∘ (MAX_OBJ_NUM).
Proof.  
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  destruct H3.
  simpl_sat H. simpljoin1.
  auto.
Qed. 


Lemma nth_ObjArr_free_P_range: 
  forall s vl P i, s |= AObjArr vl ** P -> nth_ObjArr_free_P i vl -> 0 <= i < MAX_OBJ_NUM.
Proof. 
  intros.
  funfold H0.
  apply aobjarr_len_frm in H.
  rewrite H in *.
  auto with zarith.
Qed.

Lemma obj_getnull:
  forall vl vll1 vll2 objs hld i,
    ObjArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) objs hld ->
    nth_ObjArr_free_P i (vll1 ++ vl :: vll2) ->
    length vll1 = Z.to_nat i ->
    length (vll1 ++ vl :: vll2) = ∘ (MAX_OBJ_NUM) ->
    exists tp,
      get objs (Int.repr i) = Some (objnull, tp) /\
      V_ObjPtr vl = Some Vnull.
Proof.
  introv He Hf Hl1 Hl2.
  funfold Hf.
  rewrite Hl2 in H0.
  change (Z.of_nat ∘ (MAX_OBJ_NUM)) with (MAX_OBJ_NUM) in H0.
  assert (Hi_ran: Int.ltu ($ i) Int.zero = false /\ Int.unsigned ($ i) <= Int.max_unsigned).
  unfold MAX_OBJ_NUM in H0.
  int auto.
  destruct Hi_ran as (Hi1 & Hi2).
  assert (Hi: Int.unsigned (Int.repr i) = i).
  eapply int_usign_eq; auto.
  unfold MAX_OBJ_NUM in H0.
  int auto.
  unfold nat_of_Z in H1.
  rewrite <- Hl1 in H1.
  rewrite nth_vallist_get_idx in H1.
  inverts H1.
  rewrite <- Hi in Hl1.
  lets Hsem: obj_corr He Hl1 Hi1 Hi2.
  mytac.
  unfold V_ObjPtr in *.
  rewrite Hi in Hl1.
  rewrite H4 in H3.
  do 2 destruct H3; mytac; tryfalse.
  repeat eexists.
  apply H1.
Qed.

Lemma ObjArray_P_nth_vallist: 
  forall objvl idxv absobjs hld i, 
    ObjArray_P idxv objvl absobjs hld -> 
    0 <= i < Z.of_nat (length objvl)  ->
    exists vl, nth_vallist ∘ i objvl = Some vl. 
Proof.
  induction objvl;intros.
  simpl in *.
  false.
  auto with zarith.
  simpl in H.
  mytac.
  destruct (∘ i ) eqn: eq1.
  simpl.
  exists a. auto.
  lets Hi: nat_of_Z_eq_succ eq1.
  simpl.
  rewrite Hi.
  eapply IHobjvl in H5.
  instantiate (1:= (i - 1)) in H5.
  auto.
  lets eq2: nat_of_Z_eq eq1 H0.
  unfold nat_of_Z in eq1.
  subst i.
  simpl length in H1.
  split.
  auto with zarith.
  auto with zarith.
Qed.

Lemma obj_corr_alt: 
  forall i objvl absobjs hld, 
    ObjArray_P (Vint32 Int.zero) objvl absobjs hld -> 
    (i < (length objvl))%nat ->
    length objvl = ∘ (MAX_OBJ_NUM) ->
    exists vl oid_opt att, 
      nth_vallist i objvl = Some vl /\
        get absobjs ($ (Z.of_nat i)) = Some (oid_opt, att) /\
        V_ObjAttr vl = Some (Vint32 att) /\ 
        (
          (exists oid, oid_opt = objid oid /\ 
                         V_ObjPtr vl = Some (Vptr oid) /\ oid <> hld) \/
            (oid_opt = objholder /\ V_ObjPtr vl = Some (Vptr hld)) \/
            (oid_opt = objnull /\ V_ObjPtr vl = Some Vnull) 
        ). 
Proof.
introv He Hi Hl.
destruct objvl.
simpl in *. false.
auto with zarith.
assert (v :: objvl <> nil ) by eauto.
lets Hsp: list_vallist_split_idx Hi H.
destruct Hsp. do 3 destruct H0.
rewrite H0 in *.
eapply obj_corr in He.
instantiate (1:= ($ Z.of_nat i)) in He.
destruct He. destruct H2.
do 3 eexists. 
splits; pauto. 
subst i.
rewrite nth_vallist_get_idx. auto.
subst i.
unfold MAX_OBJ_NUM in Hl.
rewrite Hl in Hi.
int auto. clear -Hi. int auto.
assert (Z.of_nat (length x) < 20).
{
  asserts_rewrite (20 = Z.of_nat ∘ 20). auto with zarith. int auto.
}
int auto.
rewrite int_ltu_zero_eq_false; auto.
unfold MAX_OBJ_NUM in Hl.
rewrite Hl in Hi.
clear -Hi. int auto. mauto. mauto.
Qed.

Lemma obj_corr_alt': 
  forall i objvl absobjs hld, 
    ObjArray_P (Vint32 Int.zero) objvl absobjs hld ->  
    (Int.unsigned i) < Z.of_nat (length objvl) ->
    length objvl = ∘ (MAX_OBJ_NUM) ->
    exists vl oid_opt att, 
      nth_vallist ∘ (Int.unsigned i) objvl = Some vl /\
        get absobjs i = Some (oid_opt, att) /\
        V_ObjAttr vl = Some (Vint32 att) /\
        (
          (exists oid, oid_opt = objid oid /\  
                         V_ObjPtr vl = Some (Vptr oid) /\ oid <> hld) \/
            (oid_opt = objholder /\ V_ObjPtr vl = Some (Vptr hld)) \/
            (oid_opt = objnull /\ V_ObjPtr vl = Some Vnull)
        ). 
Proof.
  introv He Hi Hl.
  eapply obj_corr_alt in He.
  instantiate (1:= ∘ (Int.unsigned i)) in He.
  assert (($ Z.of_nat ∘ (Int.unsigned i)) = i).
  change ∘ (MAX_OBJ_NUM) with 20%nat in Hl.
  rewrite Hl in Hi.
  unfold nat_of_Z.
  mauto.
  rewrite H in He.
  auto.
  unfold  nat_of_Z.
  unfold MAX_OBJ_NUM in Hl.
  rewrite Hl in *.
  clear -Hi. mauto.
  auto.
Qed.

Lemma obj_get_not_null: 
  forall objvl absobjs hld, 
    ObjArray_P (Vint32 Int.zero) objvl absobjs hld ->
    ObjArr_full_P objvl ->
    length objvl = ∘ (MAX_OBJ_NUM) ->
    ~(exists i tp,
          get absobjs i = Some (objnull, tp) /\ 0 <= (Int.unsigned i) < Z.of_nat (length objvl)).
Proof.
  introv He Hf Hl.
  funfold Hf.
  introv H. 
  do 2 destruct H.
  eapply obj_corr_alt' in He; eauto.
  instantiate (1:= x) in He.
  destruct He. destruct H0. destruct H0.
  destruct H. destructs H0.
  unfold get in H, H2.
  unfold ObjMap in H, H2.
  rewrite H2 in H. inverts H. 
  destruct H4.
  destruct H. destruct H. tryfalse. 
  destruct H. destruct H. tryfalse.
  destruct H.
  eapply Hf; eauto.
  destruct H. destruct H0. 
  auto.
Qed.

Lemma struct_type_vallist_match_get_sem_type:
  forall x15 x14,
    struct_type_vallist_match service_obj_t (x15 :: x14 :: nil) -> 
    exists att, x15 = Vint32 att.
Proof.
simpl.
intros.
destruct H as (H & _).
destruct x15; tryfalse.
eauto.
Qed.

Lemma RH_OBJ_ECB_P_set_to_hold:
  forall els objs idx att,
    RH_OBJ_ECB_P els objs -> 
    RH_OBJ_ECB_P els (set objs idx (objholder, att)). 
Proof.
  unfold RH_OBJ_ECB_P. 
  intros.
  rewrite ObjMod.set_sem in H0.
  destruct (idxspec.beq idx idx0) eqn: eq1; tryfalse.
  eapply H in H0; eauto.
Qed.

(* RHL_OBJ_P change ****************************************************************)

Lemma RHL_OBJ_P_set_to_hold: 
  forall vl vhold v t,
    V_ObjPtr vl = Some v ->
    V_ObjAttr vl = Some (Vint32 t) -> 
    RHL_OBJ_P (update_nth_val 1 vl (Vptr vhold)) (objholder, t) vhold. 
Proof.
  unfold RHL_OBJ_P.
  intros.
  inverts H1.
  unfold V_ObjAttr in *. 
  splits; auto.
  eapply nth_upd_neqrev; auto.

  right. left.
  unfold V_ObjPtr in *.
  splits; auto.
  eapply update_nth. eauto.
Qed.

Lemma RHL_OBJ_P_set_to_null: 
  forall vl vhold v t,
    V_ObjPtr vl = Some v ->
    V_ObjAttr vl = Some (Vint32 t) -> 
    RHL_OBJ_P (update_nth_val 1 vl Vnull) (objnull, t) vhold.  
Proof.
  unfold RHL_OBJ_P. 
  intros.
  inverts H1.
  splits.
  eapply nth_upd_neqrev; auto.
  right. right.
  unfold V_ObjPtr in *.
  splits; auto.
  eapply update_nth. eauto.
Qed.

Lemma RHL_OBJ_P_set_to_tid: 
  forall vl vhold v pid t,
    V_ObjPtr vl = Some v ->
    V_ObjAttr vl = Some (Vint32 t) -> 
    pid <> vhold ->
    RHL_OBJ_P (update_nth_val 1 vl (Vptr pid)) (objid pid,t) vhold.
Proof.
  unfold RHL_OBJ_P.
  intros.
  inverts H2.
  splits.
  eapply nth_upd_neqrev; auto.

  left.
  unfold V_ObjAttr in *.
  unfold V_ObjPtr in *.
  eexists.
  splits; auto.
  eapply update_nth. eauto.
Qed.

Lemma RHL_OBJ_P_set_type:
  forall vl vhold att att' eop,
    RHL_OBJ_P vl (eop, att) vhold ->
    RHL_OBJ_P (update_nth_val 0 vl (Vint32 att')) (eop, att') vhold.
Proof.
  unfold RHL_OBJ_P.
  intros.
  inverts H0.
  unfold V_ObjAttr in *; unfold V_ObjPtr in *.
  specialize (H _ _ (eq_refl _)).
  destructs H.
  splits; (try (eapply nth_upd_neqrev; auto; fail)).
  eapply update_nth. eauto.

  destruct H0 as [H' | [H' | H']]; mytac.
  left.  eexists. splits; eauto. eapply nth_upd_neqrev; eauto. 
  right. left. split; auto. 
  eapply nth_upd_neqrev; eauto.
  right. right.
  split; auto.  
  eapply nth_upd_neqrev; eauto.
Qed.

Lemma RHL_OBJ_P_update_hold:  
  forall vl vhold x v n,
    n <> 1%nat ->
    n <> 0%nat ->
    RHL_OBJ_P vl x vhold ->
    RHL_OBJ_P (update_nth_val n vl v) x vhold. 
Proof.
  unfold RHL_OBJ_P.
  introv Hn1 Hn2.
  intros.
  subst x.
  specialize (H _ _ (eq_refl _)).
  destructs H. 
  unfold V_ObjAttr in *.
  unfold V_ObjPtr in *. 
  splits; (try (eapply nth_upd_neqrev; auto; fail)).

  destruct H0 as [H' | [H' | H']]; mytac;
    [left | right; left | do 2 right].

  eexists.
  splits; eauto.
  eapply nth_upd_neqrev; eauto.
  splits; eauto.
  eapply nth_upd_neqrev; eauto.
  splits; eauto.
  eapply nth_upd_neqrev; eauto.
Qed.

(* ObjArray_P change ********************************************************************)

Lemma ObjArray_P_hold_for_update_to_hold:
  forall vll1 vl vll2 absobjs vhold idx j t, 
    idx = Int.repr (Z.of_nat (length vll1)) ->
    Z.of_nat (length vll1) <= Int.max_unsigned ->
    Int.unsigned j + Int.unsigned idx <= Int.max_unsigned ->
    V_ObjAttr vl = Some (Vint32 t) ->  
    ObjArray_P (Vint32 j) (vll1 ++ vl :: vll2) absobjs vhold ->
    ObjArray_P (Vint32 j) 
      (vll1 ++ (update_nth_val 1 vl (Vptr vhold)) :: vll2)
      (set absobjs (Int.add idx j) (objholder, t)) vhold. 
Proof.
  induction vll1; intros.
  simpl in *.
  mytac.
  inverts H3.
  do 4 eexists.
  destruct x1 as [eop' tp'].
  lets Hcp: H6.
  eapply RHL_OBJ_P_get_ptr in Hcp. 
  destruct Hcp.
  splits; eauto.
  change ($ 0) with Int.zero.
  instantiate (1:= (objholder, t)).
  2: { eapply RHL_OBJ_P_set_to_hold; eauto.  }
  rewrite Int.add_zero_l.
  eapply ObjMod_get_join_sig_set; eauto.
  eapply ObjMod_join_get_none_r; [idtac | eauto].
  eapply ObjMod.map_get_sig.
  (* case 2 *)
  assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
  eapply int_usign_eq; simpl length in *; auto with zarith.
  assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
  eapply int_usign_eq; simpl length in *; auto with zarith.
  simpl in H3. simpl.
  mytac.
  inverts H3.
  do 4 eexists.
  splits; eauto.
  instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x) (objholder, t)).
  eapply ObjMod.join_comm.
  eapply ObjMod.map_join_set_none.
  eapply ObjMod.join_comm. auto.
  eapply ObjMod.get_sig_none.
  rewrite Int.add_commut.
  eapply pos_add_i_neq. rewrite Heq1.
  simpl length in *; auto with zarith.
  rewrite int_ltu_zero_eq_false; auto.
  auto.
  assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x) 
              = ($ Z.of_nat (length vll1) +ᵢ  (x +ᵢ  Int.one))).
  rewrite Int.add_permut.
  rewrite Int.add_commut.
  int auto; simpl length in *; auto with zarith.
  int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
  rewrite Heq.
  eapply IHvll1; eauto.
  simpl length in *; auto with zarith.
  rewrite Heq1 in H1.
  simpl length in H1.
  assert (Int.unsigned x + Z.of_nat (S (length vll1)) = (Int.unsigned x + 1) + Z.of_nat (length vll1)).
  auto with zarith.
  rewrite H in H1.
  assert (0 <= Int.unsigned x + 1).
  pose proof (Int.unsigned_range_2 x).
  auto with zarith.
  lets Hcp: H1.
  eapply Z_add_le_trans in Hcp; auto with zarith.
  assert (Int.unsigned (x +ᵢ  Int.one) = Int.unsigned x + 1).
  int auto;simpl length in *; auto with zarith.
  rewrite H4. rewrite Heq2. auto.
Qed.

Lemma ObjArray_P_hold_for_update_to_null:
  forall vll1 vl vll2 objs vhold idx j t,
    idx = Int.repr (Z.of_nat (length vll1)) ->
    Z.of_nat (length vll1) <= Int.max_unsigned ->
    Int.unsigned j + Int.unsigned idx <= Int.max_unsigned ->
    V_ObjAttr vl = Some (Vint32 t) -> 
    ObjArray_P (Vint32 j) (vll1 ++ vl :: vll2) objs vhold ->
    ObjArray_P (Vint32 j) 
      (vll1 ++ (update_nth_val 1 vl Vnull) :: vll2)
      (set objs (Int.add idx j) (objnull,t)) vhold. 
Proof.
  induction vll1; intros.
  simpl in *.
  mytac.
  inverts H3.
  do 4 eexists.
  destruct x1 as [eop' tp'].
  lets Hcp: H6.
  eapply RHL_OBJ_P_get_ptr in Hcp.
  destruct Hcp.
  splits; eauto.
  change ($ 0) with Int.zero.
  instantiate (1:= (objnull,t)).
  2: { eapply RHL_OBJ_P_set_to_null; eauto. }
  rewrite Int.add_zero_l.
  eapply ObjMod_get_join_sig_set; eauto.
  eapply ObjMod_join_get_none_r; [idtac | eauto].
  eapply ObjMod.map_get_sig.
  (* case 2 *)
  assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
  eapply int_usign_eq; simpl length in *; auto with zarith.
  assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
  eapply int_usign_eq; simpl length in *; auto with zarith.
  simpl in H3. simpl.
  mytac.
  inverts H3.
  do 4 eexists.
  splits; eauto.
  instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x) (objnull, t)). 
  eapply ObjMod.join_comm.
  eapply ObjMod.map_join_set_none.
  eapply ObjMod.join_comm. auto.
  eapply ObjMod.get_sig_none.
  rewrite Int.add_commut.
  eapply pos_add_i_neq. rewrite Heq1.
  simpl length in *; auto with zarith.
  rewrite int_ltu_zero_eq_false; auto.
  auto.
  assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x) 
              = ($ Z.of_nat (length vll1) +ᵢ  (x +ᵢ  Int.one))).
  rewrite Int.add_permut.
  rewrite Int.add_commut.
  int auto; simpl length in *; auto with zarith.
  int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
  rewrite Heq.
  eapply IHvll1; eauto.
  simpl length in *; auto with zarith.
  rewrite Heq1 in H1.
  simpl length in H1.
  assert (Int.unsigned x + Z.of_nat (S (length vll1)) = (Int.unsigned x + 1) + Z.of_nat (length vll1)).
  auto with zarith.
  rewrite H in H1.
  assert (0 <= Int.unsigned x + 1).
  pose proof (Int.unsigned_range_2 x).
  auto with zarith.
  lets Hcp: H1.
  eapply Z_add_le_trans in Hcp; auto with zarith.
  assert (Int.unsigned (x +ᵢ  Int.one) = Int.unsigned x + 1).
  int auto;simpl length in *; auto with zarith.
  rewrite H4. rewrite Heq2. auto.
Qed.

Lemma ObjArray_P_hold_for_update_to_hold':
  forall vll1 vl vll2 objs vhold idx t,
    length vll1 = Z.to_nat idx ->
    0 <= idx <= Int.max_unsigned ->
    (* isptr eflag -> *)
    V_ObjAttr vl = Some (Vint32 t) ->  
    ObjArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) objs vhold ->
    ObjArray_P (Vint32 Int.zero) 
      (vll1 ++ (update_nth_val 1 vl (Vptr vhold)) :: vll2)
      (set objs (Int.repr idx) (objholder, t)) vhold. 
Proof.
  intros.
  lets Hr: Int.unsigned_repr H0.
  destruct H0.
  eapply ObjArray_P_hold_for_update_to_hold in H2.
  rewrite Int.add_zero in H2.
  eauto.
  eapply Z2Nat.id in H0.
  rewrite <- H0.  rewrite H. auto.
  eapply Z2Nat.id in H0.
  rewrite H.  rewrite H0. auto.
  rewrite Int.unsigned_zero. 
  auto with zarith.
  auto.
Qed.

Lemma ObjArray_P_hold_for_update_to_null': 
  forall vll1 vl vll2 objs vhold idx t,
    length vll1 = Z.to_nat idx ->
    0 <= idx <= Int.max_unsigned ->
    V_ObjAttr vl = Some (Vint32 t) -> 
    ObjArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) objs vhold ->
    ObjArray_P (Vint32 Int.zero) 
      (vll1 ++ (update_nth_val 1 vl Vnull) :: vll2)
      (set objs (Int.repr idx) (objnull, t)) vhold.
Proof.
  intros.
  lets Hr: Int.unsigned_repr H0.
  destruct H0.
  eapply ObjArray_P_hold_for_update_to_null in H1.
  rewrite Int.add_zero in H1.
  eauto.
  eapply Z2Nat.id in H0.
  rewrite <- H0.  rewrite H. auto.
  eapply Z2Nat.id in H0.
  rewrite H.  rewrite H0. auto.
  rewrite Int.unsigned_zero. 
  auto with zarith.
  auto.
Qed.

Lemma ObjArray_P_hold_for_update_to_tid:
  forall vll1 vl vll2 objs vhold idx j pid t,
    idx = Int.repr (Z.of_nat (length vll1)) ->
    Z.of_nat (length vll1) <= Int.max_unsigned ->
    Int.unsigned j + Int.unsigned idx <= Int.max_unsigned ->
    (* eflag = Vnull \/ eflag = Vptr pid -> *)
    V_ObjAttr vl = Some (Vint32 t) -> 
    pid <> vhold ->
    ObjArray_P (Vint32 j) (vll1 ++ vl :: vll2) objs vhold ->
    ObjArray_P (Vint32 j) 
      (vll1 ++ (update_nth_val 1 vl (Vptr pid)) :: vll2)
      (set objs (Int.add idx j) (objid pid,t)) vhold.
Proof.
  induction vll1; intros.
  simpl in *.
  mytac.
  inverts H4.
  do 4 eexists.
  destruct x1 as [eop' tp'].
  lets Hcp: H7.
  eapply RHL_OBJ_P_get_ptr in Hcp.
  destruct Hcp.
  splits; eauto.
  change ($ 0) with Int.zero.
  instantiate (1:= (objid pid, t)). 
  2: { eapply RHL_OBJ_P_set_to_tid; eauto. }
  rewrite Int.add_zero_l.
  eapply ObjMod_get_join_sig_set; eauto.
  eapply ObjMod_join_get_none_r; [idtac | eauto].
  eapply ObjMod.map_get_sig.
  (* case 2 *)
  assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
  eapply int_usign_eq; simpl length in *; auto with zarith.
  assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
  eapply int_usign_eq; simpl length in *; auto with zarith.
  simpl in H4. simpl.
  mytac.
  inverts H4.
  do 4 eexists.
  splits; eauto.
  instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x) (objid pid, t)).
  eapply ObjMod.join_comm.
  eapply ObjMod.map_join_set_none.
  eapply ObjMod.join_comm. auto.
  eapply ObjMod.get_sig_none.
  rewrite Int.add_commut.
  eapply pos_add_i_neq. rewrite Heq1.
  simpl length in *; auto with zarith.
  rewrite int_ltu_zero_eq_false; auto.
  auto.
  assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x) 
              = ($ Z.of_nat (length vll1) +ᵢ  (x +ᵢ  Int.one))).
  rewrite Int.add_permut.
  rewrite Int.add_commut.
  int auto; simpl length in *; auto with zarith.
  int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
  rewrite Heq.
  eapply IHvll1; eauto.
  simpl length in *; auto with zarith.
  rewrite Heq1 in H1.
  simpl length in H1.
  assert (Int.unsigned x + Z.of_nat (S (length vll1)) = (Int.unsigned x + 1) + Z.of_nat (length vll1)).
  auto with zarith.
  rewrite H in H1.
  assert (0 <= Int.unsigned x + 1).
  pose proof (Int.unsigned_range_2 x).
  auto with zarith.
  lets Hcp: H1.
  eapply Z_add_le_trans in Hcp; auto with zarith.
  assert (Int.unsigned (x +ᵢ  Int.one) = Int.unsigned x + 1).
  int auto;simpl length in *; auto with zarith.
  rewrite H5. rewrite Heq2. auto.
Qed.

Lemma ObjArray_P_hold_for_update_to_tid':
forall vll1 vl vll2 objs vhold idx pid t,
idx = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned idx <= Int.max_unsigned ->
V_ObjAttr vl = Some (Vint32 t) ->
pid <> vhold ->
ObjArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) objs vhold ->
ObjArray_P (Vint32 Int.zero) 
                        (vll1 ++ (update_nth_val 1 vl (Vptr pid)) :: vll2)
                        (set objs idx (objid pid, t)) vhold.
Proof.
  intros.
  lets Hnew: ObjArray_P_hold_for_update_to_tid H H0.
  instantiate (4:= Int.zero) in Hnew.
  change (Int.unsigned Int.zero) with 0 in Hnew.
  rewrite Int.add_commut in Hnew.
  rewrite Int.add_zero_l in Hnew.
  rewrite Z.add_0_l in Hnew.
  eapply Hnew;eauto.
Qed.

Lemma ObjArray_P_hold_for_update_att:
  forall vll1 vl vll2 objs vhold att idx j att' eop,
    idx = Int.repr (Z.of_nat (length vll1)) ->
    Z.of_nat (length vll1) <= Int.max_unsigned ->
    Int.unsigned j + Int.unsigned idx <= Int.max_unsigned ->
    ObjMod.get objs (Int.add idx j) = Some (eop, att) ->
    V_ObjAttr vl = Some (Vint32 att) ->
    ObjArray_P (Vint32 j) (vll1 ++ vl :: vll2) objs vhold ->
    ObjArray_P (Vint32 j) 
      (vll1 ++ (update_nth_val 0 vl (Vint32 att')) :: vll2)
      (set objs (Int.add idx j) (eop, att')) vhold.
Proof.
  induction vll1; intros.
  simpl in *.
  mytac.
  inverts H4.
  do 4 eexists.
  destruct x1 as [eop0 att0].
  lets Hget: ObjMod.join_sig_get H6.
  change ($ 0) with Int.zero in *.
  rewrite Int.add_zero_l in H2.
  rewrite H2 in Hget.
  inverts Hget.
  lets Hcp: H7.
  eapply RHL_OBJ_P_get_ptr in Hcp.
  destruct Hcp.
  splits; eauto.
  instantiate (1:= (eop, att')).
  2: { eapply RHL_OBJ_P_set_type; eauto. }
  rewrite Int.add_zero_l.
  eapply ObjMod_get_join_sig_set; eauto.
  eapply ObjMod_join_get_none_r; [idtac | eauto].
  eapply ObjMod.map_get_sig.
  (* case 2 *)
  assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
  eapply int_usign_eq; simpl length in *; auto with zarith.
  assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
  eapply int_usign_eq; simpl length in *; auto with zarith.
  simpl in H4. simpl.
  mytac.
  inverts H4.
  do 4 eexists.
  splits; eauto.
  instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x) (eop, att')).
  eapply ObjMod.join_comm.
  eapply ObjMod.map_join_set_none.
  eapply ObjMod.join_comm. auto.
  eapply ObjMod.get_sig_none.
  rewrite Int.add_commut.
  eapply pos_add_i_neq. rewrite Heq1.
  simpl length in *; auto with zarith.
  rewrite int_ltu_zero_eq_false; auto.
  auto.
  assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x) 
              = ($ Z.of_nat (length vll1) +ᵢ  (x +ᵢ  Int.one))).
  rewrite Int.add_permut.
  rewrite Int.add_commut.
  int auto; simpl length in *; auto with zarith.
  int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
  rewrite Heq.
  eapply IHvll1; eauto.
  simpl length in *; auto with zarith.
  rewrite Heq1 in H1.
  simpl length in H1.
  assert (Int.unsigned x + Z.of_nat (S (length vll1)) = (Int.unsigned x + 1) + Z.of_nat (length vll1)).
  auto with zarith.
  rewrite H in H1.
  assert (0 <= Int.unsigned x + 1).
  pose proof (Int.unsigned_range_2 x).
  auto with zarith.
  lets Hcp: H1.
  eapply Z_add_le_trans in Hcp; auto with zarith.
  assert (Int.unsigned (x +ᵢ  Int.one) = Int.unsigned x + 1).
  int auto;simpl length in *; auto with zarith.
  rewrite H5. rewrite Heq2. auto.
  eapply ObjMod.map_join_get_none in H6.
  erewrite H2 in H6.
  rewrite H6.
  rewrite Heq. auto. 
  eapply ObjMod.get_sig_none.
  rewrite Int.add_commut.
  eapply pos_add_i_neq. rewrite Heq1.
  simpl length in *; auto with zarith.
  rewrite int_ltu_zero_eq_false; auto.
  auto.
Qed.

Lemma ObjArray_P_hold_for_update_att':
  forall vll1 vl vll2 objs vhold att idx att' eop, 
    idx = Int.repr (Z.of_nat (length vll1)) ->
    Z.of_nat (length vll1) <= Int.max_unsigned ->
    Int.unsigned idx <= Int.max_unsigned -> 
    ObjMod.get objs idx = Some (eop,att) ->
    V_ObjAttr vl = Some (Vint32 att) ->
    ObjArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) objs vhold ->
    ObjArray_P (Vint32 Int.zero) 
      (vll1 ++ (update_nth_val 0 vl (Vint32 att')) :: vll2)
      (set objs idx (eop, att')) vhold.
Proof.
  intros.
  lets Hnew: ObjArray_P_hold_for_update_att H H0.
  instantiate (4:= Int.zero) in Hnew.
  change (Int.unsigned Int.zero) with 0 in Hnew.
  rewrite Int.add_commut in Hnew.
  rewrite Int.add_zero_l in Hnew.
  rewrite Z.add_0_l in Hnew.
  eapply Hnew;eauto.
Qed.

Lemma ObjArray_P_hold_for_update_same: 
  forall vll1 vl vll2 objs vhold idx j v n,
    idx = Int.repr (Z.of_nat (length vll1)) ->
    Z.of_nat (length vll1) <= Int.max_unsigned ->
    Int.unsigned j + Int.unsigned idx <= Int.max_unsigned ->
    n <> 1%nat ->
    n <> 0%nat ->
    ObjArray_P (Vint32 j) (vll1 ++ vl :: vll2) objs vhold ->
    ObjArray_P (Vint32 j) (vll1 ++ (update_nth_val n vl v) :: vll2) objs vhold.
Proof.
  induction vll1; intros.
  simpl in *.
  mytac.
  inverts H4.
  do 4 eexists.
  splits;eauto.
  eapply RHL_OBJ_P_update_hold; eauto.
  (* case 2 *)
  assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
  eapply int_usign_eq; simpl length in *; auto with zarith.
  assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
  eapply int_usign_eq; simpl length in *; auto with zarith.
  simpl in H4. simpl.
  mytac.
  inverts H4.
  do 4 eexists.
  splits; eauto.
  eapply IHvll1; eauto.
  simpl length in *; auto with zarith.
  rewrite Heq1 in H1.
  simpl length in H1.
  assert (Int.unsigned x + Z.of_nat (S (length vll1)) = (Int.unsigned x + 1) + Z.of_nat (length vll1)).
  auto with zarith.
  rewrite H in H1.
  assert (0 <= Int.unsigned x + 1).
  pose proof (Int.unsigned_range_2 x).
  auto with zarith.
  lets Hcp: H1.
  eapply Z_add_le_trans in Hcp; auto with zarith.
  assert (Int.unsigned (x +ᵢ  Int.one) = Int.unsigned x + 1).
  int auto;simpl length in *; auto with zarith.
  rewrite H5. rewrite Heq2. auto.
Qed.

Lemma ObjArray_P_hold_for_update_same':
  forall vll1 vl vll2 objs vhold idx v n,
    idx = Int.repr (Z.of_nat (length vll1)) ->
    Z.of_nat (length vll1) <= Int.max_unsigned ->
    Int.unsigned idx <= Int.max_unsigned ->
    n <> 1%nat ->
    n <> 0%nat ->
    ObjArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) objs vhold ->
    ObjArray_P (Vint32 Int.zero) (vll1 ++ (update_nth_val n vl v) :: vll2) objs vhold.
Proof.
  intros.
  eapply ObjArray_P_hold_for_update_same; eauto.
Qed.

Lemma ObjArray_P_hold_for_update_to_tid_att:
  forall vll1 vl vll2 objs vhold idx j pid t att',
    idx = Int.repr (Z.of_nat (length vll1)) ->
    Z.of_nat (length vll1) <= Int.max_unsigned ->
    Int.unsigned j + Int.unsigned idx <= Int.max_unsigned ->
    V_ObjAttr vl = Some (Vint32 t) -> 
    pid <> vhold ->
    ObjArray_P (Vint32 j) (vll1 ++ vl :: vll2) objs vhold ->
    ObjArray_P (Vint32 j) 
      (vll1 ++ (update_nth_val 0 (update_nth_val 1 vl (Vptr pid)) (Vint32 att')) :: vll2)
      (set objs (Int.add idx j) (objid pid,att')) vhold.
Proof.
  induction vll1; intros.
  simpl in *.
  mytac.
  inverts H4.
  do 4 eexists.
  destruct x1 as [eop' tp'].
  lets Hcp: H7.
  eapply RHL_OBJ_P_get_ptr in Hcp.
  destruct Hcp.
  splits; eauto.
  change ($ 0) with Int.zero.
  instantiate (1:= (objid pid, att')). 
  2: { eapply RHL_OBJ_P_set_type.
         eapply RHL_OBJ_P_set_to_tid; eauto. }
  rewrite Int.add_zero_l.
  eapply ObjMod_get_join_sig_set; eauto.
  eapply ObjMod_join_get_none_r; [idtac | eauto].
  eapply ObjMod.map_get_sig.
  (* case 2 *)
  assert (Heq1: Int.unsigned ($ Z.of_nat (length (a :: vll1))) = Z.of_nat (length (a :: vll1))).
  eapply int_usign_eq; simpl length in *; auto with zarith.
  assert (Heq2: Int.unsigned ($ Z.of_nat (length vll1)) = Z.of_nat (length vll1)).
  eapply int_usign_eq; simpl length in *; auto with zarith.
  simpl in H4. simpl.
  mytac.
  inverts H4.
  do 4 eexists.
  splits; eauto.
  instantiate (1:= set x0 ($ Z.of_nat (length (a :: vll1)) +ᵢ  x) (objid pid, att')).
  eapply ObjMod.join_comm.
  eapply ObjMod.map_join_set_none.
  eapply ObjMod.join_comm. auto.
  eapply ObjMod.get_sig_none.
  rewrite Int.add_commut.
  eapply pos_add_i_neq. rewrite Heq1.
  simpl length in *; auto with zarith.
  rewrite int_ltu_zero_eq_false; auto.
  auto.
  assert (Heq:($ Z.of_nat (length (a :: vll1)) +ᵢ  x) 
              = ($ Z.of_nat (length vll1) +ᵢ  (x +ᵢ  Int.one))).
  rewrite Int.add_permut.
  rewrite Int.add_commut.
  int auto; simpl length in *; auto with zarith.
  int auto. change Int.max_unsigned with 4294967295 in *. auto with zarith.
  rewrite Heq.
  eapply IHvll1; eauto.
  simpl length in *; auto with zarith.
  rewrite Heq1 in H1.
  simpl length in H1.
  assert (Int.unsigned x + Z.of_nat (S (length vll1)) = (Int.unsigned x + 1) + Z.of_nat (length vll1)).
  auto with zarith.
  rewrite H in H1.
  assert (0 <= Int.unsigned x + 1).
  pose proof (Int.unsigned_range_2 x).
  auto with zarith.
  lets Hcp: H1.
  eapply Z_add_le_trans in Hcp; auto with zarith.
  assert (Int.unsigned (x +ᵢ  Int.one) = Int.unsigned x + 1).
  int auto;simpl length in *; auto with zarith.
  rewrite H5. rewrite Heq2. auto.
Qed.

Lemma ObjArray_P_hold_for_update_to_tid_att':
forall vll1 vl vll2 objs vhold idx pid t att',
idx = Int.repr (Z.of_nat (length vll1)) ->
Z.of_nat (length vll1) <= Int.max_unsigned ->
Int.unsigned idx <= Int.max_unsigned ->
V_ObjAttr vl = Some (Vint32 t) ->
pid <> vhold ->
ObjArray_P (Vint32 Int.zero) (vll1 ++ vl :: vll2) objs vhold ->
ObjArray_P (Vint32 Int.zero) 
                        (vll1 ++ (update_nth_val 0 (update_nth_val 1 vl (Vptr pid)) (Vint32 att')) :: vll2)
                        (set objs idx (objid pid, att')) vhold.
Proof.
  intros.
  lets Hnew: ObjArray_P_hold_for_update_to_tid_att H H0.
  instantiate (4:= Int.zero) in Hnew.
  change (Int.unsigned Int.zero) with 0 in Hnew.
  rewrite Int.add_commut in Hnew.
  rewrite Int.add_zero_l in Hnew.
  rewrite Z.add_0_l in Hnew.
  eapply Hnew;eauto.
Qed.

Lemma RH_OBJ_ECB_P_set_minus_one : 
  forall els sid n wls embls,
    EcbMod.get els sid = Some (abssem n, wls) ->
    RH_OBJ_ECB_P els embls ->
    RH_OBJ_ECB_P (set els sid (abssem (n -ᵢ Int.one), wls)) embls. 
Proof.
  unfold RH_OBJ_ECB_P.
  intros.
  assert (Hi: oid = sid \/ oid <> sid) by tauto.
  destruct Hi.
  subst.
  exists (n -ᵢ Int.one) wls.
  eapply EcbMod.set_a_get_a.
  eapply tidspec.eq_beq_true.
  auto.
  assert (Hg: get (set els sid (abssem (n -ᵢ Int.one), wls)) oid = get els oid).
  eapply EcbMod.set_a_get_a'.
  eapply tidspec.neq_beq_false.
  eauto.
  rewrite Hg.
  eauto.
Qed.

Lemma RH_OBJ_ECB_P_set_wls':  
  forall els sid n wls objs wls',
    EcbMod.get els sid = Some (abssem n, wls) ->
    RH_OBJ_ECB_P els objs ->
    RH_OBJ_ECB_P (set els sid (abssem n, wls')) objs.
Proof.
  unfold RH_OBJ_ECB_P.
  intros.
  assert (Hi: oid = sid \/ oid <> sid) by tauto.
  destruct Hi.
  subst.
  repeat eexists.
  eapply EcbMod.set_a_get_a.
  eapply tidspec.eq_beq_true.
  auto.
  assert (Hg: get (set els sid (abssem n, wls')) oid = get els oid).
  eapply EcbMod.set_a_get_a'.
  eapply tidspec.neq_beq_false.
  eauto.
  rewrite Hg.
  eauto.
Qed.

Lemma AObjs_sem_set_wls'_preserve: 
  forall els sid n wls objs wls' objl vhold s P,
    EcbMod.get els sid = Some (abssem n, wls) ->
    s |= AObjs objl objs els vhold ** P -> 
    s |= AObjs objl objs (set els sid (abssem n, wls')) vhold ** P.  
Proof. 
  introv Hsat Hget.
  unfold AObjs in *.
  sep pauto.
  eapply RH_OBJ_ECB_P_set_wls'; eauto. 
Qed. 

Lemma RH_OBJ_ECB_P_sem_inc : 
  forall els sid n wls objs,
    EcbMod.get els sid = Some (abssem n, wls) ->
    RH_OBJ_ECB_P els objs ->
    RH_OBJ_ECB_P (set els sid (abssem (n +ᵢ Int.one), wls)) objs.
Proof.
  unfold RH_OBJ_ECB_P.
  intros.
  assert (Hi: oid = sid \/ oid <> sid) by tauto.
  destruct Hi.
  subst.
  exists (n +ᵢ Int.one) wls.
  eapply EcbMod.set_a_get_a.
  eapply tidspec.eq_beq_true.
  auto.
  assert (Hg: get (set els sid (abssem (n +ᵢ Int.one), wls)) oid = get els oid).
  eapply EcbMod.set_a_get_a'.
  eapply tidspec.neq_beq_false.
  eauto.
  rewrite Hg.
  eauto.
Qed.

Lemma RH_OBJ_ECB_P_set_type_preserve: 
  forall ecbls objs idx e att att', 
    RH_OBJ_ECB_P ecbls objs ->
    get objs idx = Some (e, att) -> 
    RH_OBJ_ECB_P ecbls (set objs idx (e, att')). 
Proof.
  introv Hrh Hget.
  unfold RH_OBJ_ECB_P in *.
  introv Hget'.
  casetac idx idx0 Heq Hneq.
  subst.
  rewrite set_a_get_a in Hget'.
  inverts Hget'.
  eapply Hrh; eauto.
  rewrite set_a_get_a' in Hget'; eauto.
Qed.

Lemma RH_OBJ_ECB_P_null_preserve: 
  forall ecbls semeibs idx att, 
    RH_OBJ_ECB_P ecbls semeibs ->
    RH_OBJ_ECB_P ecbls (set semeibs idx (objnull, att)). 
Proof.
  intros.
  unfold RH_OBJ_ECB_P in *. 
  introv Hget.
  casetac idx idx0 Ht Hf.
  subst.
  rewrite set_a_get_a in Hget. inverts Hget.
  rewrite set_a_get_a' in Hget; eauto. 
Qed.

Lemma RH_OBJ_ECB_P_ptr_preserve:  
  forall ecbls objs idx att eid, 
    RH_OBJ_ECB_P ecbls objs ->
    is_kobj ecbls eid ->  
    RH_OBJ_ECB_P ecbls (set objs idx (objid eid, att)). 
Proof.
  introv Hrh Hobj.
  unfold RH_OBJ_ECB_P in *.
  introv Hget.
  casetac idx idx0 Heq Hne.
  subst.
  rewrite set_a_get_a in Hget. inverts Hget.
  unfold is_kobj in Hobj. eauto.
  rewrite set_a_get_a' in Hget; eauto.
Qed.

Lemma obj_ecb_delobj_preserve:   
  forall els objs els' i1 eid idx att, 
    RH_OBJ_ECB_P els objs ->
    objref_distinct objs ->
    join els' (sig eid (abssem i1, nil)) els ->
    get objs idx = Some (objid eid, att) -> 
    RH_OBJ_ECB_P els' (set objs idx (objnull, att)).  
Proof.
  introv Hobjecb Hd Hjo Hobj.
  unfold RH_OBJ_ECB_P in *.
  introv Hget.
  casetac idx idx0 Heq Hneq.
  subst.
  rewrite set_a_get_a in Hget. inverts Hget.
  rewrite set_a_get_a' in Hget; eauto.
  lets H00: Hobjecb Hget. clear Hobjecb.
  simpljoin1.
  casetac oid eid Ht Hf.
  subst.
  unfold objref_distinct in Hd.
  specialize (Hd eid).
  assert (idx = idx0). { eapply Hd; eauto. }
  subst.
  tryfalse. 
  
  exists x x0.
  assert (join (sig eid (abssem i1, nil)) els' els).
  join auto.
  eapply perm_map_lemmas_part4.join_sig_get_r; eauto. 
Qed.

Lemma obj_ecb_delobj_preserve':
  forall els objs els'  i1 ptr wls,
  RH_OBJ_ECB_P els objs ->
  ~ obj_ref objs ptr ->
  join els' (sig ptr (abssem i1, wls)) els ->
  RH_OBJ_ECB_P els' objs.
Proof.
 unfold RH_OBJ_ECB_P.
 unfold obj_ref.
 intros.
 casetac oid ptr Ht Hf.
 subst.
 false. eapply H0; eauto.
 lets H00: H H2.
 simpljoin.
do 2 eexists.
rewrite <- H3.
apply eq_sym.
eapply EcbMod.map_join_get_none.
eapply EcbMod.join_comm; eauto.
eapply EcbMod.map_get_sig'; eauto.
Qed.



