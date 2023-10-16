
Require Import os_code_defs. 
Require Import os_ucos_h.
Require Import Integers.
Require Import math_auto.

(* Require Import sem_common. *)
Require Import pure_lib.
Require Import step_prop.

Require Import os_inv.

Require Import Aarray_new_common.

Local Open Scope Z_scope. 
Local Open Scope int_scope.
Local Open Scope code_scope.

Lemma Aarray_new_emp:
  forall e e0 i l a b i0, 
    (e, e0, empenv, i, l, empenv, a) |= Aarray_new (b, i0) (Tarray service_obj_t 0) nil. 
Proof.
  intros.
  unfold Aarray_new.
  unfold Aarray_new'.
  simpl; split; auto. 
  unfold emposabst.
  auto.
Qed.   

Lemma Aarray_new'_split_strong :
  forall vll1 n vll2 m t b i s, 
    s |= Aarray_new' (b,i) (n + m) t (vll1 ++ vll2) ->
    Z.of_nat (S n * typelen t) <= Int.max_unsigned -> 
    (* 0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned -> *)
    length vll1 = n /\ length vll2 = m ->
    s |= Aarray_new' (b, i) n t vll1 ** Aarray_new' (b, i +ᵢ $ Z.of_nat (n * (typelen t))) m t vll2.
Proof.
  induction vll1; induction n; intros.
  simpl Aarray_new' in *.
  assert (i +ᵢ  $ 0 = i) by int auto.
  rewrite H2.
  sep pauto.
  inverts H1.
  inverts H2.
  inverts H1.
  inverts H2.
  eapply Aarray_new'_succ_alt.
  change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)) in H.
  rewrite Nat.add_succ_l in H.
  eapply Aarray_new'_succ_imp in H.
  sep pauto.
  cut ($ Z.of_nat (S n * typelen t) = $ Z.of_nat (typelen t) +ᵢ $ Z.of_nat (n * typelen t)).
  {
    intro.
    rewrite H3.
    rewrite <- Int.add_assoc.
    eapply IHvll1.
    sep pauto.
    auto with zarith.
    inverts H1. auto.
  }
  int auto.
Qed.

Lemma Aarray_new_split_strong :
  forall vll1 n vll2 m t b i s, 
    s |= Aarray_new (b,i) (Tarray t (n + m)) (vll1 ++ vll2) ->
    (* 0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned -> *)
    Z.of_nat (S n * typelen t) <= Int.max_unsigned -> 
    length vll1 = n /\ length vll2 = m ->
    s |=
      Aarray_new (b, i) (Tarray t n) vll1 **
      Aarray_new (b, i +ᵢ $ Z.of_nat (n * (typelen t))) (Tarray t m) vll2.
Proof.
  unfold Aarray_new.
  apply Aarray_new'_split_strong.
Qed.

Ltac unfold_usr_max_evts := 
  unfold OS_USER_MAX_EVENTS; unfold OS_MAX_EVENTS; unfold CORENUM.

Ltac unfold_usr_max_evts_in h :=
  unfold OS_USER_MAX_EVENTS in h; unfold OS_MAX_EVENTS in h; unfold CORENUM in h.

Lemma mul_typelen_transform: 
  forall i, 
    Int.ltu i ($ 0) = false -> 
    Z.of_nat (S (Z.to_nat (Int.unsigned i))) <= MAX_OBJ_NUM ->
    Int.mul ($ Z.of_nat (typelen service_obj_t)) i =
      $ Z.of_nat (Z.to_nat (Int.unsigned i) * typelen service_obj_t). 
Proof.
  introv Hrgn1 Hrgn2.
  unfold_usr_max_evts_in Hrgn2.
  simpl in Hrgn2. 
  simpl.  
  assert (Hle: 0 <= Int.unsigned i) by int auto.
  destruct (Int.unsigned i) eqn: E.
  mauto.
  2: {
    lets H0: Pos2Z.neg_is_nonpos p.
    assert (Z.neg p = 0) by auto with zarith.
    rewrite H. mauto.
  }
  rewrite <- E. 
  unfold Int.mul. 
  rewrite Nat2Z.inj_mul.
  rewrite Z.mul_comm.
  asserts_rewrite (Int.unsigned ($ 8) = Z.of_nat 8). { mauto. }
  rewrite Z2Nat.id; auto. 
  mauto.
Qed.
  
Ltac mytac :=
  heat; jeauto2.

Lemma new_array_type_vallist_match_split2: 
  forall semvl vll1 vll2 t, 
    new_array_type_vallist_match t semvl ->
    semvl = vll1 ++ vll2 ->
    new_array_type_vallist_match t vll1 /\
    new_array_type_vallist_match t vll2.
Proof.
  inductions semvl.
  -  intros.
     symmetry in H0.
     apply app_eq_nil in H0. 
     destruct H0. subst vll1 vll2. 
     simpl. auto.
  - introv Hmt1 Hlst.
    destruct vll1.
    simpl in Hlst.
    destruct vll2; inverts Hlst.
    split; simpl; auto.
    rewrite <- app_comm_cons in Hlst.
    inverts Hlst.
    simpl in Hmt1.
    destruct t;
      (destruct Hmt1 as (Hmta & Hmtb);
       specialize (IHsemvl vll1 vll2 _ Hmtb (eq_refl _));
       split; [simpl; mytac | mytac]).
Qed.          

Lemma new_array_type_vallist_match_split: 
  forall objvl vll1 vll2 vl, 
    new_array_type_vallist_match service_obj_t objvl ->
    objvl = vll1 ++ (vl::vll2) ->
    new_array_type_vallist_match service_obj_t vll1 /\
    new_array_type_vallist_match service_obj_t vll2 /\ 
    struct_type_vallist_match service_obj_t vl.   
Proof.
  introv Hmatch Hlst.
  lets Hsp2 : new_array_type_vallist_match_split2 Hmatch Hlst.
  destruct Hsp2.
  split; auto.
  simpl in H0.
  destruct H0.
  split; auto.
Qed.   

Lemma Aarray_new'_compose_strong :
  forall vll1 n vll2 m t b i s, 
    Z.of_nat (S n * typelen t) <= Int.max_unsigned -> 
     (* 0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned -> *)
    s |= Aarray_new' (b,i) n t vll1 ** Aarray_new' (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) m t vll2 -> 
    s |= Aarray_new' (b,i) (n + m) t (vll1 ++ vll2).
Proof.
  induction vll1; induction n; intros.
  simpl Aarray_new' in H0.
  assert (i +ᵢ  $ 0 = i) by int auto.
  rewrite H1 in H0.
  sep pauto.
  eapply astar_l_afalse_elim in H0.
  tryfalse.
  eapply astar_l_afalse_elim in H0.
  tryfalse.
  eapply Aarray_new'_succ_imp_alt in H0.
  change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)).
  rewrite Nat.add_succ_l.
  eapply Aarray_new'_succ.
  sep pauto.
  eapply IHvll1 with (i:=i +ᵢ  $ Z.of_nat (typelen t)); eauto.
  auto with zarith.
  rewrite Int.add_assoc.
  assert (Heq:
           $ Z.of_nat (S n * typelen t) = ($ Z.of_nat (typelen t) +ᵢ  $ Z.of_nat (n * typelen t))).
  { int auto. }
  rewrite <- Heq.
  auto.
Qed.

Lemma Aarray_new_compose_strong:
  forall vll1 n vll2 m t b i s, 
    Z.of_nat (S n * typelen t) <= Int.max_unsigned ->     
    s |= Aarray_new (b,i) (Tarray t n) vll1 ** Aarray_new (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) (Tarray t m) vll2 -> 
    s |= Aarray_new (b,i) (Tarray t (n + m)) (vll1 ++ vll2).
Proof.
  unfold Aarray_new.
  apply Aarray_new'_compose_strong.
Qed.

Ltac simpl_sat H := unfold sat in H; fold sat in H; simpl substmo in H; simpl getmem in H; simpl getabst in H; simpl empst in H.

Ltac simpl_sat_goal := unfold sat; fold sat; unfold substmo; unfold substaskst; unfold getmem; unfold getabst; unfold get_smem; unfold get_mem.

Lemma aobjarr_len: 
  forall s vl, s |= AObjArr vl -> length vl = ∘ (MAX_OBJ_NUM).
Proof.  
  introv Hsat.
  destruct Hsat.
  simpl_sat H. simpljoin1.
  auto.
Qed. 


Lemma pos_to_nat_20: Pos.to_nat 20 = 20%nat. 
auto with arith. Qed. 

Lemma mul_arith:
  forall idx, (idx < 6)%nat -> Z.of_nat (idx * 32) < 192.
intros. auto with zarith. Qed.

Lemma sub_Z_nat:
  forall (a:nat) b, (a <= ∘ b)%nat -> (∘ (b - Z.of_nat a) = (∘ b) - a)%nat. 
  unfold nat_of_Z in *. intros. auto with zarith. Qed.

Lemma sub_eq_succ:
  forall m n l,  (S m <= l -> S n = l - m -> n = l - (S m))%nat. 
intros. auto with zarith. Qed.

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

Require Import Lia.

Lemma length_exists: 
  forall {A:Type} (l: list A), (length l > 0)%nat -> exists h t, l = h :: t.
Proof.
  intros.
  destruct l.
  simpl in H; lia.
  eauto.
Qed.

Lemma AObjArr_unfold_any_idx: 
  forall s objvl idx,
    s |= AObjArr objvl ->
    (idx < length objvl)%nat ->
    s |= EX vll1 vll2 b i vl ,
        GV obj_arr @ service_obj_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray service_obj_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen service_obj_t))) service_obj_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen service_obj_t))))
          (Tarray service_obj_t (∘ (MAX_OBJ_NUM - Z.of_nat (S idx)))) vll2 **  
          [| new_array_type_vallist_match service_obj_t objvl |] **
          [| length objvl = ∘ (MAX_OBJ_NUM) |] **
          [| objvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (MAX_OBJ_NUM - Z.of_nat (S idx)) |] ** 
          [| Z.of_nat (S idx) <= MAX_OBJ_NUM |].   
Proof. 
  introv Hsat.
  assert (Hlengt: Z.of_nat (length objvl * typelen service_obj_t) <= Int.max_unsigned). 
  { erewrite aobjarr_len; eauto.  simpl. mauto. }
  introv Hlenle. 
  unfold AObjArr in Hsat.
  simpl_sat Hsat. 
  simpljoin1.
  rewrite <- H11 in *.
  assert (Hlen: (length objvl = idx + (length objvl - idx))%nat) 
    by auto with arith.
  lets Hsplit: (firstn_skipn idx objvl). 
  rewrite <- Hsplit in H8 at 2.
  rewrite Hlen in H8. 
  destruct x.
  lets Harrs0: Aarray_new_split_strong H8.
  assert (HSidx: (S idx <= length objvl)%nat) by auto with arith.
  assert (Harith: Z.of_nat (S idx * typelen service_obj_t) <= Int.max_unsigned). 
  {
    apply Z.le_trans with (m:=Z.of_nat (length objvl * typelen service_obj_t));
      auto.
    apply inj_le. 
    apply NPeano.Nat.mul_le_mono_r; auto.
  }
  lets Harrs00: Harrs0 Harith.
  clear Harrs0.
  assert (Hlens: length (firstn idx objvl) = idx /\ length (skipn idx objvl) = (length objvl - idx)%nat).
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

  assert (HlenS: (length objvl - idx = S (length objvl - (S idx)))%nat).
  {
    rewrite NPeano.Nat.sub_succ_r.
    rewrite Nat.lt_succ_pred with (z:=0%nat); auto.
    rewrite <- Nat.lt_add_lt_sub_r. simpl. auto.
  }
  rewrite HlenS in H13.
  assert (Hln: (length (skipn idx objvl) > 0)%nat).
  {
    rewrite skipn_length.  
    cut (0 < length objvl - idx)%nat.
    auto with arith.
    rewrite <- NPeano.Nat.lt_add_lt_sub_l.
    rewrite Nat.add_0_r. auto.
  }
  apply length_exists in Hln.
  destruct Hln as (vh & vlt & Hlst). rewrite Hlst in H13.
  apply Aarray_new'_succ_imp in H13.
  assert (Hsimp: $ Z.of_nat (idx * typelen service_obj_t) +ᵢ  $ Z.of_nat (typelen service_obj_t) =
                   $ Z.of_nat (S idx * typelen service_obj_t)).
  {
    rewrite <- Nat.add_1_r.
    rewrite NPeano.Nat.mul_add_distr_r. 
    rewrite Nat2Z.inj_add.
    change (1 * typelen service_obj_t)%nat with (typelen service_obj_t).
    simpl. 
    assert (Ha: Z.of_nat (idx * 8) = Int.unsigned ($ (Z.of_nat (idx * 8)))). 
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
  assert (Hc: (∘ (MAX_OBJ_NUM - Z.of_nat (S idx)) = length objvl - S idx)%nat).
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

  exists (firstn idx objvl). exists vlt. exists b. exists i.
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
  auto.
  simpl. split; auto. unfolds. auto.

Qed. 

Lemma AObjArr_unfold_any_idx_frm: 
  forall s objvl idx P,
    s |= AObjArr objvl ** P ->
    (idx < length objvl)%nat ->
    s |= (EX vll1 vll2 b i vl ,
        GV obj_arr @ service_obj_t ∗ |-> Vptr (b,i) **
          Aarray_new (b, i) (Tarray service_obj_t idx) vll1 **
          Astruct (b, i +ᵢ $ Z.of_nat (idx * (typelen service_obj_t))) service_obj_t vl **
          Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S idx) * (typelen service_obj_t))))
            (Tarray service_obj_t (∘ (MAX_OBJ_NUM - Z.of_nat (S idx)))) vll2 ** 
          [| new_array_type_vallist_match service_obj_t objvl |] **
          [| length objvl = ∘ (MAX_OBJ_NUM) |] ** 
          [| objvl = vll1 ++ (vl::vll2) |] ** 
          [| length vll1 = idx /\ length vll2 = ∘ (MAX_OBJ_NUM - Z.of_nat (S idx)) |] ** 
          [| Z.of_nat (S idx) <= MAX_OBJ_NUM |]) ** P.    
Proof. 
  introv Hsat Hlenle. 
  sep cancel 2%nat 2%nat.
  eapply AObjArr_unfold_any_idx; eauto.
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

(***********************)
