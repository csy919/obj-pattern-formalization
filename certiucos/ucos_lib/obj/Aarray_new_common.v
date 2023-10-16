Require Import List.
Require Export include_frm.
Require Import int_auto.
Require Export sep_auto.

Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Local Open Scope list_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

Lemma Aarray_new'_succ :
  forall s a vll n t b i, 
    s |= Aarray_new' (b,i) 1 t (a::nil) ** Aarray_new' (b,i +ᵢ  $ Z.of_nat  (typelen t)) n t vll -> 
    s |= Aarray_new' (b,i) (S n) t (a :: vll).
Proof.
intros.
destruct t;
simpl Aarray_new' in *;
destruct a;
try(eapply astar_l_afalse_elim in H; sep pauto);
try(destruct a);
try(eapply astar_l_afalse_elim in H);
try(sep pauto).
Qed.

Lemma Aarray_new'_succ_alt :
  forall s a vll n t b i P, 
    s |= Aarray_new' (b,i) 1 t (a::nil) ** Aarray_new' (b,i +ᵢ  $ Z.of_nat  (typelen t)) n t vll ** P -> 
    s |= Aarray_new' (b,i) (S n) t (a :: vll) ** P.
Proof.
intros.
sep pauto.
destruct t;
simpl Aarray_new' in *;
destruct a;
try(eapply astar_l_afalse_elim in H; sep pauto);
try(destruct a);
try(eapply astar_l_afalse_elim in H);
try(sep pauto).
Qed.

Lemma Aarray_new'_succ_imp :
  forall s a vll n t b i, 
    s |= Aarray_new' (b,i) (S n) t (a :: vll) ->
    s |= Aarray_new' (b,i) 1 t (a::nil) ** Aarray_new' (b,i +ᵢ  $ Z.of_nat  (typelen t)) n t vll.
Proof.
intros.
destruct t;
simpl Aarray_new' in *;
destruct a;
try(eapply astar_l_afalse_intro; sep pauto);
try(destruct a);
try(eapply astar_l_afalse_intro);
try(sep pauto).
Qed.

Lemma Aarray_new'_succ_imp_alt :
  forall s a vll n t b i P, 
    s |= Aarray_new' (b,i) (S n) t (a :: vll) ** P ->
    s |= Aarray_new' (b,i) 1 t (a::nil) ** Aarray_new' (b,i +ᵢ  $ Z.of_nat  (typelen t)) n t vll ** P.
Proof.
intros.
sep pauto.
destruct t;
simpl Aarray_new' in *;
destruct a;
try(eapply astar_l_afalse_intro; sep pauto);
try(destruct a);
try(eapply astar_l_afalse_intro);
try(sep pauto).
Qed.

Lemma Aarray_new'_compose :
  forall vll1 n vll2 m t b i s, 
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
    s |= Aarray_new' (b,i) n t vll1 ** Aarray_new' (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) m t vll2 -> 
    s |= Aarray_new' (b,i) (n + m) t (vll1 ++ vll2).
Proof.
induction vll1; induction n; intros.
clear H.
simpl Aarray_new' in H0.
assert (i +ᵢ  $ 0 = i) by int auto.
rewrite H in H0.
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
assert (Htrans: forall a b k, 0 <= a <= k /\ 0 <= b <= a -> 0 <= b <= k) by (auto with zarith).
assert (Ht: 0 <= Z.of_nat (typelen t) <= Int.max_unsigned /\ 0 <= Z.of_nat (n * typelen t) <= Int.max_unsigned).
{ clear -H H1 Htrans. split; eapply Htrans; int auto. }
assert ($ Z.of_nat (S n * typelen t) = $ Z.of_nat (typelen t) +ᵢ $ Z.of_nat (n * typelen t)).
{ simpl.
rewrite Nat2Z.inj_add.
clear -H H1 Ht.
simpl in H.
int auto. }
rewrite H2 in H0.
eapply IHvll1.
clear -H H1 Ht H2 Htrans.
int auto.
int auto.
rewrite Int.add_assoc.
sep pauto.
Qed.

Lemma Aarray_new'_compose_alt :
  forall vll1 n vll2 m t b i s P, 
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
    s |= Aarray_new' (b,i) n t vll1 ** Aarray_new' (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) m t vll2 ** P -> 
    s |= Aarray_new' (b,i) (n + m) t (vll1 ++ vll2) ** P.
Proof.
intros.
sep pauto.
eapply Aarray_new'_compose.
eauto.
sep pauto.
Qed.

Lemma Aarray_new'_split :
  forall vll1 n vll2 m t b i s, 
     s |= Aarray_new' (b,i) (n + m) t (vll1 ++ vll2) ->
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
      length vll1 = n /\ length vll2 = m ->
    s |= Aarray_new' (b,i) n t vll1 ** Aarray_new' (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) m t vll2.
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
(* simpl Aarray_new' in *. *)
(* eapply astar_l_afalse_intro. *)
(* simpl in H1. *)
eapply Aarray_new'_succ_alt.
change ((a :: vll1) ++ vll2) with (a :: (vll1 ++ vll2)) in H.
rewrite Nat.add_succ_l in H.
eapply Aarray_new'_succ_imp in H.
sep pauto.
assert (Htrans: forall a b k, 0 <= a <= k /\ 0 <= b <= a -> 0 <= b <= k) by (auto with zarith).
assert (Ht: 0 <= Z.of_nat (typelen t) <= Int.max_unsigned /\ 0 <= Z.of_nat (n * typelen t) <= Int.max_unsigned).
{ clear -H0 H3 Htrans. split; eapply Htrans; int auto. }
assert ($ Z.of_nat (S n * typelen t) = $ Z.of_nat (typelen t) +ᵢ $ Z.of_nat (n * typelen t)).
{ simpl.
rewrite Nat2Z.inj_add.
clear -H0 H3 Ht.
simpl in H0.
int auto. }
rewrite H4.
rewrite <- Int.add_assoc.
eapply IHvll1.
sep pauto.
clear -H0 H3 Ht H4 Htrans.
int auto.
int auto.
eauto.
Qed.

Lemma Aarray_new'_split_alt :
  forall vll1 n vll2 m t b i s P, 
     s |= Aarray_new' (b,i) (n + m) t (vll1 ++ vll2) ** P ->
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
      length vll1 = n /\ length vll2 = m ->
    s |= Aarray_new' (b,i) n t vll1 ** Aarray_new' (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) m t vll2 ** P.
Proof.
intros.
sep pauto.
eapply Aarray_new'_split;
eauto.
Qed.

Lemma Aarray_new_succ :
  forall s a vll n t b i, 
    s |= Aarray_new (b,i) (Tarray t 1) (a::nil) ** Aarray_new (b,i +ᵢ  $ Z.of_nat  (typelen t)) (Tarray t n) vll -> 
    s |= Aarray_new (b,i) (Tarray t (S n)) (a :: vll).
Proof.
unfold Aarray_new.
apply Aarray_new'_succ.
Qed.

Lemma Aarray_new_succ_alt :
  forall s a vll n t b i P, 
    s |= Aarray_new (b,i) (Tarray t 1) (a::nil) ** Aarray_new (b,i +ᵢ  $ Z.of_nat  (typelen t)) (Tarray t n) vll ** P -> 
    s |= Aarray_new (b,i) (Tarray t (S n)) (a :: vll) ** P.
Proof.
unfold Aarray_new.
apply Aarray_new'_succ_alt.
Qed.

Lemma Aarray_new_succ_imp :
  forall s a vll n t b i, 
    s |= Aarray_new (b,i) (Tarray t (S n)) (a :: vll) ->
    s |= Aarray_new (b,i) (Tarray t 1) (a::nil) ** Aarray_new (b,i +ᵢ  $ Z.of_nat  (typelen t)) (Tarray t n) vll.
Proof.
unfold Aarray_new.
apply Aarray_new'_succ_imp.
Qed.

Lemma Aarray_new_succ_imp_alt :
  forall s a vll n t b i P, 
    s |= Aarray_new (b,i) (Tarray t (S n)) (a :: vll) ** P ->
    s |= Aarray_new (b,i) (Tarray t 1) (a::nil) ** Aarray_new (b,i +ᵢ  $ Z.of_nat  (typelen t)) (Tarray t n) vll ** P.
Proof.
unfold Aarray_new.
apply Aarray_new'_succ_imp_alt.
Qed.

Lemma Aarray_new_compose :
  forall vll1 n vll2 m t b i s, 
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
    s |= Aarray_new (b,i) (Tarray t n) vll1 ** Aarray_new (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) (Tarray t m) vll2 -> 
    s |= Aarray_new (b,i) (Tarray t (n + m)) (vll1 ++ vll2).
Proof.
unfold Aarray_new.
apply Aarray_new'_compose.
Qed.

Lemma Aarray_new_compose_alt :
  forall vll1 n vll2 m t b i s P, 
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
    s |= Aarray_new (b,i) (Tarray t n) vll1 ** Aarray_new (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) (Tarray t m) vll2 ** P -> 
    s |= Aarray_new (b,i) (Tarray t (n + m)) (vll1 ++ vll2) ** P.
Proof.
unfold Aarray_new.
apply Aarray_new'_compose_alt.
Qed.

Lemma Aarray_new_split :
  forall vll1 n vll2 m t b i s, 
     s |= Aarray_new (b,i) (Tarray t (n + m)) (vll1 ++ vll2) ->
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
      length vll1 = n /\ length vll2 = m ->
    s |= Aarray_new (b,i) (Tarray t n) vll1 ** Aarray_new (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) (Tarray t m) vll2.
Proof.
unfold Aarray_new.
apply Aarray_new'_split.
Qed.

Lemma Aarray_new_split_alt :
  forall vll1 n vll2 m t b i s P, 
     s |= Aarray_new (b,i) (Tarray t (n + m)) (vll1 ++ vll2) ** P ->
     0 <= Int.unsigned i + Z.of_nat ((n + m) * (typelen t)) <= Int.max_unsigned ->
      length vll1 = n /\ length vll2 = m ->
    s |= Aarray_new (b,i) (Tarray t n) vll1 ** Aarray_new (b,i +ᵢ  $ Z.of_nat (n * (typelen t))) (Tarray t m) vll2 ** P.
Proof.
unfold Aarray_new.
apply Aarray_new'_split_alt.
Qed.

(* OS_MAX_EVENTS err *)
(* in os_code_defs.v, OS_MAX_EVENTS := 36 %Z *)
(* it should be 64 according to OS_CFG.h *)

Require Import os_inv.
Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

Lemma AObjArr_succ:
  forall s P b i vl vll,
    s |= GV obj_arr @ service_obj_t ∗ |-> Vptr (b,i) **
            Astruct (b,i) service_obj_t vl **
            Aarray_new (b, (i+ᵢ  $ Z.of_nat (typelen service_obj_t))) (Tarray service_obj_t (∘ (MAX_OBJ_NUM - 1))) vll ** P ->
     new_array_type_vallist_match service_obj_t (vl::vll) ->
     length (vl::vll) = ∘ MAX_OBJ_NUM ->
     s |= AObjArr (vl::vll) ** P . 
Proof.
  intros.
  unfold AObjArr.
  sep pauto.
Qed.

Lemma Aarray_new'_unfold:
  forall s  b i n vl vll, 
    s |= Aarray_new' (b, i) (S n) service_obj_t (vl :: vll) ->
    s |= Astruct (b, i) service_obj_t vl **
      Aarray_new' (b, i +ᵢ  $ Z.of_nat (typelen service_obj_t)) n service_obj_t vll.
Proof.
  introv H.
  unfold Aarray_new' in H.
  fold Aarray_new' in H.
  unfold service_obj_t in H.
  fold service_obj_t in H.
  auto.
Qed. 

Lemma AObjArr_succ_imp:
  forall s P vl vll,
    s |= AObjArr (vl::vll) ** P ->
    s |= (EX b i, GV obj_arr @ service_obj_t ∗ |-> Vptr (b,i) **
            Astruct (b,i) service_obj_t vl **
            Aarray_new (b, (i+ᵢ  $ Z.of_nat (typelen service_obj_t))) (Tarray service_obj_t (∘ (MAX_OBJ_NUM - 1))) vll ** 
            [| struct_type_vallist_match service_obj_t vl /\ 
                new_array_type_vallist_match service_obj_t vll /\
                length (vl::vll) = ∘ (MAX_OBJ_NUM)|]) ** P. 
Proof.
  unfold AObjArr.
  unfold Aarray_new.
  change (∘  (MAX_OBJ_NUM)) with 20%nat.
  change (∘ (MAX_OBJ_NUM - 1)) with 19%nat. 
  intros.
  sep cancel 2%nat 2%nat.
  destruct H.
  destruct x.
  exists b. exists i. sep cancel obj_arr. 
  unfold new_array_type_vallist_match in H.
  unfold service_obj_t in H.
  fold service_obj_t in H.
  fold new_array_type_vallist_match in H.
  sep split in H. sep split.
  2: {
    simpljoin1.
    splits; auto. 
  }
  apply Aarray_new'_unfold in H. auto.
Qed.

Lemma AObjArr_select_sn : 
  forall vll1 n vll2 b i s vl P, 
      Z.of_nat(S n) <= MAX_OBJ_NUM ->
     0 <= Int.unsigned i + (MAX_OBJ_NUM) * (Z.of_nat (typelen service_obj_t)) <= Int.max_unsigned ->
     s |= GV obj_arr @ service_obj_t ∗ |-> Vptr (b, i) **
              Aarray_new (b, i) (Tarray service_obj_t n) vll1 **
              Astruct (b,(i+ᵢ  $ Z.of_nat (n * (typelen service_obj_t)))) service_obj_t vl **
              Aarray_new (b, (i+ᵢ  $ Z.of_nat ( (S n) * (typelen service_obj_t)))) 
                      (Tarray service_obj_t (∘ (MAX_OBJ_NUM - Z.of_nat(S n)))) vll2 ** P -> 
     new_array_type_vallist_match service_obj_t (vll1 ++ (vl::vll2)) ->
     length (vll1 ++ (vl::vll2)) = ∘ (MAX_OBJ_NUM) -> 
    s |= AObjArr (vll1 ++ (vl::vll2)) ** P. 
Proof.
  intros.
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
  eapply Aarray_new_compose.
  rewrite <- Heq.
  eauto.
  sep pauto.
  eapply Aarray_new_succ.
  rewrite Int.add_assoc.
  assert ($ Z.of_nat (n * typelen service_obj_t) +ᵢ  $ Z.of_nat (typelen service_obj_t) 
          = $ Z.of_nat (S n * typelen service_obj_t)). 
  { 
    rewrite Nat.mul_succ_l.
    rewrite Nat2Z.inj_add.
    clear -H H0 H4.
    assert (Htrans: forall a b k, 0 <= a <= k /\ 0 <= b <= a -> 0 <= b <= k) by (auto with zarith).
    rewrite <- Nat.add_1_r in H.
    simpl in *.
    int auto.
    eapply Htrans.
    instantiate (1:=MAX_OBJ_NUM * 32). 
    split.
    simpl. int auto.
    split.
    int auto.
    eauto with zarith.
  }
  rewrite H5.
  sep pauto.
  unfold service_obj_t.
  unfold Aarray_new.
  unfold Aarray_new'.
  fold service_obj_t.
  sep pauto.
Qed.

Lemma AObjArr_select_sn_ex :
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
             [| 0 <= Int.unsigned i + (MAX_OBJ_NUM) * (Z.of_nat (typelen service_obj_t)) <= Int.max_unsigned |] **
              P ->
    s |= AObjArr objvl ** P. 
Proof.
  intros.
  do 6 destruct H.
  sep split in H.
  subst.
  eapply AObjArr_select_sn.
  eauto.
  eauto.
  sep pauto.
  eauto.
  eauto.
Qed.

Lemma AObjArr_unfold_sn:
  forall s objvl,
      s |= AObjArr objvl ->
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
             [| Z.of_nat(S n) <= MAX_OBJ_NUM |]. 
Proof.
  intros.
  unfold AObjArr in H. 
  destruct H.
  destruct x.
  sep split in H.
  destruct H0.
  destruct objvl. 
  inverts H1.
  do 6 eexists.
  instantiate (1 := 0%nat).
  instantiate (1 := objvl).
  instantiate (1 := nil).
  instantiate (1 := v).
  instantiate (1 := i).
  instantiate (1 := b).
  sep pauto.
  unfold Aarray_new in *.
  simpl Aarray_new' at 1.
  change ($ Z.of_nat (0 * typelen service_obj_t)) with ($ 0).
  change ($ Z.of_nat (1 * typelen service_obj_t)) with ($ Z.of_nat ( typelen service_obj_t)).  
  assert (i +ᵢ  $ 0 = i) by int auto.
  rewrite H2.
  sep pauto.
  change (MAX_OBJ_NUM) with 20.
  eauto with zarith.
Qed.

Lemma AObjArr_unfold_sn_alt: 
  forall s objvl P, 
     s |= AObjArr objvl ** P ->
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
             [| Z.of_nat(S n) <= MAX_OBJ_NUM |] ** P.
Proof.
  intros.
  unfold AObjArr in H. 
  eapply astar_l_aexists_elim in H.
  destruct H.
  destruct x.
  sep split in H.
  destruct H0.
  destruct objvl. 
  inverts H1.
  do 6 eexists.
  instantiate (1 := 0%nat).
  instantiate (1 := objvl). 
  instantiate (1 := nil).
  instantiate (1 := v).
  instantiate (1 := i).
  instantiate (1 := b).
  sep pauto.
  unfold Aarray_new in *.
  simpl Aarray_new' at 1.
  change ($ Z.of_nat (0 * typelen service_obj_t)) with ($ 0).
  change ($ Z.of_nat (1 * typelen service_obj_t)) with ($ Z.of_nat (typelen service_obj_t)).  
  assert (i +ᵢ  $ 0 = i) by int auto.
  rewrite H2.
  sep pauto.
  change (MAX_OBJ_NUM) with 20.  
  eauto with zarith.
Qed.

