
Require Import seplog_lemmas.

Require Import ucos_include.
Require Import symbolic_lemmas.
Require Import os_ucos_h.
Require Import Aarray_new_common.
Require Import Aarray_new_common_extend.
Require Import seplog_pattern_tacs.

Require Import os_code_defs.
Require Import get_free_obj_idx_spec.
Require Import obj_common.
Require Import obj_common_ext.
Require Import hoare_assign_tac_ext.

Local Open Scope code_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.
Local Open Scope int_scope.

Lemma get_free_obj_idx_proof:
    forall vl p r logicl ct, 
      Some p =
      BuildPreI new_os_internal get_free_obj_idx vl logicl getFreeObjIdxPre ct->
      Some r =
      BuildRetI new_os_internal get_free_obj_idx vl logicl getFreeObjIdxPost ct->
      exists t d1 d2 s,
        new_os_internal get_free_obj_idx = Some (t, d1, d2, s) /\
        {|new_OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
init spec.
subst logicl.
rename v' into vi.
rename v'0 into s.
rename v'1 into objvl.
rename v'2 into lg'.
(* i ′ =ₑ ′ 0 *)
hoare forward.
(*WHILE (′ MAX_OBJ_NUM >ₑ i ′) *)

(*1: remember irrelevant sep-conjunctions*)
hoare_lifts_trms_pre (AObjArr, Alvarmapsto i).
hoare remember (1 :: 2 :: nil)%nat pre.

(*2: get the while loop inv into the pre-condition,
    so the pre-condition after the while statement
    can be correctly instantiated
   *)

eapply backward_rule1 with (p := (*below is the loop inv*)
     (EX i p vl vll1 vll2 lb li,  LV os_code_defs.i @ Int32u |-> (V$ (Z.of_nat i)) **
      GV obj_arr @ service_obj_t ∗ |-> Vptr (lb, li) **
      Aarray_new (lb, li) (Tarray service_obj_t i) vll1 **
      Astruct (lb,(li+ᵢ  $ Z.of_nat (i * (typelen service_obj_t)))) service_obj_t vl **
      Aarray_new (lb, (li+ᵢ  $ Z.of_nat ( (S i) * (typelen service_obj_t))))
                            (Tarray service_obj_t (∘ (MAX_OBJ_NUM - Z.of_nat(S i)))) vll2 **
      [| new_array_type_vallist_match service_obj_t objvl |] **
      [| length objvl = ∘ (MAX_OBJ_NUM) |] **
      [| objvl = vll1 ++ (vl::vll2) |] ** 
      [| length vll1 = i /\ length vll2 = ∘ (MAX_OBJ_NUM - Z.of_nat(S i)) |] **
      [| Z.of_nat(S i) <= MAX_OBJ_NUM |] **
      [| ObjArr_full_P vll1  |] ** (* use for get out of the while loop *)
      [| V_ObjPtr vl = Some p /\ isptr p |] **
      H) \\//
    (
        LV os_code_defs.i @ Int32u |-> (V$ MAX_OBJ_NUM) **
      AObjArr objvl **
      [| ObjArr_full_P objvl  |] ** H)
    ).
intros.
left.
eapply AObjArr_unfold_any_idx_frm with (idxv:= 0%nat) in H0.
sep normal in H0.
sep destruct H0.
sep split in H0.
destruct H4.
apply length_zero_nil in H4.
subst x.
subst.
lets Hgetp: new_array_type_vallist_match_sem_getp H1.
destruct Hgetp as (p & Hvp & Hptr).
exists 0%nat.
exists p.
sep pauto.
apply ObjArr_full_P_nil.
unfold AObjArr in H0.
sep normal in H0.
destruct H0.
sep split in H0.
simpljoin.
rewrite H2.
simpl.
int auto.

 (*3: apply the 'seq_rule' to get the while statement
    off the remaining statements, then apply the 'while_rule'
   *)
eapply seq_rule.

(*4: prove the condition expression of while is legal *)
eapply while_rule with (tp := Int32u).
(*prove the condition expression of while is legal *)
intros.
(*2 cases*)
destruct H0.
symbolic_execution.
pure_auto.
symbolic_execution.
(*Aistrue (′ MAX_OBJ_NUM >ₑ i ′)*)

(*5: the cond-expr of while hold implies the left part
    of the loop-inv*)
  eapply backward_rule1 with ( p:= (
     EX i p vl vll1 vll2 lb li,  LV os_code_defs.i @ Int32u |-> (V$ (Z.of_nat i)) **
      GV obj_arr @ service_obj_t ∗ |-> Vptr (lb, li) **
      Aarray_new (lb, li) (Tarray service_obj_t i) vll1 **
      Astruct (lb,(li+ᵢ  $ Z.of_nat (i * (typelen service_obj_t)))) service_obj_t vl **
      Aarray_new (lb, (li+ᵢ  $ Z.of_nat ( (S i) * (typelen service_obj_t))))
                            (Tarray service_obj_t (∘ (MAX_OBJ_NUM - Z.of_nat(S i)))) vll2 **
      [| new_array_type_vallist_match service_obj_t objvl |] **
      [| length objvl = ∘ (MAX_OBJ_NUM) |] **
      [| objvl = vll1 ++ (vl::vll2) |] ** 
      [| length vll1 = i /\ length vll2 = ∘ (MAX_OBJ_NUM - Z.of_nat(S i)) |] **
      [| Z.of_nat(S i) <= MAX_OBJ_NUM |] **
      [| ObjArr_full_P vll1  |] ** (* use for get out of the while loop *)
      [| V_ObjPtr vl = Some p /\ isptr p |] **
      H
)). 
introv Hsat.
destruct Hsat as (Hsat & Histrue).
destruct Hsat as [Hsat | Hsat].
(*case 1*)
sep destruct Hsat.
sep eexists.
sep cancel 1%nat 1%nat.
(*case 2*)
sep remember (1::nil)%nat in Hsat.
false.
destruct_s s0.
simpl in Hsat; simpljoin1.
simpl in Histrue.
rewrite H10 in Histrue.
unfold cmp_int_type in Histrue.
unfold cmp_val in Histrue.
unfold cmpu in Histrue.
apply mapstoval_load in H11; auto.
lets Hload: H11.
eapply load_mono in Hload; eauto.
change (Int.unsigned Int.zero) with 0 in *.
rewrite Hload in Histrue.
rewrite H11 in Histrue.
change (Int.ltu ($ MAX_OBJ_NUM) ($ MAX_OBJ_NUM)) with false in Histrue.
simpl in Histrue.
destruct Histrue as (v & Heq & Hf).
inverts Heq.
simpl in Hf.
tryfalse.

(*If (efield (obj_arr ′ [i ′]) ptr ==ₑ NULL)*)
hoare_split_pure_all.
destruct H6 as (Hvp & Hptr).
assert (Hgetp: 
    (LV i @ long |-> (V$ Z.of_nat v') **
     GV obj_arr @ service_obj_t ∗ |-> Vptr (v'4, v'5) **
     Aarray_new (v'4, v'5) (Tarray service_obj_t v') v'2 **
     Astruct (v'4, v'5 +ᵢ  $ Z.of_nat (v' * typelen service_obj_t)) service_obj_t
       v'1 **
     Aarray_new (v'4, v'5 +ᵢ  $ Z.of_nat (S v' * typelen service_obj_t))
       (Tarray service_obj_t ∘ (MAX_OBJ_NUM - Z.of_nat (S v'))) v'3 **
     [|new_array_type_vallist_match service_obj_t objvl|] **
     [|length objvl = ∘ MAX_OBJ_NUM|] **
     [|objvl = v'2 ++ v'1 :: v'3|] **
     [| length v'3 = ∘ (MAX_OBJ_NUM - Z.of_nat (S v'))|] **
     [|Z.of_nat (S v') <= MAX_OBJ_NUM|] **
     [| ObjArr_full_P v'2  |] ** (* use for get out of the while loop *)
     [|V_ObjPtr v'1 = Some v'0 /\ isptr v'0|] ** H)
     ==> Rv (efield (obj_arr ′ [i ′]) ptr ==ₑ NULL) @ Int32 == val_inj(val_eq v'0 Vnull)).
{ introv Hsat.
eapply bop_rv.
sep_get_rv_array_struct.
eapply new_array_type_vallist_match_split in H0; eauto.
simpljoin; auto.
sep get rv.
unfold V_ObjPtr in Hvp.
eapply nth_val_nth_val'_some_eq in Hvp.
rewrite Hvp.
simpl; eauto.
pure_auto.
simpl; eauto.
}
(* actual if *)
hoare forward.
eapply ift_rule_general.
intros.
eexists.
eapply Hgetp.
sep pauto.
eauto.
(* if true *)
eapply backward_rule1 with (p := (
    (LV i @ long |-> (V$ Z.of_nat v') **
     GV obj_arr @ service_obj_t ∗ |-> Vptr (v'4, v'5) **
     Aarray_new (v'4, v'5) (Tarray service_obj_t v') v'2 **
     Astruct (v'4, v'5 +ᵢ  $ Z.of_nat (v' * typelen service_obj_t)) service_obj_t
       v'1 **
     Aarray_new (v'4, v'5 +ᵢ  $ Z.of_nat (S v' * typelen service_obj_t))
       (Tarray service_obj_t ∘ (MAX_OBJ_NUM - Z.of_nat (S v'))) v'3 **
     [|new_array_type_vallist_match service_obj_t objvl|] **
     [|length objvl = ∘ MAX_OBJ_NUM|] **
     [|objvl = v'2 ++ v'1 :: v'3|] **
     [| length v'3 = ∘ (MAX_OBJ_NUM - Z.of_nat (S v'))|] **
     [|Z.of_nat (S v') <= MAX_OBJ_NUM|] **
     [| ObjArr_full_P v'2  |] ** (* use for get out of the while loop *)
     [|V_ObjPtr v'1 = Some v'0 /\ isptr v'0|] ** H) **
     [| val_inj (val_eq v'0 Vnull) <> Vint32 Int.zero 
         /\ val_inj (val_eq v'0 Vnull) <> Vnull /\ val_inj (val_eq v'0 Vnull) <> Vundef |]
)).
lets Htrue:  sep_aconj_r_aistrue_to_astar Hgetp.
intros. eapply Htrue. clear Hgetp Htrue.
destruct H6.
eapply aconj_intro.
sep pauto.
sep pauto.

mytac_getret 1%nat.
instantiate (1:= Afalse).
clear Hgetp.
hoare unfold.
(* change ($ 0) with Int.zero. *)
hoare forward. (*RETURN i*)
sep cancel p_local.
eapply ObjArr_select_sn_ex_strong_frm.
sep auto.
pure_auto.
rewrite <- Byte.unsigned_repr_eq.
lets Hieq: user_max_obj_eq H4.
rewrite Hieq.
rewrite Byte.unsigned_repr.
2:{ clear -H4. unfold MAX_OBJ_NUM in *.   change Byte.max_unsigned with 255. int auto. }
unfold nth_ObjArr_free_P.
exists v'1.
rewrite H7.
change (Z.of_nat ∘ MAX_OBJ_NUM) with (MAX_OBJ_NUM).
rewrite nat_of_Z_of_nat.
splits.
clear -H4; int auto.
clear -H4; int auto.
apply nth_vallist_get_idx.
rewrite Hvp.
destruct H16 as [Heq | ((vp_b & vp_i) & Heq)]; subst; auto.
simpl in H13; tryfalse.
(* if false *)
eapply backward_rule1 with (p := (
    (LV i @ long |-> (V$ Z.of_nat v') **
     GV obj_arr @ service_obj_t ∗ |-> Vptr (v'4, v'5) **
     Aarray_new (v'4, v'5) (Tarray service_obj_t v') v'2 **
     Astruct (v'4, v'5 +ᵢ  $ Z.of_nat (v' * typelen service_obj_t)) service_obj_t
       v'1 **
     Aarray_new (v'4, v'5 +ᵢ  $ Z.of_nat (S v' * typelen service_obj_t))
       (Tarray service_obj_t ∘ (MAX_OBJ_NUM - Z.of_nat (S v'))) v'3 **
     [|new_array_type_vallist_match service_obj_t objvl|] **
     [|length objvl = ∘ MAX_OBJ_NUM|] **
     [|objvl = v'2 ++ v'1 :: v'3|] **
     [| length v'3 = ∘ (MAX_OBJ_NUM - Z.of_nat (S v'))|] **
     [|Z.of_nat (S v') <= MAX_OBJ_NUM|] **
     [| ObjArr_full_P v'2  |] ** (* use for get out of the while loop *)
     [|V_ObjPtr v'1 = Some v'0 /\ isptr v'0|] ** H) **
     [| val_inj (val_eq v'0 Vnull) = Vint32 Int.zero 
         \/ val_inj (val_eq v'0 Vnull) = Vnull |]
)).
introv Hsat.
destruct Hsat as [Hsat | Hsat]; tryfalse.
lets Hf:  sep_aconj_r_aisfalse_to_astar Hgetp.
eapply Hf. clear Hgetp Hf.
destruct Hsat.
eapply aconj_intro.
sep pauto.
sep pauto.
(* ++ i ′ *)
clear Hgetp.
hoare_split_pure 14%nat.
assert (Hveq: exists p, v'0 = Vptr p).
{ destruct Hptr as [Heq | ((vp_b & vp_i) & Heq)]; subst; eauto.
   simpl in H6; destruct H6; tryfalse.
}
assert (Hsuc: ($ Z.of_nat v' +ᵢ  $ 1) = ($ (Z.of_nat (S v')))).
{
  clear -H4.
  unfold MAX_OBJ_NUM in *.
  int auto.
}
assert (Hcond: Z.of_nat (S v') = MAX_OBJ_NUM \/ Z.of_nat (S v') < MAX_OBJ_NUM).
clear -H4.
int auto.
destruct Hcond as [Hc1 | Hc2].
(* case 1*)
eapply backward_rule1 with (p:= (LV i @ long |-> (V$ Z.of_nat v') ** AObjArr objvl ** H)).
intros.
sep cancel 1%nat 1%nat.
eapply AObjArr_select_sn_ex_strong.
sep pauto.
subst H.
hoare forward.
rewrite Hsuc in H.
rewrite Hc1 in H.
eapply adisj_intro.
right.
sep pauto.
rewrite Hc1 in H7.
simpl in H7.
eapply length_zero_nil in H7.
subst.
rewrite <- ObjArr_full_P_split.
split; auto.
unfold ObjArr_full_P.
simpl.
intros.
destruct (∘ i); tryfalse. inverts H7. rewrite Hvp. pure_auto.
(* case 2 *)
destruct v'3.
{
  false.
  destruct H3 as (Hlen & Hnil).
  clear -Hnil Hc2.
  change (length nil) with 0%nat in Hnil.
  unfold nat_of_Z in Hnil.
  unfold MAX_OBJ_NUM in *.
  auto with zarith.
}
eapply backward_rule1 with (p:= (LV i @ long |-> (V$ Z.of_nat v') **  AObjArr objvl ** H)).
intros.
sep cancel 1%nat 1%nat.
eapply AObjArr_select_sn_ex_strong.
sep pauto.
subst H.
hoare forward.
rewrite Hsuc in H.
eapply adisj_intro.
left.
sep lift 3%nat in H.
assert (Hvl: v'2 ++ v'1 :: v :: v'3 = (v'2 ++ (v'1 :: nil)) ++ (v :: v'3)).
{
simpl; rewrite app_assoc_reverse.
simpl. auto.
}
rewrite Hvl in *.
eapply AObjArr_split_frm in H.
sep destruct H.
sep split in H.
destruct H10 as (Hlen & Hnnil).
assert (Hl1: length (v'2 ++ v'1 :: nil) = S (length v'2)).
{ rewrite app_length. simpl. rewrite Nat.add_1_r. auto. }
rewrite Hl1 in Hlen.
rewrite <- Hlen in *.
lets Hgetp: new_array_type_vallist_match_sem_getp H8.
destruct Hgetp as (p & Hgetp).
sep auto.
clear -Hgetp. pure_auto.
rewrite <- ObjArr_full_P_split.
split; auto.
unfold ObjArr_full_P.
simpl.
intros.
destruct (∘ i); tryfalse. inverts H3. rewrite Hvp. pure_auto.

(* end of while Aistrue*)
(* start of while Aisfalse *)
mytac_getret 2%nat.
eapply backward_rule1 with (p := 
(
    (LV i @ long |-> (V$ MAX_OBJ_NUM) **
   AObjArr objvl ** [|ObjArr_full_P objvl|] ** H) **
     [| Vint32 Int.zero = Vint32 Int.zero \/ Vint32 Int.zero = Vnull |]
)).
introv Hsat.
destruct Hsat as (Hsat & Hfalse).
destruct Hsat as [Hsat | Hsat].
lets Hnew: aconj_intro Hsat Hfalse.
clear Hsat Hfalse.
eapply sep_aconj_r_aisfalse_to_astar in Hnew.
2 : {
introv Hsat.
sep destruct Hsat.
sep get rv.
sep split in Hsat.
assert (Hif: Int.ltu ($ Z.of_nat x) ($ MAX_OBJ_NUM) = true).
clear -H4.
unfold MAX_OBJ_NUM in *.
int auto.
rewrite Hif.
simpl. eauto. pure_auto.
}
sep normal in Hnew.
sep destruct Hnew.
sep split in Hnew.
destruct H7; tryfalse.

lets Hnew: aconj_intro  Hsat Hfalse.
clear  Hsat Hfalse.
eapply sep_aconj_r_aisfalse_to_astar in Hnew.
2 : {
intros.
sep get rv.
}
change (Int.ltu ($ MAX_OBJ_NUM) ($ MAX_OBJ_NUM)) with false in *.
sep split in Hnew.
simpl in H1.
sep pauto.

hoare unfold.
hoare forward.

Unshelve.
trivial.
Qed.

