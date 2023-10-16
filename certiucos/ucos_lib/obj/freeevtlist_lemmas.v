
Require Import os_inv.
Require Import inv_prop.

Require Import os_ucos_h.
Require Import ucos_include.
Require Import seplog_lemmas.
Require Import seplog_tactics.

Require Import memory.
Require Import Maps.
Require Import join_lib.

Require Import seplog_pattern_tacs. 

Local Open Scope code_scope.
Local Open Scope int_scope.

Lemma join_sub2_disjoint:
  forall (x1 x2 x1' x2' x : mem),
    join x1 x2 x ->
    sub x1' x1 ->
    sub x2' x2 ->
    disjoint x1' x2'.
Proof.
  intros.
  apply join_disj in H.
  lets H00: mem_sub_disjoint' H0 H; eauto.
  apply disj_sym in H00.
  lets H00': mem_sub_disjoint' H1 H00; eauto.
  apply disj_sym.
  auto.
Qed.  

Lemma ecb_dup_false:
  forall a vl1 vl2 s P, 
    s |= Astruct a OS_EVENT vl1 ** Astruct a OS_EVENT vl2 ** P ->
    (* struct_type_vallist_match OS_EVENT vl1 -> *)
    (* struct_type_vallist_match OS_EVENT vl2 ->  *)
    False. 
Proof.
  intros.
  simpl_sat H.
  simpljoin1.
  destruct_s s.
  change_smo_hyps. simp_mem_abst.
  unfold Astruct in *.
  unfold OS_EVENT in H3, H8.
  destruct vl1 eqn: E1; destruct vl2 eqn: E2.
  simpl in H3. tryfalse. 
  simpl in H3. tryfalse.
  simpl in H8. tryfalse.
  simpl in H3; simpl in H8; destruct a.
  simpl_sat H3. simpl_sat H8.
  simpljoin1.
  clear H15. clear H10.
  simpl in H14. simpl in H8.
  simpljoin1.
  assert (Hs1: sub x1 x0).
  {
    apply join_sub_l in H3. apply join_sub_l in H5. eapply sub_trans; eauto.
  }
  assert (Hs2: sub x13 x).
  {
    apply join_sub_l in H11. 
    auto.
  }  
  unfold mapstoval in H4. unfold mapstoval in H.
  simpljoin1.
  unfold ptomvallist in *.
  assert (Hlen1: length (encode_val Tint8 v) = typelen Tint8) by 
      (eapply encode_val_length; eauto). 
  assert (Hlen2: length (encode_val Tint8 v0) = typelen Tint8) by 
      (eapply encode_val_length; eauto). 
  simpl in Hlen1. simpl in Hlen2.
  destruct (encode_val Tint8 v) eqn: Eq1; destruct (encode_val Tint8 v0) eqn: Eq2.
  simpl in Hlen1. tryfalse. tryfalse. tryfalse.
  simpljoin1.
  unfold ptomval in *.
  assert (Hsub1: sub x11 x) by (eapply sub_trans; eauto; eapply join_sub_l; eauto).
  assert (Hsub2: sub x7 x0) by (eapply sub_trans; eauto; eapply join_sub_l; eauto).
  assert (Hdsj: disjoint x11 x7).
  {
     eapply join_sub2_disjoint with (x1:=x) (x2:=x0); eauto.
  }
  assert (Hget1: get x11 (b, Int.unsigned i2) = Some (true, m0)).
  {
    subst x11. join auto.
  }
  assert (Hget2: get x7 (b, Int.unsigned i2) = None).
  {
    clear -Hget1 Hdsj.
    assert (get x7 (b, Int.unsigned i2) = None \/
                 get x7 (b, Int.unsigned i2) = Some (true, m0) /\ isRw (true, m0) = false).
    eapply disjoint_semp1; eauto. 
    destruct H. auto. simpljoin1.
    unfold isRw in H0. unfold memMap in H0.
    simpl in H0. tryfalse.
  }
  subst x7.
  rewrite map_get_sig in Hget2.
  tryfalse.
Qed.  

Lemma struct_type_vallist_match_evt_ptr: 
  forall vl v,
    struct_type_vallist_match OS_EVENT vl ->
    V_OSEventListPtr vl = Some v ->
    isptr v. 
Proof.
  introv Hmt Hnxt.
  lets H00: struct_type_vallist_match_os_event Hmt.
  simpljoin1. 
  unfold V_OSEventListPtr in Hnxt. 
  simpl in Hnxt.
  inverts Hnxt.
  simpl in Hmt.
  simpljoin1.
  clear - H3.
  destruct v; tryfalse.
  unfold isptr. left; auto.
  unfold isptr. right; auto.
  eexists; eauto.
Qed.

Lemma ptr_in_ecbsllseg_ptr: 
  forall a v vll,
    ptr_in_ecbsllseg (Vptr a) v vll ->
    exists p, v = Vptr p. 
Proof.
  intros.
  destruct vll.
  simpl in H. tryfalse.
  simpl in H.
  destruct v; tryfalse.
  eexists; eauto.
Qed.   

Lemma isptr_ecbf_sllseg_frm: 
  forall s head eventl t next P,
    s |= ecbf_sllseg head Vnull eventl t next ** P -> isptr head.
Proof.
  introv Hsat.
  destruct Hsat.
  simpljoin1.
  eapply isptr_ecbf_sllseg; eauto.
Qed.

Lemma semacc_int_eq_true:
  forall i j,
    Int.eq i j = true ->
    i = j.
  intros.
  assert (Hif: if Int.eq i j then i = j else i <> j).
    eapply Int.eq_spec.
  rewrite H in Hif.
  auto.
Qed.

Lemma ecbf_sllseg_split2_frm: 
  forall vll s tn a a0 P, 
    s |= ecbf_sllseg (Vptr a0) tn vll OS_EVENT V_OSEventListPtr ** P ->
    ptr_in_ecblist (Vptr a) (Vptr a0) vll -> 
    s |= EX vll1 vll2, 
           ecbf_sllseg (Vptr a0) (Vptr a) vll1 OS_EVENT V_OSEventListPtr **
           ecbf_sllseg (Vptr a) tn vll2 OS_EVENT V_OSEventListPtr **
           [| vll = vll1 ++ vll2 |] ** P. 
Proof.
  induction vll.
  -
    intros.
    unfold ptr_in_ecblist in H0.
    simpl in H0.
    tryfalse.
  -
    introv Hsat Hin.
    rename a into vl.
    unfold ptr_in_ecblist in Hin. 
    simpl in Hin.
    destruct (os_inv.beq_addrval a0 a1) eqn: E. 
    +
      assert (a0 = a1).
      {
        unfold os_inv.beq_addrval in E.
        destruct a0; destruct a1.
        destruct (beq_pos b b0) eqn: E1.
        2: {  simpl in E. tryfalse. }
        destruct (Int.eq i i0) eqn: E2.
        2: { simpl in E. tryfalse. }
        clear E.
        rewrite beq_pos_Pos_eqb_eq in E1.
        rewrite Pos.eqb_eq in E1. subst. 
        apply semacc_int_eq_true in E2. subst.
        auto.
      }
      subst.
      exists (nil: list vallist) (vl::vll).
      unfold ecbf_sllseg at 1.
      sep split; auto.
    +    
      unfold ecbf_sllseg in Hsat.
      fold ecbf_sllseg in Hsat.
      sep normal in Hsat.
      sep destruct Hsat. (* new add *)
(*       destruct Hsat. destruct H. destruct H. *)
      sep_lifts_trms_in Hsat ecbf_sllseg.
      sep split in Hsat.
(*       inverts H0. *)
      rewrite H in Hin. (* change H4 -> H *)
      lets Hptr: ptr_in_ecbsllseg_ptr Hin.
      destruct Hptr as [p Hxp].
      subst x.
      lets H00: IHvll Hsat Hin.
      clear IHvll.
      sep destruct H00. (* new add *)
(*       destruct H00. destruct H0. *)
      sep split in H00.
      sep_lifts_trms_in H00 (node, Aarray x0, Aarray x2).
      exists (vl::x). exists x4 (* x2 *).
      sep split.
      2: {
        subst vll. simpl. auto.
      }
      unfold ecbf_sllseg at 1.
      fold ecbf_sllseg.
      sep normal.
      exists (Vptr p).
      exists x0. exists x1.
      exists x2. exists x3. (* new add *)
      sep split; auto.
Qed.   

Lemma ecbf_sllseg_split3_frm: 
  forall s vll a0 a P, 
    s |= ecbf_sllseg (Vptr a0) Vnull vll OS_EVENT V_OSEventListPtr ** P ->
    ptr_in_ecblist (Vptr a) (Vptr a0) vll -> 
    s |= EX vll1 vl vll2 ltbl vla vn lpetbl petbl, 
           [| V_OSEventListPtr vl = Some vn |] **
           ecbf_sllseg (Vptr a0) (Vptr a) vll1 OS_EVENT V_OSEventListPtr **
           node (Vptr a) vl OS_EVENT ** 
           Aarray ltbl (Tarray Tint8 (nat_of_Z OS_EVENT_TBL_SIZE)) vla **
           Aarray lpetbl (Tarray Tint8 (nat_of_Z OS_EVENT_TBL_SIZE)) petbl ** (* new add *)
           [|V_OSEventType vl = Some (V$ OS_EVENT_TYPE_UNUSED)|] ** 
           [| id_addrval' (Vptr a) OSEventTbl OS_EVENT = Some ltbl |] ** 
           [| id_addrval' (Vptr a) OSPostEventTbl OS_EVENT = Some lpetbl |] **
           ecbf_sllseg vn Vnull vll2 OS_EVENT V_OSEventListPtr **
           [| vll = vll1 ++ (vl :: vll2) |] ** P.  
Proof.
  intros.
  lets H00: ecbf_sllseg_split2_frm H H0.
  sep destruct H00.
  sep split in H00.
  destruct x0.
  unfold ecbf_sllseg at 2 in H00.
  sep split in H00. tryfalse.
  unfold ecbf_sllseg at 2 in H00.
  fold ecbf_sllseg in H00.
  sep normal in H00.
  sep destruct H00.
  sep split in H00.
  exists x. exists v. exists x0.
  exists x2. exists x3. exists x1.
  exists x4. exists x5. (* new add *)
  sep split; eauto.
  sep auto.
Qed.

Lemma ecbf_sllseg_head_vptr:
  forall head a0 vll s P, 
    s |= ecbf_sllseg head (Vptr a0) vll OS_EVENT V_OSEventListPtr ** P ->
    exists p, head = Vptr p.
Proof.
  introv Hsat.
  destruct vll.
  unfold ecbf_sllseg in Hsat.
  sep split in Hsat.
  eexists; eauto.
  unfold ecbf_sllseg in Hsat.
  fold ecbf_sllseg in Hsat.
  unfold node in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  simpljoin1.
  eexists; eauto.
Qed.   

Lemma ecbf_sllseg_compose2_frm:
  forall vll1 vll2 vll s tn a a0 P,
    s |= ecbf_sllseg (Vptr a0) (Vptr a) vll1 OS_EVENT V_OSEventListPtr **
           ecbf_sllseg (Vptr a) tn vll2 OS_EVENT V_OSEventListPtr **
           [| vll = vll1 ++ vll2 |] ** P ->
    s |= ecbf_sllseg (Vptr a0) tn vll OS_EVENT V_OSEventListPtr ** P.
Proof.
  inductions vll1.
  intros.
  unfold ecbf_sllseg at 1 in H.
  sep split in H.
  inverts H0.
  simpl in H1. subst.
  auto.

  introv Hsat.
  unfold ecbf_sllseg at 1 in Hsat.
  fold ecbf_sllseg in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  rewrite H3. (* H2 -> H3 *)
  change ((a :: vll1) ++ vll2) with (a::(vll1 ++ vll2)).
  unfold ecbf_sllseg.
  fold ecbf_sllseg.
  sep normal.
  exists x x0 x1.
  exists x2 x3. (* new add *)
  sep split; eauto.
  sep cancel node.
  sep cancel Aarray.
  sep cancel Aarray. (* new add *)

  lets H00: ecbf_sllseg_head_vptr Hsat.
  destruct H00 as (p & Hptr).
  subst.
  eapply IHvll1; eauto.
  sep pauto.
Qed.

Lemma ecbf_sllseg_compose3_frm:
  forall s vl vll vll1 vll2 vla ltbl a0 b vn P lpetbl petbl,
    s |= ecbf_sllseg (Vptr a0) (Vptr (b, Int.zero)) vll1 OS_EVENT V_OSEventListPtr **
           Astruct (b, Int.zero) OS_EVENT vl **
           Aarray ltbl (Tarray Tint8 (nat_of_Z OS_EVENT_TBL_SIZE)) vla **
           Aarray lpetbl (Tarray Tint8 (nat_of_Z OS_EVENT_TBL_SIZE)) petbl ** (* new add *)
           ecbf_sllseg vn Vnull vll2 OS_EVENT V_OSEventListPtr ** P ->
    vll = vll1 ++ (vl :: vll2) ->
    V_OSEventType vl = Some (V$ OS_EVENT_TYPE_UNUSED) ->
    V_OSEventListPtr vl = Some vn ->
    id_addrval' (Vptr (b, Int.zero)) OSEventTbl OS_EVENT = Some ltbl ->
    id_addrval' (Vptr (b, Int.zero)) OSPostEventTbl OS_EVENT = Some lpetbl -> (* new add *)
    struct_type_vallist_match OS_EVENT vl ->
    s |= ecbf_sllseg (Vptr a0) Vnull vll OS_EVENT V_OSEventListPtr ** P.
Proof. 
  introv Hsat Hvll Husd Hvn Hltbl Hlpetbl Hmt.
  subst vll.
  eapply ecbf_sllseg_compose2_frm; eauto.
  sep cancel (ecbf_sllseg (Vptr a0)).
  sep split; eauto.
  unfold ecbf_sllseg.
  fold ecbf_sllseg.
  sep normal.
  exists vn ltbl vla.
  sep split; eauto.
  sep pauto.
  sep cancel Aarray. (* new add *)
  unfold node.
  exists b.
  sep split; eauto.
  eauto. (* new add *)
Qed.

Lemma hd_not_in_evt_freelist: 
  forall vll s a vl p P, 
    s |= Astruct a OS_EVENT vl ** ecbf_sllseg (Vptr p) Vnull vll OS_EVENT V_OSEventListPtr ** P -> 
    V_OSEventListPtr vl = Some (Vptr p) -> 
    ~ptr_in_ecblist (Vptr a) (Vptr p) vll. 
Proof.
  intros.
  introv Hf.
  sep_lifts_trms_in H ecbf_sllseg.  
  lets H00: ecbf_sllseg_split3_frm H Hf.
  sep destruct H00.
  sep split in H00.
  unfold node in H00.
  sep normal in H00.
  sep destruct H00. sep split in H00.
  sep_lifts_trms_in H00 (Astruct a). 
  destruct H6. inverts H6. (* H5 -> H6 *)
  sep remember (1::2::nil)%nat in H00.
  apply ecb_dup_false in H00.
  auto.
Qed. 
