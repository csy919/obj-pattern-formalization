Require Import seplog_pattern_tacs.
Require Import symbolic_lemmas.
Require Import OSTimeTickPure.
Require Import OSQPostPure.

Open Scope list_scope.
Open Scope int_scope.
Open Scope Z_scope.
Open Scope code_scope.

Ltac mytac :=
  heat; jeauto2.

Fixpoint set_tls_rdy (wl: list addrval) (tls: TcbMod.map) : TcbMod.map :=
match wl with
 | nil => tls
 | tid :: wl' => match TcbMod.get tls tid  with 
                            | None => set_tls_rdy wl' tls
                            | Some (p, st, m) => set_tls_rdy wl' (set tls tid (p,rdy,Vnull))
                            end
end.

Definition is_subl  (subwl : list tid) (wl: list tid) :=
(forall t, In t subwl -> In t wl) /\
(forall t, ~(In t wl) -> ~(In t subwl)) /\
NoDup subwl /\
(length subwl < length wl)%nat.

Fixpoint remove_wls (l: list tid) (wls: list tid) : list tid :=
match l with
 | nil => wls
 | tid :: l' => remove_wls l' (remove_tid tid wls)
end.

Lemma eqdomtls_set_tls_rdy_gen:
forall wl tls tls', eqdomtls tls tls' -> eqdomtls tls (set_tls_rdy wl tls').
Proof.
induction wl.
simpl.
auto.
intros.
simpl.
destruct (TcbMod.get tls' a) eqn: eq1.
destruct b. destruct p.
eapply IHwl;eauto.
eapply eqdomtls_trans; eauto.
eapply tls_get_set_indom;eauto.
eapply IHwl;eauto.
Qed.

Lemma eqdomtls_set_tls_rdy:
forall wl tls, eqdomtls tls (set_tls_rdy wl tls).
Proof.
intros.
eapply eqdomtls_set_tls_rdy_gen.
apply eqdomtls_same.
Qed.

Lemma nil_is_subl:
forall wl, wl <> nil -> is_subl nil wl.
Proof.
unfold is_subl.
induction wl.
intros. tryfalse.
intros.
splits; auto.
intros.
tryfalse.
apply NoDup_nil.
simpl length in *.
auto with zarith.
Qed.

Lemma RL_Tbl_Grp_P_zero_impl:
forall etbl, 
array_type_vallist_match Int8u etbl ->
length etbl = ∘ OS_EVENT_TBL_SIZE ->
RL_Tbl_Grp_P etbl (Vint32 Int.zero) -> 
(forall n, (0 <= n < 8)%nat -> nth_val' n etbl = Vint32 Int.zero).
Proof.
intros.
eapply array_type_match_get_value in H; eauto.
destruct H.
instantiate (1:= Z.of_nat n) in H.
rewrite Nat2Z.id in H.
assert (Vint32 Int.zero = Vint32 Int.zero) by auto.
lets Heq: H1 H2 H H3.
eapply nth_val_nth_val'_some_eq in H.
rewrite H.
rewrite Int.and_zero_l in Heq.
change ($ 0) with Int.zero in Heq.
pure_auto.
subst; auto.
auto with zarith.
Qed.

Lemma Grp_eq_zero_imp_wl_nil:
forall etbl eid osevent els tcbls ct n wls petbl, 
array_type_vallist_match Int8u etbl ->
length etbl = ∘ OS_EVENT_TBL_SIZE ->
RL_Tbl_Grp_P etbl (Vint32 Int.zero) -> 
R_ECB_ETbl_P eid (osevent, etbl,petbl) tcbls ->
RH_TCBList_ECBList_P els tcbls ct ->
EcbMod.get els eid = Some (abssem n, wls) ->
wls = nil.
Proof.
intros.
lets Hk: RL_Tbl_Grp_P_zero_impl H H0 H1.
funfold H2.
funfold H2.
funfold H5.
assert(~(exists prio, PrioWaitInQ (Int.unsigned prio) etbl )).
{ pure_auto.
  destruct H13.
  eapply prioinq_exists in H13.
  destruct H13 as (i & Hi & Hnth).
  lets Heq: Hi.
  eapply Hk in Hi.
  eapply nth_val'_imply_nth_val in Hi;eauto.
  rewrite H0; unfold OS_EVENT_TBL_SIZE; unfold nat_of_Z; auto with zarith.
}
assert (Hwl: wls = nil \/ wls <> nil) by tauto.
destruct Hwl;auto.
assert ((exists tid, In tid wls) \/ ~(exists tid, In tid wls)) by tauto.
destruct H15.
2:{ induction wls. tryfalse. simpl in H15.
      false. eapply H15. eauto. }
destruct H15 as (tid & Hin).
funfold H3.
assert (exists prio m t,  get tcbls tid = Some (prio, wait (os_stat_sem eid) t, m)).
eapply H15;eauto.
mytac.
eapply H10 in H18.
mytac.
false.
eapply H13;eauto.
Qed.

Lemma Grp_eq_nz_imp_wl_not_nil:
forall etbl eid osevent els tcbls ct n wls egrp petbl, 
array_type_vallist_match Int8u etbl ->
length etbl = ∘ OS_EVENT_TBL_SIZE ->
RL_Tbl_Grp_P etbl (Vint32 egrp) -> 
egrp <> Int.zero ->
R_ECB_ETbl_P eid (osevent, etbl,petbl) tcbls ->
RH_TCBList_ECBList_P els tcbls ct ->
EcbMod.get els eid = Some (abssem n, wls) ->
V_OSEventType osevent = Some (V$ OS_EVENT_TYPE_SEM) ->
Int.unsigned egrp <= 255 ->
wls <> nil.
Proof.
intros.
rename H6 into Hetype.
rename H7 into Heg_r.
assert (Hwl: wls = nil \/ wls <> nil) by tauto.
destruct Hwl;auto.
assert (~(exists tid, In tid wls)).
subst; simpl. pure_auto.
mytac.
assert (~(exists tid prio m t,  get tcbls tid = Some (prio, wait (os_stat_sem eid) t, m))).
{ pure_auto.
   mytac.
   funfold H4.
   eapply H6 in H8.
   unfold get in H8; unfold EcbMap in H8.
   mytac.
   rewrite H5 in H8; inverts H8.
  eapply H7; eauto.
}
funfold H3.
funfold H3.
funfold H9.
assert(~(exists prio, PrioWaitInQ (Int.unsigned prio) etbl )).
{ pure_auto.
   destruct H17.
   eapply H6 in H11; eauto.
   rewrite Int.repr_unsigned in H11.
   mytac.
  eapply H8; eauto.
}
assert (~(exists n, (0 <= n < 8)%nat /\ nth_val n etbl <> Some (V$ 0))).
pure_auto.
destruct H18 as (i & Hi & Hnth).
eapply array_int8u_nth_lt_len in H; eauto.
instantiate (1:= i) in H.
destruct H as (x & Hnth' & Hx_range).
eapply nth_val'_imply_nth_val in Hnth'; eauto.
assert (Vint32 egrp = Vint32 egrp) by auto.
eapply H1 in H; eauto.
lets Hcp : Hnth'.
eapply prio_inq in Hcp;eauto.
destruct Hcp as (prio & Hcp).
eapply H17.
exists ($ prio).
assert (Heq: Int.unsigned ($ prio) = prio).
eapply Int.unsigned_repr.
funfold Hcp.
clear -H18 H23. int auto.
rewrite Heq.
auto.
eapply int_eq_false_ltu.
eapply Int.eq_false.
rewrite Hnth' in Hnth.
pure_auto.
rewrite H0; unfold OS_EVENT_TBL_SIZE; unfold nat_of_Z; auto with zarith.
rewrite H0; unfold OS_EVENT_TBL_SIZE; unfold nat_of_Z; auto with zarith.
false.
assert (forall n, (0 <= n < 8)%nat -> nth_val n etbl = Some (V$ 0)).
intros.
eapply Classical_Pred_Type.not_ex_all_not in H18.
instantiate (1:= n0%nat) in H18.
eapply Classical_Prop.not_and_or in H18.
destruct H18; tryfalse.
assert ( nth_val n0 etbl <> Some (V$ 0) \/  nth_val n0 etbl = Some (V$ 0)) by tauto.
destruct H20;auto.
destruct H18;auto.
clear H18.
lets Hneq: Int.eq_false H2.
change Int.zero with ($ 0) in Hneq.
eapply int8_neq0_ex in Hneq;eauto.
destruct Hneq as (k & Hk & Heg).
lets Hk': H19 Hk.
assert (Vint32 egrp = Vint32 egrp) by auto.
eapply H1 in H18; eauto.
destruct H18 as (_ & (Hf & _)).
eapply Hf in Heg.
change (Int.ltu ($ 0) ($ 0)) with false in Heg; tryfalse.
Qed.

Lemma set_tls_rdy_nil:
forall tls, set_tls_rdy nil tls = tls.
Proof.
simpl. auto.
Qed.

Lemma set_tls_rdy_join:
forall wls tls1 tls2 tls,
TcbMod.join tls1 tls2 tls ->
TcbMod.join (set_tls_rdy wls tls1) (set_tls_rdy wls tls2)
  (set_tls_rdy wls tls).
Proof.
induction wls; intros.
erewrite set_tls_rdy_nil; auto.
simpl.
lets Hcp: H.
unfold TcbMod.join in Hcp.
unfold get in *.
unfold TcbMap in *.
specialize Hcp with (a:= a).
destruct (TcbMod.get tls1 a) eqn: eq1;
try destruct b as ((p & st) & m);
destruct (TcbMod.get tls2 a) eqn: eq2;
try destruct b as ((p' & st') & m');
tryfalse.
lets Heq: eq1.
eapply TcbMod.join_get_l in eq1; eauto.
rewrite eq1.
eapply IHwls; eauto.
eapply TcbMod.join_set_l; eauto.
unfold TcbMod.indom; eauto.
lets Heq: eq2.
eapply TcbMod.join_get_r in eq2; eauto.
rewrite eq2.
eapply IHwls; eauto.
eapply TcbMod.join_set_r; eauto.
unfold TcbMod.indom; eauto.
eapply TcbMod.map_join_get_none in eq1; eauto.
rewrite eq2 in eq1.
rewrite eq1.
eapply IHwls; eauto.
Qed.

Lemma set_tls_rdy_get_some:
forall a wls tls p st m, 
get tls a = Some (p,st,m) ->
exists st' m', get (set_tls_rdy wls tls) a = Some (p, st', m').
Proof.
induction wls.
simpl. eauto.
simpl.
intros.
destruct (TcbMod.get tls a0) eqn: eq1.
destruct b as ((p' & st') & m').
assert (Htd:  a0 = a \/ a0 <> a) by tauto.
destruct Htd.
subst.
eapply IHwls.
rewrite TcbMod.map_get_set.
unfold get,set in *; unfold TcbMap in *.
rewrite H in eq1. inverts eq1.
eauto.
eapply IHwls.
eapply TcbMod.map_get_set' in H0.
unfold get,set; unfold TcbMap.
erewrite H0.
eauto.
eapply IHwls; eauto.
Qed.

Lemma set_tls_rdy_get_none:
forall a wls tls, 
get tls a = None ->
get (set_tls_rdy wls tls) a = None.
Proof.
induction wls.
simpl; auto.
simpl.
intros.
destruct (TcbMod.get tls a0) eqn: eq1.
destruct b as ((p & st) & m).
assert (Htd:  a0 = a \/ a0 <> a) by tauto.
destruct Htd.
subst.
unfold get,set in *; unfold TcbMap in *.
rewrite H in eq1. inverts eq1.
eapply IHwls.
rewrite TcbMod.map_get_set'; auto.
eapply IHwls; eauto.
Qed.


Lemma set_tls_rdy_succ_eq:
forall (wls: list tid) (a: addrval) (tls: TcbMod.map),
set_tls_rdy (a :: nil) (set_tls_rdy wls tls) = set_tls_rdy (a :: wls) tls.
Proof.
induction wls.
simpl. auto.
intros.
specialize IHwls with (a:= a0) (tls:= set_tls_rdy (a :: nil) tls).
simpl set_tls_rdy in *.
unfold get,set in *; unfold TcbMap in *.
destruct (TcbMod.get tls a) eqn: eq1.
destruct b as ((p & st) & m).
rewrite IHwls.
destruct (TcbMod.get tls a0) eqn: eq2.
destruct b as ((p' & st') & m').
rewrite TcbMod.set_sem.
rewrite TcbMod.set_sem.
destruct (tidspec.beq a a0) eqn: eq3;
lets Heq: TcbMod.beq_sym eq3;
rewrite Heq.
eapply tidspec.beq_true_eq in eq3; subst.
rewrite eq1 in eq2; inverts eq2.
auto.
rewrite eq1; rewrite eq2.
eapply tidspec.beq_false_neq in eq3.
erewrite neq_set_comm; eauto.
rewrite TcbMod.set_sem.
destruct (tidspec.beq a a0) eqn: eq3.
eapply tidspec.beq_true_eq in eq3; subst.
rewrite eq1 in eq2; inverts eq2.
rewrite eq2. auto.
rewrite IHwls.
destruct (TcbMod.get tls a0) eqn: eq2.
destruct b as ((p' & st') & m').
rewrite TcbMod.set_sem.
destruct (tidspec.beq a0 a) eqn: eq3.
eapply tidspec.beq_true_eq in eq3; subst.
rewrite eq1 in eq2; inverts eq2.
rewrite eq1. auto.
auto.
Qed.

Lemma set_tls_rdy_get_some_in:
forall a wls tls p st m, 
In a wls ->
get tls a = Some (p,st,m) ->
get (set_tls_rdy wls tls) a = Some (p, rdy, Vnull).
Proof.
induction wls; intros.
simpl in *.
tryfalse.
simpl in H.
destruct H.
subst.
rewrite <- set_tls_rdy_succ_eq.
simpl.
eapply set_tls_rdy_get_some in H0.
mytac.
rewrite H.
rewrite TcbMod.map_get_set.
auto.
rewrite <- set_tls_rdy_succ_eq.
simpl.
destruct (get tls a0) eqn: eq2.
destruct p0 as ((p' & st') & m').
lets Hget: set_tls_rdy_get_some eq2.
mytac.
rewrite H1.
rewrite TcbMod.set_sem.
destruct (tidspec.beq a0 a) eqn:eq1.
eapply tidspec.beq_true_eq in eq1; subst.
rewrite H0 in eq2; inverts eq2.
auto.
eapply IHwls; eauto.
lets Hget: set_tls_rdy_get_none eq2.
rewrite Hget.
eapply IHwls; eauto.
Qed.




Lemma remove_wls_nil
: forall wls, remove_wls nil wls = wls.
Proof.
simpl; auto.
Qed.

Lemma is_subl_succ:
forall subwl wls a,
is_subl (a :: subwl) wls -> is_subl subwl wls.
Proof.
unfold is_subl.
intros.
mytac.
splits; intros.
eapply H; simpl; auto.
eapply H0 in H3.
rewrite not_in_cons in H3.
destruct H3; auto.
eapply NoDup_cons_iff in H1.
destruct H1; auto.
simpl length in *.
auto with zarith.
Qed.

Lemma remove_wls_succ_eq:
forall (subwl wls: list tid) (a: addrval), remove_wls (a :: subwl) wls = remove_tid a (remove_wls subwl wls).
Proof.
induction subwl.
simpl. auto.
intros.
assert (remove_wls (a0 :: a :: subwl) wls = remove_wls (a0 :: subwl) (remove_tid a wls)).
simpl; rewrite remove_tid_eq; auto.
rewrite H.
erewrite IHsubwl.
simpl. auto.
Qed.

Lemma in_remove_wls:
forall subwl wls t, In t (remove_wls subwl wls) -> In t wls.
Proof.
induction subwl.
simpl; auto.
intros.
rewrite remove_wls_succ_eq in H.
eapply IHsubwl; eapply in_remove_tid; eauto.
Qed.

Lemma in_remove_wls_nin:
forall subwl wls t, In t (remove_wls subwl wls) -> ~(In t subwl).
Proof.
induction subwl.
simpl; auto.
intros.
rewrite remove_wls_succ_eq in H.
rewrite not_in_cons.
assert (t = a \/ t <> a) by tauto.
destruct H0.
subst.
eapply in_remove_tid_false in H; tryfalse.
split; auto.
eapply IHsubwl; eapply in_remove_tid; eauto.
Qed.

Lemma remove_sub_wls_eq:
forall subwl wls, 
is_subl subwl wls ->
(forall t, In t (subwl ++ remove_wls subwl wls) <-> In t wls).
Proof.
induction subwl.
simpl. tauto.
intros.
lets Hsub: is_subl_succ H.
eapply IHsubwl in Hsub.
assert (In a wls).
eapply H; simpl; eauto.
split; intros.
rewrite remove_wls_succ_eq in H1.
simpl in H1.
destruct H1.
subst; auto.
eapply in_app_or in H1.
destruct H1.
eapply H; simpl; auto.
eapply in_remove_wls; eapply in_remove_tid; eauto.
rewrite <- Hsub in H1.
rewrite remove_wls_succ_eq.
simpl.
assert (a = t \/ a <> t) by tauto.
destruct H2; auto.
right.
eapply in_app_or in H1.
eapply in_or_app.
destruct H1; auto.
right.
eapply in_remove_tid'; eauto.
Qed.

Lemma is_subl_length_lt:
forall subwl wls, is_subl subwl wls -> (S (length subwl) <= length wls)%nat.
Proof.
intros.
funfold H.
(* eapply NoDup_incl_length in H1; eauto. *)
auto with zarith.
Qed.

Lemma remove_sub_wls_eq_gen:
forall subwl wls, 
(forall t, In t subwl -> In t wls) ->
(forall t, ~ In t wls -> ~ In t subwl) ->
(forall t, In t (subwl ++ remove_wls subwl wls) <-> In t wls).
Proof.
induction subwl.
simpl. tauto.
intros.
assert (Hsub: forall t, In t (subwl ++ remove_wls subwl wls) <-> In t wls).
{ eapply IHsubwl.
   intros.
   eapply H; simpl; auto.
   intros.
   eapply H0 in H1.
   eapply not_in_cons in H1.
   destruct H1; auto.
}
assert (In a wls).
eapply H; simpl; eauto.
split; intros.
rewrite remove_wls_succ_eq in H2.
simpl in H2.
destruct H2.
subst; auto.
eapply in_app_or in H2.
destruct H2.
eapply H; simpl; auto.
eapply in_remove_wls; eapply in_remove_tid; eauto.
rewrite <- Hsub in H2.
rewrite remove_wls_succ_eq.
simpl.
assert (a = t \/ a <> t) by tauto.
destruct H3; auto.
right.
eapply in_app_or in H2.
eapply in_or_app.
destruct H2; auto.
right.
eapply in_remove_tid'; eauto.
Qed.

Lemma remove_tid_nin_eq:
forall wls a, ~(In a wls) -> remove_tid a wls = wls.
Proof.
induction wls.
simpl. auto.
intros.
eapply not_in_cons in H.
destruct H.
simpl.
destruct (os_inv.beq_addrval a0 a) eqn: eq1.
eapply beq_tid_true_eq in eq1; subst.
tryfalse.
eapply IHwls in H0.
rewrite H0. auto.
Qed.

Lemma set_tls_rdy_in_same:
forall a wls tls,
In a wls ->
set_tls_rdy (a :: wls) tls = set_tls_rdy wls tls.
Proof.
intros.
rewrite <- set_tls_rdy_succ_eq.
simpl.
destruct (get tls a) eqn: eq1.
destruct p as ((p & st) & m).
lets Hget: set_tls_rdy_get_some eq1.
mytac.
rewrite H0.
eapply TcbMod.get_set_same.
eapply set_tls_rdy_get_some_in in eq1; eauto.
lets Hget: set_tls_rdy_get_none eq1.
rewrite Hget.
auto.
Qed.

Lemma set_tls_rdy_comm:
forall a a0 wls tls,
set_tls_rdy (a :: a0 :: wls) tls = set_tls_rdy (a0 :: a :: wls) tls.
Proof.
intros.
assert (a = a0 \/ a <> a0) by tauto.
destruct H.
subst; auto.
lets Heq1: tidspec.neq_beq_false H.
lets Heq2: TcbMod.beq_sym Heq1.
simpl.
unfold get,set; unfold TcbMap.
destruct (TcbMod.get tls a) eqn: eq1;
try destruct b as ((p & st) & m);
destruct (TcbMod.get tls a0) eqn: eq2;
try destruct b as ((p' & st') & m');
repeat try rewrite TcbMod.set_sem;
try rewrite Heq1; try rewrite Heq2;
try rewrite eq1; try rewrite eq2;
auto.
eapply neq_set_comm in H; rewrite H; auto.
Qed.

Lemma set_tls_rdy_alt_remove:
forall wls a tls,
In a wls ->
set_tls_rdy wls tls = set_tls_rdy (a :: remove_tid a wls) tls.
Proof.
induction wls.
simpl. intros; tryfalse.
intros.
simpl in H.
destruct H.
subst.
simpl remove_tid.
rewrite beq_tid_true.
assert (In a0 wls \/ ~(In a0 wls)) by tauto.
destruct H.
lets Hin: H.
eapply IHwls in H.
rewrite <- H.
eapply set_tls_rdy_in_same; eauto.
eapply remove_tid_nin_eq in H.
rewrite H; auto.
lets Hin: H.
simpl remove_tid.
destruct (os_inv.beq_addrval a0 a) eqn: eq1.
eapply beq_tid_true_eq in eq1; subst.
eapply IHwls in H.
rewrite <- H.
eapply set_tls_rdy_in_same; eauto.
rewrite set_tls_rdy_comm.
rewrite <- set_tls_rdy_succ_eq with (a:= a).
rewrite <- set_tls_rdy_succ_eq with (a:= a) (tls:= tls).
eapply IHwls in H. rewrite <- H. auto.
Qed.


Lemma set_tls_rdy_eq:
forall wls1 wls2 tls,
(forall t, In t wls1 -> In t wls2) ->
(forall t, In t wls2 -> In t wls1) ->
set_tls_rdy wls1 tls = set_tls_rdy wls2 tls.
Proof.
induction wls1.
simpl.
intros.
assert (wls2 = nil \/ wls2 <> nil) by tauto.
destruct H1; try subst; simpl; auto.
eapply qwaitset_notnil_ex in H1.
destruct H1.
eapply H0 in H1.
tryfalse.
intros.
assert (Hin: In a wls2).
eapply H; simpl; auto.
assert (Ht1: forall t : tid, In t wls1 -> In t wls2).
intros.
eapply H; simpl; auto.
assert (Ha: In a wls1 \/ ~(In a wls1)) by tauto.
destruct Ha as [Ha | Ha].
assert (Ht2: forall t : tid, In t wls2 -> In t wls1).
intros.
eapply H0 in H1.
simpl in H1.
destruct H1; try subst; auto.
lets Heq: IHwls1 Ht1 Ht2.
rewrite <- Heq.
rewrite <- set_tls_rdy_succ_eq.
simpl.
destruct (get tls a) eqn: eq1.
destruct p as ((p & st) & m).
lets Hget: set_tls_rdy_get_some eq1.
mytac.
rewrite H1.
eapply TcbMod.get_set_same.
eapply set_tls_rdy_get_some_in in eq1; eauto.
lets Hget: set_tls_rdy_get_none eq1.
rewrite Hget.
auto.
assert (Ht1': forall t : tid, In t wls1 -> In t (remove_tid a wls2)).
intros.
assert (t = a \/ t <> a) by tauto.
destruct H2.
subst; tryfalse. tauto.
eapply in_remove_tid'; eauto.
assert (Ht2: forall t : tid, In t (remove_tid a wls2) -> In t wls1).
intros.
lets Hin': H1.
eapply in_remove_tid in Hin'; eauto.
eapply H0 in Hin'.
simpl in Hin'.
lets Hf: in_remove_tid_false wls2 a.
destruct Hin'.
subst.
tryfalse.
auto.
lets Heq: IHwls1 Ht1' Ht2.
rewrite <- set_tls_rdy_succ_eq.
rewrite Heq.
rewrite set_tls_rdy_succ_eq.
eapply set_tls_rdy_alt_remove in Hin.
rewrite Hin.
auto.
Qed.

Lemma set_tls_rdy_eq':
forall wls1 wls2 tls,
(forall t, In t wls1 <-> In t wls2) ->
set_tls_rdy wls1 tls = set_tls_rdy wls2 tls.
Proof.
intros.
eapply set_tls_rdy_eq; eauto.
intros. eapply H; eauto.
intros. eapply H; eauto.
Qed.

Lemma set_tls_rdy_eq_alt:
forall subwl wls tls,
is_subl subwl wls ->
set_tls_rdy (subwl ++ remove_wls subwl wls) tls = set_tls_rdy wls tls.
Proof.
intros.
eapply set_tls_rdy_eq'; eauto.
eapply remove_sub_wls_eq; eauto.
Qed.

Lemma set_tls_rdy_eq_alt_gen:
forall subwl wls tls,
(forall t, In t subwl -> In t wls) ->
(forall t, ~ In t wls -> ~ In t subwl) ->
set_tls_rdy (subwl ++ remove_wls subwl wls) tls = set_tls_rdy wls tls.
Proof.
intros.
eapply set_tls_rdy_eq'; eauto.
eapply remove_sub_wls_eq_gen; eauto.
Qed.

Lemma remove_wls_succ_set_els_eq:
forall subwl wls a els eid st st',
EcbMod.set (EcbMod.set els eid (st', remove_wls subwl wls)) 
                               eid (st, remove_tid a (remove_wls subwl wls))
= EcbMod.set els eid (st, remove_wls (a:: subwl) wls).
Proof.
intros.
rewrite ecbmod_set_eq with (b':= (st, remove_wls (a :: subwl) wls)).
eapply EcbMod.get_set_same.
rewrite EcbMod.map_get_set.
rewrite <- remove_wls_succ_eq.
auto.
Qed.

Lemma ex_imp_neq_nil:
forall wls: list tid,
(exists t, In t wls) -> wls <> nil.
Proof.
intros.
pure_auto.
subst.
simpl in *.
destruct H.
tryfalse.
Qed.

Lemma neq_nil_length_impl:
forall wls: list tid, wls <> nil -> (0 < length wls)%nat.
Proof.
induction wls; intros.
tryfalse.
simpl; auto with zarith.
Qed.

Lemma remove_tid_length_impl:
forall wls a, 
In a wls ->
(length (remove_tid a wls) <= (length wls - 1)%nat)%nat.
Proof.
induction wls.
simpl. auto.
simpl.
intros.
destruct (os_inv.beq_addrval a0 a) eqn: eq1.
eapply beq_tid_true_eq in eq1; subst.
assert (Hin: In a wls \/ ~(In a wls)) by tauto.
destruct Hin.
eapply IHwls in H0.
auto with zarith.
eapply remove_tid_nin_eq in H0.
rewrite H0. auto with zarith.
destruct H.
subst.
rewrite beq_tid_true in eq1; tryfalse.
assert (wls <> nil).
pure_auto.
subst. tryfalse.
eapply neq_nil_length_impl in H0.
eapply IHwls in H.
simpl.
auto with zarith.
Qed.

Lemma is_subl_nil_false:
forall subl, ~(is_subl subl nil).
Proof.
intros.
pure_auto.
funfold H.
simpl in *.
auto with zarith.
Qed.

Lemma remove_wls_nil_eq:
forall l, remove_wls l nil = nil.
Proof.
induction l; auto.
Qed.

Lemma remove_tid_split_succ:
forall l a b,
remove_tid a (b :: l) = remove_tid a (b :: nil) ++ remove_tid a l.
Proof.
induction l; intros.
simpl.
erewrite app_nil_r. auto.
rewrite IHl.
simpl.
destruct (os_inv.beq_addrval a0 b) eqn: eq1;
destruct (os_inv.beq_addrval a0 a) eqn: eq2;
simpl; auto.
Qed.

Lemma remove_tid_split:
forall l1 l2 a,
remove_tid a (l1 ++ l2) = remove_tid a l1 ++ remove_tid a l2.
Proof.
induction l1; intros.
simpl. auto.
change ((a :: l1) ++ l2) with (a :: (l1 ++ l2)).
rewrite remove_tid_split_succ with (l:= (l1 ++ l2)).
rewrite remove_tid_split_succ with (l:= l1).
rewrite IHl1.
rewrite app_assoc_reverse.
auto.
Qed.

Lemma remove_wls_split_succ:
forall l wls a,
remove_wls l (a :: wls) = remove_wls l (a :: nil) ++ remove_wls l wls.
Proof.
induction l; intros.
simpl. auto.
repeat try rewrite remove_wls_succ_eq.
rewrite IHl.
rewrite remove_tid_split.
auto.
Qed.

Lemma remove_wls_split:
forall wls1 wls2 l,
remove_wls l (wls1 ++ wls2) = remove_wls l wls1 ++ remove_wls l wls2.
Proof.
induction wls1; intros.
simpl.
rewrite remove_wls_nil_eq.
auto.
change ((a :: wls1) ++ wls2) with (a :: (wls1 ++ wls2)).
rewrite remove_wls_split_succ with (wls:= (wls1 ++ wls2)).
rewrite remove_wls_split_succ with (wls:= wls1).
rewrite IHwls1.
rewrite app_assoc_reverse.
auto.
Qed.

Lemma remove_wls_succ_len_le:
forall wls subwl a,
(length (remove_wls (a :: subwl) wls) <= length (remove_wls subwl wls))%nat.
Proof.
induction wls; intros.
simpl. auto.
rewrite remove_wls_split_succ with (wls := wls).
rewrite remove_wls_split_succ with (wls := wls).
do 2 rewrite app_length.
eapply Nat.add_le_mono; eauto.
simpl.
destruct (os_inv.beq_addrval a0 a ) eqn: eq1.
rewrite remove_wls_nil_eq.
simpl.
auto with zarith.
auto.
Qed.


Lemma remove_wls_length_imp:
forall wls subwl,
(length (remove_wls subwl wls) <= length wls)%nat.
Proof.
induction wls; induction subwl; intros.
simpl. auto.
rewrite remove_wls_nil_eq.
simpl. auto.
simpl. auto.
rewrite remove_wls_split_succ in *.
simpl remove_wls at 1.
destruct (os_inv.beq_addrval a0 a) eqn: eq1.
rewrite remove_wls_nil_eq.
rewrite app_nil_l.
lets Hlt: IHwls (a0 :: subwl).
assert (length wls <= length (a :: wls))%nat.
simpl; auto with zarith.
auto with zarith.
rewrite app_length in *.
eapply plus_le_reg_l with (p:= length(remove_wls subwl wls)).
assert (Nat.add (length (remove_wls subwl wls))
                 (Nat.add (length (remove_wls subwl (a :: nil))) (length (remove_wls (a0 :: subwl) wls))) =
              Nat.add (length (remove_wls (a0 :: subwl) wls))
                 (Nat.add (length (remove_wls subwl (a :: nil))) (length (remove_wls subwl wls)))).
auto with zarith.
rewrite H.
eapply Nat.add_le_mono; eauto.
apply remove_wls_succ_len_le.
Qed.

Lemma remove_wls_nin_imp:
forall subwl wls a,
In a wls ->
~(In a subwl) ->
In a (remove_wls subwl wls).
Proof.
induction subwl; intros.
simpl. auto.
rewrite not_in_cons in H0.
destruct H0.
rewrite remove_wls_succ_eq.
eapply in_neq_remove_in; eauto.
Qed.

Lemma remove_wls_length_imp':
forall subwl wls,
is_subl subwl wls ->
(length (remove_wls subwl wls) <= (length wls - length subwl)%nat)%nat.
Proof.
induction subwl.
simpl.
auto with zarith. 
intros.
lets Hsuc: is_subl_succ H.
funfold H.
lets Hcp: H1.
rewrite NoDup_cons_iff in Hcp.
destruct Hcp.
assert (Hin: In a wls).
eapply H; simpl; eauto.
assert (In a (remove_wls subwl wls)).
eapply remove_wls_nin_imp; eauto.
eapply remove_tid_length_impl in H5.
rewrite remove_wls_succ_eq.
eapply NPeano.Nat.le_trans; eauto.
eapply IHsubwl in Hsuc.
simpl length.
auto with zarith.
Qed.

Lemma length_lt_succ:
forall wls subl a,
In a (remove_wls subl wls) ->
is_subl subl wls ->
remove_wls (a :: subl) wls <> nil ->
(S(length subl) < length wls)%nat.
Proof.
induction wls; intros.
lets Hf: is_subl_nil_false subl.
tryfalse.
lets Hlen: is_subl_length_lt H0.
simpl length in *.
rewrite NPeano.Nat.lt_eq_cases in Hlen.
destruct Hlen; auto.
lets Hlen: remove_wls_length_imp' H0.
simpl length at 2 in Hlen.
rewrite <- H2 in Hlen.
assert ((S (length subl) - length subl)%nat = 1%nat) 
by (auto with zarith).
rewrite H3 in Hlen.
rewrite NPeano.Nat.le_1_r in Hlen.
lets Hlt: neq_nil_length_impl H1.
rewrite remove_wls_succ_eq in Hlt.
lets Hle: remove_tid_length_impl H.
destruct Hlen as [Hlen_eq | Hlen_eq];
rewrite Hlen_eq in *;
auto with zarith.
Qed.