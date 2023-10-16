
Require Import include_frm.
Require Import auxdef.
Require Import simulation.
Require Import base_tac.
Require Import step_prop.
Require Import join_prop.

Lemma hmstepstar_htsteps: 
  forall pc A spc sd aop O aop' O' ke ks cst t, 
    hmstepstar sd aop O aop' O' ->
    A = (spc, sd) -> 
      htsteps (pc, A) t
        (curs (hapi_code aop), (ke, ks)) cst O
        (curs (hapi_code aop'), (ke, ks)) cst O'.  
Proof.
  induction 1.
  - constructors. 
  - introv HA.
    lets IHH: IHspec_stepstar HA. clear IHspec_stepstar.
    constructors; eauto.
    eapply hapi_step; eauto.
    constructors; auto.
    rewrite HA. simpl.
    auto.
Qed.

Lemma absabt_tskabsabt:
  forall A pc aop OO ke ks cst t, 
    (exists OO', hmstepstar (snd A) aop OO (ABORT) OO') -> 
    tskabsabt (pc, A) (curs (hapi_code aop), (ke, ks)) cst OO t. 
Proof.
  introv Hex.
  unfold tskabsabt.
  destruct Hex as (OO' & Hhms).
  exists ke ks cst OO'. 
  destruct A.
  eapply hmstepstar_htsteps; eauto.
Qed.

Lemma htsteps_hpsteps: 
  forall Th Ch t hp Ch' cst cst' O O', 
    htsteps hp t Ch cst O Ch' cst' O' ->
    get O curtid = Some (oscurt t) ->
    get Th t = Some Ch ->
    hpsteps hp Th cst O (set Th t Ch') cst' O'. 
Proof.
  introv Hsps.
  generalize dependent Th.
  induction Hsps; intros.
  - asserts_rewrite (set Th t c = Th).
    apply get_set_same; auto.
    constructors. 
  - lets IHH0: IHHsps (set Th t c'').
    assert (H': get (set Th t c'') t = Some c'') by apply get_set_eq.
    lets Htideq: htstep_tidsame H.
    assert (HtidO'': get O'' curtid = Some (oscurt t)).
    { unfold tidsame in Htideq. rewrite <- Htideq. auto. }
    lets IHH: IHH0 HtidO'' H'; auto.
    clear IHH0.
    rewrite <- set_set_eq in IHH.
    eapply hpsteps_S; eauto.
    eapply hp_step; eauto.
  - lets IHH0: IHHsps (set Th t c'').
    assert (H': get (set Th t c'') t = Some c'') by apply get_set_eq.
    assert (HeqO: O = O'') by (inverts H; auto).
    lets IHH: IHH0 H'; auto. clear IHH0.
    subst O''; auto.
    rewrite <- set_set_eq in IHH.
    subst O''.
    eapply hpsteps_S_ev; eauto.
    assert (Heqcst: cst = cst'') by (inverts H; auto).
    subst cst''.
    eapply hpt_stepev; eauto.
Qed.
    
Lemma tskabsabt_prgabsabt: 
  forall Th hp t Ch cst O, 
    get Th t = Some Ch -> 
    get O curtid = Some (oscurt t) -> 
    tskabsabt hp Ch cst O t -> 
    prgabsabt hp Th cst O. 
Proof.
  introv HTht HOctid Htskabt.
  unfold tskabsabt in Htskabt.
  unfold prgabsabt.
  destruct Htskabt as (ke' & ks' & cst' & O' & Htsps).
  exists (set Th t (curs (hapi_code (ABORT)), (ke', ks'))).
  exists cst'. exists O'.
  split.
  eapply htsteps_hpsteps; eauto.
  unfold absabt. exists t ke' ks'.
  rewrite get_set_eq; auto.
Qed.

Lemma htsteps_local: 
  forall (p : hprog) t
         (C : code) (cst : clientst) (O : osabst) (C' : code) (cst' : clientst)
         (O' OO Of : osabst),
    htsteps p t C cst O C' cst' O' ->
    join O Of OO ->
    exists OO', htsteps p t C cst OO C' cst' OO' /\ join O' Of OO'. 
Proof.
  introv Hsps. generalize OO.
  induction Hsps.
  - introv Hjo. exists OO0.
    split; auto. constructors; auto.
  - intros.
    lets H'': htstep_O_local H H0.
    destruct H'' as (OO' & Hsps' & Hjo').
    apply IHHsps in Hjo'.
    destruct Hjo' as (OO'0 & Hsps'' & Hjo'').
    exists OO'0.
    split; auto.
    eapply htsteps_S; eauto.
  - assert (O'' = O) by (inverts H; auto).
    subst O''.
    introv Hjo.
    lets Hsp': IHHsps Hjo.
    assert (Hspev: htstepev p t c cst OO0 c'' cst'' OO0 ev).
    { inverts keep H. constructors; eauto. }
    destruct Hsp' as (OO' & Hsp'' & Hjo'').
    exists OO'. split; auto.
    eapply htsteps_S_ev; eauto.
Qed.      


  (* Lemma htsteps_hpsteps:  *)
  (*   forall Th Ch t hp Ch' cst cst' O O',  *)
  (*     htsteps hp t Ch cst O Ch' cst' O' -> *)
  (*     get O curtid = Some (oscurt t) -> *)
  (*     get Th t = Some Ch -> *)
  (*     exists Th',  *)
  (*       hpsteps hp Th cst O Th' cst' O' /\ *)
  (*         Th' = set Th t Ch'. *)
  (* Proof. *)
  (*   introv Hsps. *)
  (*   generalize dependent Th. *)
  (*   induction Hsps; intros. *)
  (*   - exists Th.  *)
  (*     split. *)
  (*     constructors.  *)
  (*     symmetry. apply get_set_same; auto. *)
  (*   - lets IHH0: IHHsps (set Th t c''). *)
  (*     assert (H': get (set Th t c'') t = Some c'') by apply get_set_eq. *)
  (*     lets Htideq: htstep_tidsame H. *)
  (*     assert (HtidO'': get O'' curtid = Some (oscurt t)). *)
  (*     { unfold tidsame in Htideq. rewrite <- Htideq. auto. } *)
  (*     lets IHH: IHH0 HtidO'' H'; auto. *)
  (*     clear IHH0. *)
  (*     destruct IHH as (Th' & Hsps' & HTh'). *)
  (*     exists Th'. *)
  (*     rewrite <- set_set_eq in HTh'. *)
  (*     split; auto. *)
  (*     eapply hpsteps_S; eauto. *)
  (*     eapply hp_step; eauto. *)
  (*   - lets IHH0: IHHsps (set Th t c''). *)
  (*     assert (H': get (set Th t c'') t = Some c'') by apply get_set_eq. *)
  (*     assert (HeqO: O = O'') by (inverts H; auto). *)
  (*     lets IHH: IHH0 H'; auto. clear IHH0. *)
  (*     subst O''; auto. *)
  (*     destruct IHH as (Th' & Hsps' & HTh'). *)
  (*     exists Th'. *)
  (*     rewrite <- set_set_eq in HTh'. *)
  (*     split; auto. *)
  (*     subst O''. *)
  (*     eapply hpsteps_S_ev; eauto. *)
  (*     assert (Heqcst: cst = cst'') by (inverts H; auto). *)
  (*     subst cst''. *)
  (*     eapply hpt_stepev; eauto. *)
  (* Qed. *)
