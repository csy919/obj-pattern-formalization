Require Import include_frm.
Require Import auxdef.
Require Import simulation.
Require Import base_tac.

Lemma  hpstepstar_trans : 
  forall hp ht cs O ht' cs' O' ht'' cs'' O'', 
    hpstepstar hp ht cs O ht'' cs'' O'' -> 
    hpstepstar hp ht'' cs'' O'' ht' cs' O' -> 
    hpstepstar hp ht cs O ht' cs' O'.
Proof.
  introv Hstpstr.
  inductions Hstpstr.
  - auto.
  - introv Hss.
    apply IHHstpstr in Hss.
    constructors; eauto.
Qed. 

Lemma hpstepstar_hpsteps:
  forall p T cs O T' cs' O' T'' cs'' O'', 
    hpstepstar p T cs O T'' cs'' O'' ->
    hpsteps p  T'' cs'' O'' T' cs' O' ->
    hpsteps p T cs O T' cs' O'. 
Proof.
  induction 1. 
  - auto.
  - introv Hstps.
    apply IHhpstepstar in Hstps.
    constructors; eauto.
Qed.
  
Lemma prgnabt_hpstepstar:
  forall hp ht cs O ht' cs' O',
    ~ prgabsabt hp ht cs O ->
    hpstepstar hp ht cs O ht' cs' O' ->
    ~ prgabsabt hp ht' cs' O'.
Proof.
  introv Hnabt Hstpstr.
  introv Hnabt'.
  apply Hnabt. clear Hnabt.
  unfold prgabsabt in *.
  destruct Hnabt' as (T'' & cs'' & O'' & Hsp & Habt).
  exists T'' cs'' O''.
  split; auto.
  eapply hpstepstar_hpsteps; eauto.
Qed.   

(* Lemma prgnabt_hpstepstar: *)
(*   forall hp ht cs O ht' cs' O',  *)
(*     ~ prgabsabt hp ht cs O -> *)
(*     hpstepstar hp ht cs O ht' cs' O' ->  *)
(*     ~ prgabsabt hp ht' cs' O'.  *)
(* Proof. *)
(*   introv Hnabt Hstpstr. *)
(*   introv Hnabt'. *)
(*   apply Hnabt. clear Hnabt. *)
(*   unfold prgabsabt in *. *)
(*   destruct Hnabt' as (T' & cst' &  O'0 & Hsp & Haabt). *)
(*   exists T' cst' O'0. *)
(*   split; auto. *)
(*   eapply hpstepstar_trans; eauto. *)
(* Qed.  *)

Lemma hpstepevstar_hpsteps:
  forall p T cs O T' cs' O' T'' cs'' O'' ev, 
    hpstepevstar p T cs O T'' cs'' O'' ev ->
    hpsteps p  T'' cs'' O'' T' cs' O' ->
    hpsteps p T cs O T' cs' O'.
Proof.
  introv Hsp.
  inverts Hsp.
  introv Hsps.
  lets Hsps': hpstepstar_hpsteps H1 Hsps.
  lets Hsps'': hpsteps_S_ev H0 Hsps'.
  clear H0 H1 Hsps Hsps'.
  eapply hpstepstar_hpsteps; eauto.
Qed.   

Lemma prgnabt_hpstepevstar:
  forall hp ht cs O ht' cs' O' ev,
    ~ prgabsabt hp ht cs O ->
    hpstepevstar hp ht cs O ht' cs' O' ev ->
    ~ prgabsabt hp ht' cs' O'.
Proof.
  introv Hnabt Hstpstr.
  introv Hnabt'.
  apply Hnabt. clear Hnabt.
  unfold prgabsabt in *.
  destruct Hnabt' as (T'' & cs'' & O'' & Hsp & Habt).  
  exists T'' cs'' O''.
  split; auto.
  eapply hpstepevstar_hpsteps; eauto.
Qed.
