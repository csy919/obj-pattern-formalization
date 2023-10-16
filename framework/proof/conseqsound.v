Require Import sound_include.

Lemma conseq_rule_sound_aux : 
  forall p  sd  I r ri q q' li t,
    (q ==> q') ->
    forall  C o aop O, 
      MethSimMod p sd C o aop O li I  r ri (lift q) t ->
      MethSimMod p sd C o aop O li I  r ri (lift q') t .
Proof.
  introv Himp.
  cofix Hcofix.
  introv Hsim.                               
  inverts Hsim.
  constructors;try auto.
  (* introv Hfcall Hinv Hjm1 Hjm2 Hlstop. *)
  introv Hfcall Hinv Hjm1 Hjm2 Hlstop Hnabt.
  lets Hex : H Hfcall Hinv Hjm1.  
  (* lets Hex' : Hex Hjm2 Hlstop. *)
  lets Hex': Hex Hjm2 Hlstop Hnabt.
  simp join.
  do 6 eexists; splits; eauto.
  (* introv Hc Hmdisj Hinv Hdisj. *)
  introv Hc Hmdisj Hinv Hdisj Hnabt. 
  (* lets Hex : H0 Hc Hmdisj Hinv Hdisj. *)
  lets Hex : H0 Hc Hmdisj Hinv Hdisj Hnabt. 
  simp join.
  do 12 eexists; splits; eauto.
  splits; eauto.
  introv Hsa.
  splits; eauto.
  eapply H18; eauto.
  introv Hj1 Hj2 Heq.
  eapply Hcofix.
  eapply H18; eauto.
  (* introv Hc  Hinv Hjm1 Hjm2. *)
  introv Hc Hinv Hjm1 Hjm2 Hnabt. 
  (* lets Hex : H1 Hc   Hinv Hjm1 Hjm2  .  *)
  lets Hex : H1 Hc   Hinv Hjm1 Hjm2  Hnabt.  
  simp join.
  do 9 eexists; splits; eauto.
  splits; eauto.
  destruct H17; [simp join; left;split; eauto | right; eauto]. 
 
  (* introv Hc Hdis Hinv Hdd. *)
  (* lets Hsk : H2 Hc Hdis Hinv Hdd. *)
  introv Hc Hdis Hinv Hdd Hnabt.
  lets Hsk : H2 Hc Hdis Hinv Hdd Hnabt. 
  simp join.
  do 4 eexists; splits; eauto.
  
  (* introv Hc  Hinv Hjm1 Hjm2. *)
  (* lets Hex : H7 Hc   Hinv Hjm1 Hjm2  .  *)
  introv Hc Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H7 Hc   Hinv Hjm1 Hjm2  Hnabt.  
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.
  (* introv Hc  Hinv Hjm1 Hjm2. *)
  (* lets Hex : H8 Hc   Hinv Hjm1 Hjm2  .  *)
  introv Hc Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H8 Hc   Hinv Hjm1 Hjm2  Hnabt.  
  simp join.
  do 5 eexists; splits; eauto.
  destruct H12; simp join.
  left; do 3 eexists; splits; eauto.
  right; do 3 eexists;splits; eauto.

  (* apply meth_sim_abort_mod; auto. *)
  (* (* lxm: added due to consideration of abortion due to *)
  (*     assertion failures on the abstract level *)  *)

Qed.

Lemma conseq_rule_sound :
  forall Spec sd I r ri p' p q q' s li t, 
    (p' ==>  p) ->  (q ==> q') ->
    RuleSem Spec sd li I r ri p s q  t ->
    RuleSem  Spec sd li  I r ri p' s q' t.
Proof.
  introv Himp1 Himp2 Hsim.
  introv .
  unfold RuleSem in *.
  introv Hsat.
  lets (Hsat1 & Hsat2) : Hsat.
  lets Hsatp : Himp1 Hsat1.
  assert ((o, O, aop) |= p /\ satp o O (CurLINV li t)) by (split; auto).
  lets Hsim1 : Hsim  H. 
  eapply  conseq_rule_sound_aux; eauto.
Qed.


Lemma conseq_rule_r_sound_aux :
  forall p sd I r ri ri' q r' li t, 
    (
      forall v,  r v==> r' v
    ) ->
    ri ==> ri' ->
    forall  C o aop O, 
      MethSimMod p sd C o aop O li I  r ri q t ->
      MethSimMod p sd C o aop O li I  r' ri' q t .
Proof.
  introv Himp1 Himp2.
  cofix Hcofix.
  introv Hsim.                               
  inverts Hsim.
  constructors;try auto.
  (* introv Hfcall Hinv Hjm1 Hjm2 Hlstop. *)
  introv Hfcall Hinv Hjm1 Hjm2 Hlstop Hnabt.
  lets Hex : H Hfcall Hinv Hjm1.  
  (* lets Hex' : Hex Hjm2 Hlstop. *)
  lets Hex' : Hex Hjm2 Hlstop Hnabt.
  simp join.
  do 6 eexists; splits; eauto.
  (* introv Hc Hmdisj Hinv Hdisj. *)
  (* lets Hex : H0 Hc Hmdisj Hinv Hdisj. *)
  introv Hc Hmdisj Hinv Hdisj Hnabt. 
  lets Hex : H0 Hc Hmdisj Hinv Hdisj Hnabt. 
  simp join.
  do 12 eexists; splits; eauto.
  splits; eauto.
  introv Hsa.
  splits; eauto.
  eapply H18; eauto.
  introv Hj1 Hj2 Heq.
  eapply Hcofix.
  eapply H18; eauto.
  (* introv Hc  Hinv Hjm1 Hjm2. *)
  (* lets Hex : H1 Hc   Hinv Hjm1 Hjm2  .  *)
  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H1 Hc   Hinv Hjm1 Hjm2 Hnabt.
  simp join.
  do 9 eexists; splits; eauto.
  splits; eauto.
  destruct H17; [simp join; left;split; eauto | right; eauto]. 

  (* introv Hc Hcal Hint Hdis Hinv Hdd. *)
  (* lets Hsk : H3 Hc Hdis Hinv Hdd; eauto. *)
  introv Hc Hcal Hint Hdis Hinv Hdd Hnabt.
  lets Hsk : H3 Hc Hdis Hinv Hdd Hnabt; eauto.
  simp join.
  do 4 eexists; splits; eauto.
  
  (* introv Hc Hcal Hint Hdis Hinv Hdd. *)
  (* lets Hsk : H4 Hc Hdis Hinv Hdd; eauto. *)
  introv Hc Hcal Hint Hdis Hinv Hdd Hnabt.
  lets Hsk : H4 Hc Hdis Hinv Hdd Hnabt; eauto.
  simp join.
  do 4 eexists; splits; eauto.

  (* introv Hc Hcal Hint Hdis Hinv Hdd. *)
  (* lets Hsk : H5 Hc Hdis Hinv Hdd; eauto. *)
  introv Hc Hcal Hint Hdis Hinv Hdd Hnabt.
  lets Hsk : H5 Hc Hdis Hinv Hdd Hnabt; eauto.
  simp join.
  do 4 eexists; splits; eauto.

  (* introv Hc  Hinv Hjm1 Hjm2. *)
  (* lets Hex : H7 Hc   Hinv Hjm1 Hjm2  .  *)
  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H7 Hc   Hinv Hjm1 Hjm2 Hnabt.
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.
  (* introv Hc  Hinv Hjm1 Hjm2. *)
  (* lets Hex : H8 Hc   Hinv Hjm1 Hjm2  .  *)
  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H8 Hc   Hinv Hjm1 Hjm2 Hnabt. 
  simp join.
  do 5 eexists; splits; eauto.
  destruct H12; simp join.
  left; do 3 eexists; splits; eauto.
  right; do 3 eexists;splits; eauto.

  (* apply meth_sim_abort_mod; auto. *)
  (* (* lxm: added due to consideration of abortion due to *)
  (*     assertion failures on the abstract level *) *)
  
Qed.

Lemma conseq_rule_r_sound : 
  forall  Spec sd I r r' ri ri' p q s li t, 
    (forall v,r v ==> r' v) ->
    ri ==> ri' ->
    RuleSem Spec sd  li I  r ri p s q  t->
    RuleSem  Spec sd li I  r' ri' p s q t.
Proof.
  introv Himp Himp' Hsim.
  introv .
  unfold RuleSem in *.
  introv Hsat.
  lets Hsim1 : Hsim  Hsat. 
  eapply  conseq_rule_r_sound_aux; eauto.
Qed.


Lemma absconseq_rule_sound_aux : 
  forall p  sd I r ri q q' li t,
    (absimp' sd li q q' t) ->
    forall  C o aop O, 
      MethSimMod p sd C o aop O li I  r ri (lift q) t ->
      MethSimMod p sd C o aop O li I  r ri (lift q') t .
Proof.
  introv Himp.
  cofix Hcofix.
  introv Hsim.                               
  inverts Hsim.
  constructors;try auto.
  (* introv Hfcall Hinv Hjm1 Hjm2 Hlstop. *)
  introv Hfcall Hinv Hjm1 Hjm2 Hlstop Hnabt. 
  lets Hex : H Hfcall Hinv Hjm1.  
  (* lets Hex' : Hex Hjm2 Hlstop. *)
  lets Hex' : Hex Hjm2 Hlstop Hnabt.
  simp join.
  do 6 eexists; splits; eauto.

  (* introv Hc Hmdisj Hinv Hdisj. *)
  (* lets Hex : H0 Hc Hmdisj Hinv Hdisj. *)
  introv Hc Hmdisj Hinv Hdisj Hnabt. 
  lets Hex : H0 Hc Hmdisj Hinv Hdisj Hnabt. 
  simp join.
  do 12 eexists; splits; eauto.
  splits; eauto.
  introv Hsa.
  splits; eauto.
  eapply H18; eauto.
  introv Hj1 Hj2 Heq.
  eapply Hcofix.
  eapply H18; eauto.

  (* introv Hc  Hinv Hjm1 Hjm2. *)
  (* lets Hex : H1 Hc  Hinv Hjm1 Hjm2  .  *)
  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H1 Hc  Hinv Hjm1 Hjm2 Hnabt. 
  simp join.
  do 9 eexists; splits; eauto.
  splits; eauto.
  destruct H17; [simp join; left;split; eauto | right; eauto]. 

  (* introv Hc Hdis Hinv Hdd. *)
  (* lets Hsk : H2 Hc Hdis Hinv Hdd. *)
  introv Hc Hdis Hinv Hdd Hnabt.
  lets Hsk : H2 Hc Hdis Hinv Hdd Hnabt. 
  simp join.
  assert ((o, x1, x) |= lift q v/\  satp o x1 (CurLINV li t)) by (split;auto).
  lets Hss : Himp H14.
  lets Htt : Hss H10.
  simp join.
  lets Hspp : hmstepstar_trans H9 H16.  
  exists x4 x5 x3 x2.
  splits; eauto.
  
  (* introv Hc  Hinv Hjm1 Hjm2. *)
  (* lets Hex : H7 Hc   Hinv Hjm1 Hjm2  .  *)
  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H7 Hc   Hinv Hjm1 Hjm2 Hnabt.   
  simp join.
  do 14 eexists; splits; eauto.
  splits; eauto.
  (* introv Hc  Hinv Hjm1 Hjm2. *)
  (* lets Hex : H8 Hc   Hinv Hjm1 Hjm2  .  *)
  introv Hc  Hinv Hjm1 Hjm2 Hnabt.
  lets Hex : H8 Hc   Hinv Hjm1 Hjm2 Hnabt. 
  simp join.
  do 5 eexists; splits; eauto.
  destruct H12; simp join.
  left; do 3 eexists; splits; eauto.
  right; do 3 eexists;splits; eauto.

  (* apply meth_sim_abort_mod; auto. *)
  (* (* lxm: added due to consideration of abortion due to *)
  (*     assertion failures on the abstract level *)  *)

Qed.

(* cannot be established if the abortion case is added into the definition of task simulation
    in simulation.v *) 
Lemma abscsq_rule_sound :  
  forall   Spec sd I r ri p' p q q' s li t , 
    absinferfull sd li p' p t -> 
    absinferfull sd li q q' t ->
    RuleSem Spec sd  li I r ri p s q t  ->
    RuleSem  Spec sd  li I r ri p' s q' t.
Proof.
  introv  Himp1 Himp2 Hsim.
  apply absinfersound in Himp1.
  apply absinfersound in Himp2.
  apply absimp_eq_absimp' in Himp1.
  apply absimp_eq_absimp'  in Himp2.
  introv .
  unfold RuleSem in *.
  introv  Hsat.
  unfold absimp' in Himp1.
  lets Hsatt :  Himp1  Hsat.
  constructors; try auto.
  (* introv Hfcall Hinv Hjm1 Hjm2 Hstep. *)
  introv Hfcall Hinv Hjm1 Hjm2 Hstep Hnabt. 
  lets Hres : Hsatt  Hjm2.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm. 
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  (* lets Hsm : H Hfcall Hinv Hjm1 Hdsjj  Hstep.  *)
  lets Hsm0 : H Hfcall Hinv Hjm1 Hdsjj  Hstep.
  lets Hsm : Hsm0 Hnex. clear Hsm0.
  simp join.
  lets Hks : hmstepstar_trans Hstar H9.
  exists x x0 x1 x2 x3 x4.  
  splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.

  (* introv Hc Hmdisj Hinv Hdisj. *)
  introv Hc Hmdisj Hinv Hdisj Hnabt. 
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  (* lets Hress : H0 Hc Hmdisj Hinv Hdsjj. *)
  lets Hress0 : H0 Hc Hmdisj Hinv Hdsjj. 
  lets Hress : Hress0 Hnex. clear Hress0.
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H9.
  do 12 eexists; 
    splits; eauto.
  splits; auto.
  introv Henv.  
  splits.
  eapply H18; eauto.
  introv Hvv Hvvv Hdss.
  eapply absconseq_rule_sound_aux ; eauto.
  eapply H18; eauto.

  (* introv Hc Hmdisj Hinv Hdisj. *)
  introv Hc Hmdisj Hinv Hdisj Hnabt.
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  (* lets Hress : H1 Hc Hmdisj Hinv Hdsjj. *)
  lets Hress : H1 Hc Hmdisj Hinv Hdsjj Hnex. 
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H10.  
  clear Hstar H10.
  do 9 eexists; splits; eauto.
  splits; eauto.
  destruct H17; [simp join; left;split; eauto | right; eauto]. 
 
  introv  Hs Hjmm Hswin.
  eapply absconseq_rule_sound_aux ; eauto.

  (* introv Hc Hmdisj Hinv Hdisj. *)
  introv Hc Hmdisj Hinv Hdisj Hnabt.  
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }  
  (* lets Hsk : H2 Hc Hmdisj Hinv Hdsjj. *)
  lets Hsk : H2 Hc Hmdisj Hinv Hdsjj Hnex.  
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H9.  
  assert ((o, x1, x) |= lift q v /\ satp o x1 (CurLINV li t)) by (split; auto).
  lets Hds : Himp2 H18 H10.
  simp join.
  lets Hsbt : hmstepstar_trans  Hstt  H20.  
  do 4 eexists; splits; eauto.

  (* introv Hc Hcal Hint Hmdisj Hinv Hdisj. *)
  introv Hc Hcal Hint Hmdisj Hinv Hdisj Hnabt.  
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }  
  (* lets Hsk : H3 Hc Hmdisj Hinv Hdsjj; eauto. *)
  lets Hsk : H3 Hc Hmdisj Hinv Hdsjj Hnex; eauto. 
  simp join.
  lets Hsbt : hmstepstar_trans  Hstar  H9.  
  do 4 eexists; splits; eauto.

  (* introv Hc Hcal Hint Hmdisj Hinv Hdisj. *)
  introv Hc Hcal Hint Hmdisj Hinv Hdisj Hnabt.  
  lets Hres : Hsatt  Hdisj. 
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }    
  (* lets Hsk : H4 Hc Hmdisj Hinv Hdsjj; eauto. *)
  lets Hsk : H4 Hc Hmdisj Hinv Hdsjj Hnex; eauto. 
  simp join.
  lets Hsbt : hmstepstar_trans  Hstar  H9.  
  do 4 eexists; splits; eauto.

  (* introv Hc Hcal Hint Hmdisj Hinv Hdisj. *)
  introv Hc Hcal Hint Hmdisj Hinv Hdisj Hnabt.   
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  lets Hsk : H5 Hc Hmdisj Hinv Hdsjj Hnex; eauto.  
  (* lets Hsk : H5 Hc Hmdisj Hinv Hdsjj; eauto. *)
  simp join.
  lets Hsbt : hmstepstar_trans  Hstar  H9.  
  do 4 eexists; splits; eauto.

  (* introv Hnot  Hinv Hjon Hdisj. *)
  introv Hnot  Hinv Hjon Hdisj Hjoin Hnabt. 
  unfolds in Hdisj.
  destruct Hdisj as (OO0 & Hdisj).
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (disjoint O' Os) as Hds.
  unfolds.
  eauto.
  (* lets Hree : H6 Hnot Hinv Hjon Hds; eauto. *)
  lets Hree0 : H6 Hnot Hinv Hjon Hds Hdsjj.
  (* Search (join _ _ _ -> join _ _ _ -> _ = _). *)
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0.
    lets HOOeq: join_lib.join_unique Hdisj Hjoin.
    rewrite <- HOOeq in *.  
    eapply hmstepstar_trans; eauto.
  }
  lets Hree: Hree0 Hnex.
  eauto. (* added due to change in simulation *) 

  (* introv Hc Hmdisj Hinv Hdisj. *)
  introv Hc Hmdisj Hinv Hdisj Hnabt.  
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  (* lets Hress : H7 Hc Hmdisj Hinv Hdsjj. *)
  lets Hress : H7 Hc Hmdisj Hinv Hdsjj Hnex.  
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H13.  
  eexists.
  exists x0 x1 x2.
  do 10 eexists; splits; eauto.
  splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.

  (* introv Hc Hmdisj Hinv Hdisj. *)
  introv Hc Hmdisj Hinv Hdisj Hnabt.  
  lets Hres : Hsatt  Hdisj.
  destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp).
  lets Hsm : Hsim  Hsp.
  inverts Hsm.
  assert (Hnex: ~ (exists OO'0, hmstepstar sd gamma' OO' (ABORT) OO'0)).
  {
    introv Hex. apply Hnabt. destruct Hex as (OO'0 & Hex_OO').
    exists OO'0. eapply hmstepstar_trans; eauto.
  }
  (* lets Hress : H8 Hc Hmdisj Hinv Hdsjj. *)
  lets Hress : H8 Hc Hmdisj Hinv Hdsjj Hnex. 
  simp join.
  lets Hstt : hmstepstar_trans  Hstar H11.
  clear Hstar H11.
  eexists.
  exists x0 x1 x2.
  exists x3.
  splits; eauto.
  destruct H12; simp join.
  left.
  exists x x4 x5.
  splits; eauto.
  eapply absconseq_rule_sound_aux ; eauto.
  right.
  exists x x4 x5.
  splits; eauto.
  introv Hs1 Hj1 Hj2.
  eapply absconseq_rule_sound_aux ; eauto.
Qed.   


(* Proof. *)
(*   introv  Himp1 Himp2 Hsim. *)
(*   apply absinfersound in Himp1. *)
(*   apply absinfersound in Himp2. *)
(*   (* apply absimp_eq_absimp' in Himp1. *) *)
(*   (* apply absimp_eq_absimp'  in Himp2. *) *)
(*   introv . *)
(*   unfold RuleSem in *. *)
(*   introv  Hsat. *)
(*   assert (Himp10 := Himp1). *)
(*   assert (Himp20 := Himp2). *)
(*   unfold absimplication in Himp10.  *)
(*   (* unfold absimp' in Himp1. *) *)
(*   (* lets Hsatt :  Himp1  Hsat. *) *)
(*   lets Hsatt : Himp10 Hsat.  *)
(*   destruct Hsatt as (O' & gamma' & Hstar & Hsp). *)
(*   lets Hsm : Hsim  Hsp. *)
(*   inverts Hsm. *)
  
(*   2: { *)
(*     inverts H.   *)
(*     lets Hmsteps: hmstepstar_trans Hstar H0. *)
(*     apply meth_sim_abort_mod. eexists; eauto. *)
(*   } *)

(*   apply meth_sim_mod. *)
(*   introv Hfcall Hinv Hjm1 Hjm2 Hstep. *)
  
(*   lets Hres : Hsatt  Hjm2. *)
(*   destruct Hres as (O'0 & gamma'0 & OO'0 &Hdsjj0 &Hstar0 & Hsp0). *)
(*   lets Hsm : Hsim  Hsp0. *)
(*   inverts Hsm. *)
(*   lets Hsm : H Hfcall Hinv Hjm1 Hdsjj0  Hstep.  *)
(*   simp join. *)
(*   lets Hks : hmstepstar_trans Hstar H10. *)
(*   exists x x0 x1 x2 x3 x4.   *)
(*   splits; eauto. *)
(*   eapply absconseq_rule_sound_aux ; eauto. *)

  
(*   (* assert (H_cases: *) *)
(*   (*          ~(exists O'', spec_stepstar sd gamma' O' spec_abort O'') \/  *) *)
(*   (*            (exists O'', spec_stepstar sd gamma' O' spec_abort O'')). *) *)
(*   (* {  apply Classical_Prop.imply_to_or; auto. } *) *)
(*   (* destruct H_cases. *) *)

(*   (* Search (spec_stepstar _ _ _ _ _). *) *)
(*   (* Search (join _ _ _). *) *)
(*   (* apply map_join_comm in Hdsjj. *) *)
(*   (* inverts H0.   *) *)
(*   (* lets Hmstep: spec_stepstar_locality H1 Hdsjj. *) *)
(*   (* inversion Hmstep as [O2 [Hmstep2 Hjoin]]. *) *)
(*   (* lets Hcontra: hmstepstar_trans Hstar Hmstep2. *) *)
(*   (* exfalso. apply H. *) *)
  
  
  
(*   (* assert (H_cases: *) *)
(*   (*          ~(exists O', spec_stepstar sd x x3 spec_abort O') \/  *) *)
(*   (*            (exists O', spec_stepstar sd x x3 spec_abort O')). *) *)
(*   (* {  apply Classical_Prop.imply_to_or; auto. } *) *)
(*   (* destruct H_cases.  *) *)
(*   (* eapply absconseq_rule_sound_aux ; eauto.  *) *)
(*   (* apply meth_sim_abort_mod; auto. *) *)

(*   (* inverts H. *) *)
(*   (* exists gamma'. eexists OO'. eexists o. eexists Ms. exists O. exists Os. *) *)
(*   (* split. auto. *) *)
(*   (* split.  *) *)

(*   introv Hc Hmdisj Hinv Hdisj. *)
(*   lets Hres : Hsatt  Hdisj. *)
(*   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp). *)
(*   lets Hsm : Hsim  Hsp. *)
(*   inverts Hsm. *)
(*   lets Hress : H0 Hc Hmdisj Hinv Hdsjj. *)
(*   simp join. *)
(*   lets Hstt : hmstepstar_trans  Hstar H9. *)
(*   do 12 eexists;  *)
(*     splits; eauto. *)
(*   splits; auto. *)
(*   introv Henv.   *)
(*   splits. *)
(*   eapply H18; eauto. *)
(*   introv Hvv Hvvv Hdss. *)
(*   eapply absconseq_rule_sound_aux ; eauto. *)
(*   eapply H18; eauto. *)

(*   introv Hc Hmdisj Hinv Hdisj. *)
(*   lets Hres : Hsatt  Hdisj. *)
(*   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp). *)
(*   lets Hsm : Hsim  Hsp. *)
(*   inverts Hsm. *)
(*   lets Hress : H1 Hc Hmdisj Hinv Hdsjj. *)
(*   simp join. *)
(*   lets Hstt : hmstepstar_trans  Hstar H10.   *)
(*   clear Hstar H10. *)
(*   do 9 eexists; splits; eauto. *)
(*   splits; eauto. *)
(*   destruct H17; [simp join; left;split; eauto | right; eauto].  *)
 
(*   introv  Hs Hjmm Hswin. *)
(*   eapply absconseq_rule_sound_aux ; eauto. *)

(*   introv Hc Hmdisj Hinv Hdisj. *)
(*   lets Hres : Hsatt  Hdisj. *)
(*   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp). *)
(*   lets Hsm : Hsim  Hsp. *)
(*   inverts Hsm. *)
(*   lets Hsk : H2 Hc Hmdisj Hinv Hdsjj. *)
(*   simp join. *)
(*   lets Hstt : hmstepstar_trans  Hstar H9.   *)
(*   assert ((o, x1, x) |= lift q v /\ satp o x1 (CurLINV li t)) by (split; auto). *)
(*   lets Hds : Himp2 H18 H10. *)
(*   simp join. *)
(*   lets Hsbt : hmstepstar_trans  Hstt  H20.   *)
(*   do 4 eexists; splits; eauto. *)

(*    introv Hc Hcal Hint Hmdisj Hinv Hdisj. *)
(*    lets Hres : Hsatt  Hdisj. *)
(*   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp). *)
(*   lets Hsm : Hsim  Hsp. *)
(*   inverts Hsm. *)
(*   lets Hsk : H3 Hc Hmdisj Hinv Hdsjj; eauto. *)
(*   simp join. *)
(*   lets Hsbt : hmstepstar_trans  Hstar  H9.   *)
(*   do 4 eexists; splits; eauto. *)

(*    introv Hc Hcal Hint Hmdisj Hinv Hdisj. *)
(*    lets Hres : Hsatt  Hdisj. *)
(*   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp). *)
(*   lets Hsm : Hsim  Hsp. *)
(*   inverts Hsm. *)
(*   lets Hsk : H4 Hc Hmdisj Hinv Hdsjj; eauto. *)
(*   simp join. *)
(*   lets Hsbt : hmstepstar_trans  Hstar  H9.   *)
(*   do 4 eexists; splits; eauto. *)

(*   introv Hc Hcal Hint Hmdisj Hinv Hdisj. *)
(*   lets Hres : Hsatt  Hdisj. *)
(*   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp). *)
(*   lets Hsm : Hsim  Hsp. *)
(*   inverts Hsm. *)
(*   lets Hsk : H5 Hc Hmdisj Hinv Hdsjj; eauto. *)
(*   simp join. *)
(*   lets Hsbt : hmstepstar_trans  Hstar  H9.   *)
(*   do 4 eexists; splits; eauto. *)

(*   introv Hnot  Hinv Hjon Hdisj. *)
(*   unfolds in Hdisj. *)
(*   destruct Hdisj as (OO & Hdisj). *)
(*   lets Hres : Hsatt  Hdisj. *)
(*   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp). *)
(*   lets Hsm : Hsim  Hsp. *)
(*   inverts Hsm. *)
(*   assert (disjoint O' Os) as Hds. *)
(*   unfolds. *)
(*   eauto. *)
(*   lets Hree : H6 Hnot Hinv Hjon Hds; eauto. *)

(*   introv Hc Hmdisj Hinv Hdisj. *)
(*   lets Hres : Hsatt  Hdisj. *)
(*   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp). *)
(*   lets Hsm : Hsim  Hsp. *)
(*   inverts Hsm. *)
(*   lets Hress : H7 Hc Hmdisj Hinv Hdsjj. *)
(*   simp join. *)
(*   lets Hstt : hmstepstar_trans  Hstar H13.   *)
(*   eexists. *)
(*   exists x0 x1 x2. *)
(*   do 10 eexists; splits; eauto. *)
(*   splits; eauto. *)
(*   eapply absconseq_rule_sound_aux ; eauto. *)

(*   introv Hc Hmdisj Hinv Hdisj. *)
(*   lets Hres : Hsatt  Hdisj. *)
(*   destruct Hres as (O' & gamma' &  OO' &Hdsjj &Hstar & Hsp). *)
(*   lets Hsm : Hsim  Hsp. *)
(*   inverts Hsm. *)
(*   lets Hress : H8 Hc Hmdisj Hinv Hdsjj. *)
(*   simp join. *)
(*   lets Hstt : hmstepstar_trans  Hstar H11. *)
(*   clear Hstar H11. *)
(*   eexists. *)
(*   exists x0 x1 x2. *)
(*   exists x3. *)
(*   splits; eauto. *)
(*   destruct H12; simp join. *)
(*   left. *)
(*   exists x x4 x5. *)
(*   splits; eauto. *)
(*   eapply absconseq_rule_sound_aux ; eauto. *)
(*   right. *)
(*   exists x x4 x5. *)
(*   splits; eauto. *)
(*   introv Hs1 Hj1 Hj2. *)
(*   eapply absconseq_rule_sound_aux ; eauto. *)
(* Qed. *)
