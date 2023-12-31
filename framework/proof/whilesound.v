Require Import sound_include.

Lemma while_sim_aux :
  forall FSpec sd I r ri asrt tp e s li t,
    (asrt ==> EX v, Rv e@tp==v) ->  
    forall  C c ke ks ks' o aop O  , 
      C = (c , (ke,ks))  ->
      (
        (
          C = (SKIP,(kenil,kstop)) /\ ks'=kstop
          /\ (o,O,aop) |= asrt //\\ Aisfalse e /\ satp o O (CurLINV li t) 
        ) \/
        (
          ks' = kseq (swhile e s) kstop /\
          MethSimMod FSpec sd C o aop O li I r ri (lift asrt) t
        ) \/
        (
          C  = nilcont (swhile e s) /\ ks' = kstop /\  (o,O,aop) |= asrt /\ satp o O (CurLINV li t) 
        ) \/
        (
          ks' = (kwhile e s kstop) /\ 
          ks =kstop /\ 
          (o,O,aop) |= EX v, Rv e@tp==v  /\
                             estepstar (cure e) kenil (get_smem o) c  ke (get_smem o) /\ 
                             satp o O (CurLINV li t)  /\
          (o,O,aop) |= asrt
        )
      ) -> 
      (
        forall (o : taskst) (O : osabst) (aop : absop),
          (o, O, aop) |= asrt /\ satp o O (CurLINV li t)  ->
          MethSimMod FSpec sd  (cure e, (kenil, kstop))  o aop O li I r ri (lift asrt) t
      )->  
      (    
        forall (o : taskst) (O : osabst) (aop : absop),
          (o, O, aop) |= asrt //\\ Aistrue e /\ satp o O (CurLINV li t) ->
          (* ~ (exists O', hmstepstar sd aop O (ABORT) O') -> *)
          MethSimMod FSpec sd (nilcont s) o aop O li I r ri (lift asrt) t 
      ) (* ->  *)
      (* ~ (exists O', hmstepstar sd aop O (ABORT) O')  *)
      -> MethSimMod FSpec sd (c, (ke, ks ## ks')) o aop O li I r ri (lift (asrt //\\ Aisfalse e)) t.
Proof.
  intros FSpec sd I r ri asrt tp e s li t Hsat.
  cofix Hcofix. 
  introv  Hcode Hcase  Himpe Himp.
  (* introv Hnabt_abs.  *)
  destruct Hcase as [Hskp | Hcase].
  (*skip case*)
  destruct Hskp as (Hcs & Hks & Hsf).
  subst.
  inverts Hcs.
  simpl.
  constructors; introv Hfalse; tryfalse.
  (* introv _ _ _ Hfal.  *)
  introv _ _ _ Hfal Hnabt.
  false.
  invertstep idtac.
  inverts Hfalse.
  (* introv  Htsj Hinv Habsj. *)
  introv Htsj Hinv Habsj Hnabt.
  exists aop  OO O Os.
  splits; eauto.
  constructors.
  simp join; auto.
  simp join; auto.

  destruct Hfalse as (_ &  _ & Hf &_).
  false. apply Hf.
  unfolds. eexists; eauto.

  (*swhile e s case*)
  destruct Hcase as [Hsw | Hcase].
  destruct Hsw as (Heqks & Hsim).
  subst.
  inverts Hsim.
  assert (notabortm (c, (ke, ks)) \/ ~ notabortm (c, (ke, ks))) as Hasrf.
  tauto.
  destruct Hasrf as [Htrue | Hfalse].
  constructors; introv Hfalse; tryfalse. 
  (* introv Hinv Hjm1 Hjm2 Hstep. *)
  introv Hinv Hjm1 Hjm2 Hstep Hnabt_abs. 
  assert (disjoint O Os) as Hab.
  eexists; eauto.
  lets Hnabt : H6 p Htrue Hjm1 Hab; eauto.


  lets Hre :  loststep_keq_while_mono Hstep Hnabt.
  eauto. eauto. (* added due to change in the simulation *)  
  destruct Hre as (c' & ke' & ks' & Hstep' & HC).
  subst.
  (* lets Hex : H Hinv Hjm1 Hjm2 Hstep'. *)
  lets Hex : H Hinv Hjm1 Hjm2 Hstep' Hnabt_abs.  
  lets Hfcall' : fcall_not  Hfalse.
  auto.
  simp join.
  do 6 eexists; splits;  eauto.

  inverts Hfalse.
  destruct Htrue as (Hff'& _ ).
  false.
  apply Hff';  do 4 eexists;  eauto.
  destruct Htrue as (_&Hff'& _ ).
  false.
  apply Hff';  do 2 eexists;  eauto.
  inverts Hfalse.
  eauto.

  inverts Hfalse.
  false.
  eapply kseq_not_kstop; eauto.
  inverts Hfalse.
  introv  Hcall Hint.
  destruct Htrue as (_&_&_&Hff'& _ ).
  false.
  apply Hff'. 
  eexists ks; splits; auto.  
  eapply callcont_addcont_none;eauto.
  eapply intcont_none_addcont; eauto.

  inverts Hfalse.
  introv Hfs Hcall Hint.
  destruct Htrue as (_&_&_ & _ &Hff'&_  ).
  false.
  apply Hff'.
  rewrite kseq_eq_addstmt in *.
  lets Hex  :  addstmt_kret_exist H12.
  destruct Hex as (ks'' & Hks).
  unfolds.
  subst ks. 
  inverts H12.
  rewrite <-  kseq_eq_addstmt  in *.
  do 2 eexists; splits; eauto.
  eapply callcont_addcont_none;eauto.
  eapply intcont_none_addcont; eauto.
  inverts Hfalse.

  introv Hcall Hint.
  unfolds in Htrue.
  destruct Htrue as (_&_ & _ & _  & _  & Hff'&_).
  false.
  apply Hff'. 
  rewrite kseq_eq_addstmt in *.
  rewrite <-  kseq_eq_addstmt in *.
  exists  ks; splits; auto.
  eapply  intcont_none_addcont; eauto.
  eapply callcont_addcont_none;eauto.

  (* introv  Hjj11 Hjj22 Hinvv . *)
  introv Hjj11 Hjj22 Hinvv Hjoin Hnabt.
  lets Hnabtt : H6 p Htrue Hjj11 Hjj22 Hinvv. 
  eapply loststepabt_cont_loststepabt'; eauto.

  inverts Hfalse.
  destruct Htrue as (_&_ & _ & _  & _  & _&Hff'&_).
  false.
  apply Hff'.
  do 4 eexists; eauto.

  inverts Hfalse.
  destruct Htrue as (_&_ & _ & _  & _  & _&_&Hff').
  false.
  apply Hff'.
  do 2 eexists; eauto.
  (**)
  casenot Hfalse.
  unfolds in Cs.
  destruct Cs as (f&vl&tl&ks0&Hceq).
  inverts Hceq.
  constructors;introv Hfalse; tryfalse.
  false.
  apply Hfalse.
  do 4 eexists; eauto.
  apply eq_sym in Hfalse; inverts Hfalse.
  (* introv Hmdisj Hinv Hdisj. *)
  introv Hmdisj Hinv Hdisj Hnabt. 
  (* lets Hres : H0 Hmdisj Hinv Hdisj; eauto. *)
  lets Hres : H0 Hmdisj Hinv Hdisj Hnabt; eauto.
  simp join.
  do 12 eexists; splits; eauto.
  splits; auto.
  introv Hbs.
  splits.
  eapply H18; eauto.
  introv Henv Hpst Hjhh.
  eapply Hcofix; eauto.
  branch 2.
  splits; eauto.
  eapply H18; eauto.

  destruct Hfalse as (Hf &_).
  false. apply Hf.
  do 4 eexists; eauto.

  casenot Hfalse.
  destruct Cs as (x & ks0 & Heeq ).
  subst.
  inverts Heeq.
  constructors;introv Hfalse; tryfalse.
  (* introv _ _ _ Hstepf. *)
  introv _ _ _ Hstepf Hnabt. 
  invertstep idtac.
  (* introv   Htj Hinv HHabs. *)
  introv Htj Hinv HHabs Hnabt'. 
  inverts Hfalse.
  (* lets Hsw : H1  Htj Hinv HHabs; eauto. *)
  lets Hsw : H1  Htj Hinv HHabs Hnabt'; eauto. 
  simp join.
  do 9 eexists; splits; eauto.
  splits; auto.
  destruct H17;[left;simp join; split;auto | right; auto].
  introv Hjj Hinvv Hk.
  eapply Hcofix; eauto.
  

  destruct Hfalse as ( _& Hff & _ ). 
  false.
  apply Hff; do 2 eexists; eauto.
  casenot Hfalse.
  destruct Cs as (vv & Hcq).
  inverts Hcq.
  constructors; introv Hfalse; tryfalse.
  (* introv Hinv11 Hjm11 Hjm12 Hstep11. *)
  introv Hinv11 Hjm11 Hjm12 Hstep11 Hnabt. 
  simpl in Hstep11.
  invertstep idtac.
  (* lets Hssk : H2  Hinv11 Hjm12; eauto. *)
  lets Hssk : H2  Hinv11 Hjm12 Hnabt; eauto.
  clear - Hjm11.
  unfolds.
  unfold joinm2 in Hjm11.
  unfold joinmem in Hjm11.
  join auto.
  destruct Hssk as (gamma' & OO' &  O' & Os' & Hdds & Hstar & Hinvv & Hast).
  exists gamma'  OO'   o  Ms O' Os'.
  splits;eauto.
  destruct Hast; auto.
  assert (kstop = kstop ## kstop).
  simpl.
  auto.
  rewrite H9.
  eapply Hcofix; eauto.
  branch 3.
  splits; eauto.
  destruct Hast; auto.
  destruct Hast; auto.

  (* lets Hssk : H2  Hinv11 Hjm12; eauto. *)
  lets Hssk : H2  Hinv11 Hjm12 Hnabt; eauto.  
  clear - Hjm11.
  unfolds.
  unfold joinm2 in Hjm11.
  unfold joinmem in Hjm11.
  join auto.
  destruct Hssk as (gamma' & OO' &  O' & Os' & Hdds & Hstar & Hinvv & Hast).
  exists gamma'  OO'   o  Ms O' Os'.
  splits;eauto.
  destruct Hast; auto.
  assert (kstop = kstop ## kstop).
  simpl.
  auto.
  rewrite H9.
  eapply Hcofix; eauto.
  branch 3.
  splits; eauto.
  destruct Hast; auto.
  destruct Hast; auto.

  (* introv _ _ _  Hfs. *)
  introv _ _ _ _ _ Hfs.
  unfolds in Hfs.
  apply Hfs.
  eexists. 
  exists o2. 
  destruct o2  as [[]].
  eapply ostc_step;eauto.
  eapply stmt_step; eauto.
  simpl.
  destruct vv;
    constructors.
  
  (**)
  casenot Hfalse.
  destruct Cs as (ks0 & Heeq & Hcal& Hint).
  inverts Heeq.
  constructors; introv Hfalse; tryfalse.
  (* introv Hinv Hjm1 Hjm2 Hlost. *)
  introv Hinv Hjm1 Hjm2 Hlost Hnabt. 
  invertstep idtac.
  lets Hf' :  callcont_nont_addkseq_kstop (swhile e s) Hcal. 
  tryfalse.
  inverts Hfalse.
  (* introv  Hcc Hci Hmdisj Hinvv Hodisj. *)
  introv  Hcc Hci Hmdisj Hinvv Hodisj Hnabt.
  lets Hres : H3 Hcal Hint Hmdisj Hinvv Hodisj;  eauto. 
  destruct Hfalse as (_ & _ & _ &Hff & _ ). 
  false.
  apply Hff.
  eexists; splits; eauto.
  eapply callcont_nont_addkseq_kstop; eauto.
  eapply intcont_nont_addstmt_prev; eauto.

  (**)
  casenot Hfalse.
  destruct Cs as (v &ks0 & Heeq & Hcal & Hint).
  inverts Heeq.
  constructors; introv Hfalse; tryfalse.
  (* introv Hinv Hjm1 Hjm2 Hlost. *)
  introv Hinv Hjm1 Hjm2 Hlost Hnabt. 
  invertstep idtac.
  lets Hf' :  callcont_nont_addkseq_kstop (swhile e s) Hcal. 
  tryfalse.
  inverts Hfalse.
  (* introv   Hcc Hci Hmdisj Hinvv Hodisj. *)
  introv   Hcc Hci Hmdisj Hinvv Hodisj Hnabt. 
  lets Hres0 : H4 Hcal Hint Hmdisj Hinvv Hodisj;  eauto.  


  destruct Hfalse as (_&_& _& _ &Hff & _ ). 
  false.
  apply Hff.
  unfolds.
  simpl.
  do 2 eexists; splits; eauto.
  eapply callcont_nont_addkseq_kstop; eauto.
  eapply intcont_nont_addstmt_prev; eauto.

  casenot Hfalse.
(*  eapply Classical_Prop.NNPP in Hfalse.*)
  destruct Cs as (ks0 & Heeq  & Hint & Hcal).
  inverts Heeq.
  constructors; introv Hfalse; tryfalse.
  (* introv Hinv Hjm1 Hjm2 Hlost . *)
  introv Hinv Hjm1 Hjm2 Hlost Hnabt.
  invertstep idtac.
  lets Hnone : intcont_nont_addstmt_prev ((swhile e s)) Hint.
  tryfalse.
  (* introv Hcc Hci Hmdisj Hinvv Hodisj. *)
  introv Hcc Hci Hmdisj Hinvv Hodisj Hnabt.
  inverts Hfalse.
  lets Hres : H5 Hcal Hint Hmdisj Hinvv Hodisj;eauto. 
  destruct Hfalse as (_&_&_& _ & _ &Hff &_). 
  false.
  apply Hff.
  eexists; splits; eauto.
  eapply intcont_nont_addstmt_prev; eauto.
  eapply callcont_nont_addkseq_kstop; eauto.

  casenot Hfalse.
  destruct Cs as (e1&e2&e3 & ks0 & Hceq).
  inverts Hceq.
  constructors; introv Hfalse; tryfalse.
  (* introv _ _ _ Hlss. *)
  introv _ _ _ Hlss Hnabt.
  invertstep tryfalse.
  unfolds in Hfalse.
  destruct Hfalse as (_&_&_&_&_&_&Hf&_).  
  false.
  apply Hf.
  unfolds.
  do 4 eexists; eauto.

  inverts Hfalse.
  (* introv Hc' Hmdisj Hinv. *)
  introv Hc' Hmdisj Hinv Hnabt.
  lets Hres : H7 Hmdisj Hinv Hnabt. 
  eauto.
  auto.
  simp join.
  do 14 eexists; splits; eauto. 
  splits; eauto.

  apply Classical_Prop.NNPP in Hfalse.
  destruct Hfalse as (ek & ks0 & Hceq).
  inverts Hceq.
  constructors; introv Hfalse; tryfalse.
  (* introv _ _ _ Hlss. *)
  introv _ _ _ Hlss Hnabt. 
  invertstep tryfalse.
  unfolds in Hfalse.
  destruct Hfalse as (_&_&_&_&_&_&_&Hf).  
  false.
  apply Hf.
  unfolds.
  do 2 eexists; eauto.
  inverts Hfalse.
  (* introv Hc' Hmdisj Hinv. *)
  introv Hc' Hmdisj Hinv Hnabt.
  (* lets Hres : H8 Hmdisj Hinv ; eauto. *)
  lets Hres : H8 Hmdisj Hinv Hnabt; eauto.
  simp join.
  do 5 eexists; splits; eauto. 
  destruct H12; simp join.
  left; do 3 eexists; splits; eauto.
  right; do 3 eexists; splits; eauto.
  introv Hs Hj Hk.
  eapply Hcofix; eauto.

  (**)
  (* c = curs (swhile e s) /\ ks' = kstop /\ ks = kstop/\ (exists m isr aux v0,
    o = (m, isr, aux) /\ estepstar (cure e) kenil m (curv v0) kenil m)*)
  destruct Hcase as [ Hcsw | Hcase].
  destruct  Hcsw as (Hccde & Hkss & Hpre ).
  unfold nilcont in Hccde.
  rewrite  Hcode in  Hccde.
  inverts Hccde.
  subst.
  simpl.
  constructors;introv Hfalse; tryfalse.
  
  (* introv Hinv Hjm1 Hjm2 Hlstep. *)
  introv Hinv Hjm1 Hjm2 Hlstep Hnabt.  
  invertstep idtac.
  exists  aop OO  o  Ms O Os.
  splits; eauto.
  constructors.
  destruct Hpre; auto.
  assert (kwhile e s kstop = kstop ## kwhile e s kstop).
  simpl; auto.
  rewrite H.
  eapply Hcofix;eauto.
  branch 4.
  splits; eauto.
  destruct Hpre; auto.
  constructors.
  destruct Hpre; auto.
  destruct Hpre; auto.
  (*
apply notabort_expr.
constructors.
   *)
  (* introv  _ _  Hfal. *)
  introv _ _ _ _ Hfal.
  introv Hstep.
  unfolds in Hstep.
  apply Hstep.
  destruct o2 as [[[[]]]].
  do 2 eexists; eapply ostc_step;eapply stmt_step; constructors.
  (* ks' = kwhile e s kstop*)
  
  destruct  Hcase as (Hks'& Hks  & Hste & Hestar &Hsal &Hasrt).
  subst.
  destruct o as [[[[G E] M] isr] aux].
  simpl substaskst in *.
  simpl get_smem in *.
  simpl get_mem in *.
  assert( (G, E, M, isr, aux, O, aop)
            |= EX v : val, Rv e @ tp ==  v) as Hassst.
  auto.
  simpl in Hste.
  destruct Hste as (v' & Heval &Het &Hvn).
  subst.
  lets Hestp : evalval_imply_estepstar kenil Heval.
  lets Hres :  estepstar_imply_star Hestar Hestp.
  lets Hdes :  estepv_notabortm Hres.
  constructors;introv Hfalse; tryfalse.
  {
  (* introv Hinv Hjm1 Hjm2 Hstep. *)
  introv Hinv Hjm1 Hjm2 Hstep Hnabt.
  inverts Hres.
  {
  simpl in Hstep.
  invertstep idtac.
    {
      simp join.
      assert ( kseq (swhile e s) kstop = kstop ##  kseq (swhile e s) kstop).
      simpl; auto.
      do 6 eexists. 
      splits; eauto.
      1: constructor.
      rewrite H6.
      eapply Hcofix; eauto.
      branch 2.
      splits; auto.
      eapply Himp.
      split; auto.
      simpl.
      splits; auto.
      eexists; splits; eauto.
    }
    {
      simp join.
      assert ( kstop = kstop ## kstop).
      simpl; auto.
      do 6 eexists. 
      splits; eauto.
      1: constructor.
      rewrite H6.
      eapply Hcofix; eauto.
      branch 1.
      splits; auto.
      split; auto.
      simpl.
      eexists; splits; eauto.
    }
  }
  lets  Hinrr :  estep_lstep_deter p H Hstep;eauto.
  destruct Hinrr.
  apply sym_eq in H1.
  subst.
  lets Hintr :   estep_join_lstep p H Hjm1 .
  destruct Hintr as (o2''& C''& Hstepp & Heqo & Heqc).
  apply sym_eq in Heqo.
  subst.
  
  simp join.
  do 6 eexists; splits; eauto.
  1: constructor.
  assert  ( kwhile e s kstop = kstop ##  kwhile e s kstop) as Htt.
  simpl; auto.
  rewrite Htt.
  eapply Hcofix; eauto.
  branch 4.

  lets Hex : estep_mem_same    H.
  subst m'.
  lets ess : estepstar_estep_trans Hestar H; eauto.

 unfolds in Hjm1.
 unfold joinmem in *.
 simp join.
 simpl in Hinv.
  simp join.
  splits; eauto.
  }
  
  inverts Hfalse.
  destruct Hdes as (Hf&_).
  false. apply Hf. do 4 eexists; eauto.
  inverts Hfalse.
  destruct Hdes as (_&Hf&_).
  false. apply Hf. do 2 eexists; eauto.
  inverts Hfalse.
  destruct Hdes as (_&_&Hf&_).
  false. apply Hf. do 2 eexists; eauto.
  inverts Hfalse.
  destruct Hdes as (_&_&_&_&Hf&_).
  false. apply Hf. do 3 eexists; eauto.

  (* introv   Hjj11 Hjj22 Hinvv Hstep. *)
  {
    introv Hjj11 Hjj22 Hinvv Hjoin Hnabt Hstep. 
    pose proof I as H.
      inverts Hres.
      {
        apply Hstep.
        simpl.
        destruct o2 as [[? ?] ?].
        assert (istrue v' = Some true \/ istrue v'  = Some false) as Hv'.
        {
          destruct v'; simpl; try tauto; tryfalse.
          destruct (Int.eq i0 Int.zero); try tauto.
        }
        destruct Hv'; do 2 eexists; econstructor; eapply stmt_step; eauto;
          [apply svwhilet_step; auto | apply svwhilef_step; auto].
      }
      {
        destruct Hjj22 as [? [? ?]].
        revert Hstep; eapply loststep_join_notabt.
        + apply H2.
        + apply H3.
        + do 2 eexists.
         econstructor.
         econstructor; eauto.
      }
  }
  
  inverts Hfalse.
  destruct Hdes as (_&_&_&_&_&Hf&_).
  false.
  apply Hf.
  do 4 eexists; eauto.

  inverts Hfalse.
  destruct Hdes as (_&_&_&_&_&_&Hf).
  false.
  apply Hf.
  do 2 eexists; eauto.

Qed.


Lemma while_rule_sound :
  forall Spec sd I r ri p  e s  tp li t,  
    ( p ==> EX v , Rv e @ tp ==  v) ->
    RuleSem  Spec sd li I r ri ( p //\\ (Aistrue e)) s p t  -> 
    RuleSem Spec sd  li I r ri p (swhile e s) (p //\\ (Aisfalse e)) t.
Proof.
  introv Hsat Hsim.
  unfold RuleSem in *.
  introv Hwf.
  unfold nilcont.
  assert (kstop = kstop ## kstop); simple; auto.
  rewrite H.
  destruct Hwf.
  eapply while_sim_aux with (tp:=tp)(ke :=kenil)(s:=s); eauto.
  right. right. left.
  splits; eauto.
  introv Hsp.
  destruct o0 as [[[[G E]M] isr]aux].
  lets Hsate : Hsat Hsp.
  destruct Hsate as (v&Heval&Hetp & Hvn).
  simpl in Hetp.
  destruct Hetp.
  eapply skip_expr_eval_msim_hold with (v:=v); eauto.
  destruct Hsp; auto.
  constructors; introv Hfalse; tryfalse.
  simpl substaskst in *.
  introv Hinv Hjm1 Hjm2 Hlstep.
  invertstep idtac.
  inverts Hfalse.
  unfold getmem.
  simpl get_smem in *.
  simpl get_mem in *.
  introv Hdj Hinvv Hdjj.
  exists aop0 OO  O0 Os.
  splits; eauto.
  constructors.
  destruct Hsp; auto.
  destruct Hsp; auto.
  destruct Hfalse as (_&_&Hf&_).
  false.
  eapply Hf.
  eexists; eauto.
Qed.

