Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import kernel_obj_oper.
Require Import kernel_obj_oper_spec.

Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.
Require Import os_program.
Require Import abs_op.
Require Import inv_prop.
Require Import hoare_forward.
Require Import pure.
Require Import abs_infer_abt.
Require Import abs_step.

Require Import seplog_pattern_tacs.

Local Open Scope code_scope.
Local Open Scope int_scope.
Local Open Scope Z_scope.

(*********************** kernel obj oper **************************************)

Lemma kobjoper_absimp_succ:
  forall P sch s vp verr,
    verr = (Vint32 ($ OS_NO_ERR)) ->
    can_change_aop P ->
    absinfer sch
             ( <|| kobjoper (vp :: verr :: nil) ;; s ||> ** P)
             (<|| s ||> ** P).
Proof.
   infer_solver 0%nat.
Qed.

Lemma kobjoper_absimp_succ_abt:
  forall P sch s vp verr,
    verr <> (Vint32 ($ OS_NO_ERR)) ->
    can_change_aop P ->
    absinfer sch
             ( <|| kobjoper (vp :: verr :: nil) ;; s ||> ** P)
             (<|| ABORT ||> ** P).
Proof.
   intros.
   eapply absinfer_trans; try eapply absinfer_seq_abt; eauto.
   eapply absinfer_seq; eauto.
   eapply absinfer_abt; eauto.
   absimp_abt_solver.
Qed.

(* the proof that the function **kernel_obj_oper** satisfies its specification *) 
Lemma kernel_obj_oper_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal kernel_obj_oper vl logicl KObjOperPre ct->
    Some r =
    BuildRetI os_internal kernel_obj_oper vl logicl KObjOperPost ct->
    exists t d1 d2 s,
      os_internal kernel_obj_oper = Some (t, d1, d2, s) /\
      {|new_OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.
  hoare_lifts_trms_pre Aop.
  assert (Hv : v'1 = (Vint32 ($ OS_NO_ERR)) \/ v'1 <> (Vint32 ($ OS_NO_ERR))) by tauto.
  destruct Hv.
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply kobjoper_absimp_succ; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  hoare forward.
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply kobjoper_absimp_succ_abt; eauto.
  can_change_aop_solver.
  eapply absinfer_eq.
  apply absabort_rule.
Qed.
