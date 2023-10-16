Require Import sound_include.

Lemma absabt_rule_sound : 
  forall Spec sd I r ri p q s pa t,
    (* InfRules Spec sd pa I r ri (<|| ABORT ||> ** p) s q t -> *)
    RuleSem Spec sd pa I r ri (<|| ABORT ||> ** p) s q t.
Proof.
  intros.
  unfolds.
  introv Hsat0.
  destruct Hsat0 as (Hsat1 & Hsat2). 
  simpl in Hsat1. 
  simp join. 
  constructors; introv Hfalse; tryfalse.  
            
  introv Hsat Hjoinm2 Hjoin Hlostp Hnabt.
  false. apply Hnabt.
  exists OO; apply spec_stepO.

  introv _ _ _ Hnabt.
  false. apply Hnabt.
  exists OO; apply spec_stepO.

  introv _ _ _ Hnabt.
  false. apply Hnabt.
  exists OO; apply spec_stepO.

  introv _ _ _ Hnabt.
  false. apply Hnabt.
  exists OO; apply spec_stepO.

  introv _ _ _ _ _ Hnabt.
  false. apply Hnabt.
  exists OO; apply spec_stepO.

  introv _ _ _ _ _ Hnabt.
  false. apply Hnabt.
  exists OO; apply spec_stepO.

  introv Hsatp Hjoinm2 Hdisj.
  introv Hjoin Hnabt.
  false. apply Hnabt.
  exists OO; apply spec_stepO.

  introv _ _ _ Hnabt.
  false. apply Hnabt.
  exists OO; apply spec_stepO.
  
  introv _ _ _ Hnabt.
  false. apply Hnabt.
  exists OO; apply spec_stepO.

Qed.
