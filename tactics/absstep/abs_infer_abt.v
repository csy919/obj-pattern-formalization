
Require Import base_tac. 
Require Import opsem.
Require Import cancel_abs. 
Require Import seplog_lemmas. 
Require Import seplog_tactics. 
Require Import abs_infer_step.

Ltac absimp_abt_solver := 
  unfolds; intros;
  eexists; exgamma;
  (first [ splits ; 
           [ try simpl_subst_gamma;
             try hmstep_call_consturctor; try eapply spec_prim_step_abt; 
             [ unfolds; repeat eexists; subst;
               try (eapply absdata_elim; eauto with abst_solver_base); try eauto 
             | try apply map_join_emp 
             |  repeat hmstep_call_consturctor
             | .. ]
           | sep remember (1 :: nil)%nat; simpl in *; simpljoin ;
           do 6 eexists ; splits ; try eauto ; eapply change_aop_rule; eauto]
         | idtac] ).

Ltac absimp_abt_solver' :=
  unfolds; intros;
  eexists; exgamma;
 (first  [ splits;
      [ try simpl_subst_gamma;
         try hmstep_call_consturctor; try eapply spec_prim_step_abt;
         [ unfolds; repeat (try splits; try eauto; try eexists); subst;
            try (eapply cancel_abs.absdata_elim; eauto with abst_solver_base);
            try eauto
         | try apply map_join_emp
         | repeat hmstep_call_consturctor
         | .. ]
      | sep remember (1%nat :: nil); simpl in *; simpljoin;
         do 6 eexists; splits; try eauto; eapply change_aop_rule; eauto ]
   | idtac ]).

