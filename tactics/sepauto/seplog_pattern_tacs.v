
Require Import include_frm.
Require Import sep_auto.
Require Import join_lib. 
Require Import hoare_conseq. 
Require Import derived_rules.

Require Import List. 


Ltac sep_lift_context_in H trm :=
  match type of H with
    | _ |= ?P =>
      match find_match_context P trm with
         | none _ => idtac 1 "no such term in the Hsat"; fail 1
         | some ?a => sep lifts (a::nil)%nat in H
      end
  end.

Ltac sep_lift_context trm :=
  match goal with
    | |- _ |= ?P =>
      match find_match_context P trm with
         | none _ => idtac 1 "no such term in the Hsat"; fail 1
         | some ?a => sep lifts (a::nil)%nat 
      end
  end.

Inductive _num_ := _N_ (n:nat).

Ltac find_match_context_skip' Hp x k :=
  match Hp with
  | ?A ** ?B =>
      match find_match_context_skip' A x k with
      | (some (?a, ?k')) => constr:(some (a, k'))
      | (none (?a, ?k')) =>
          match find_match_context_skip' B x k' with 
          | (some (?b, ?k'')) => constr:(some ((a + b)%nat, k'')) 
          | (none (?b, ?k'')) => constr:(none ((a + b)%nat, k'')) 
          end
      end
  | context [x] =>
    match k with
      0%nat => constr:(some (1%nat, 0%nat))
    | S ?k' => constr:(none (1%nat, k')) 
    end  
  | _ => constr:(none (1%nat, k))
  end.

Ltac find_match_context_skip Hp x k :=
  let y := find_match_context_skip' Hp x k in
  eval compute in y.

Ltac trms_to_idxs trms :=
  match trms with
    (?trms', ?trm) =>
    let l := (trms_to_idxs trms') in 
    match trm with 
      _N_ ?n => constr: (n :: l)
    | _ => 
      match goal with
      | |- _ |= ?P =>
        match find_match_context P trm with
        | none _ => l 
        | some ?a => constr: (a :: l) 
        end
      end
    end
  | pnil => constr: (@nil nat)
  | ?trm =>
    match trm with
      _N_ ?n => constr: (n :: (@nil nat)) 
    | _ => 
      match goal with
      | |- _ |= ?P =>
        match find_match_context P trm with
        | none _ => constr: (@nil nat) 
        | some ?a => constr: (a :: (@nil nat))
        end
      end
    end
  end.

Ltac trms_to_idxs_skip trms :=
  match trms with
  | (?trm0, _N_ ?k) =>
    match goal with
    | |- _ |= ?P =>
      match find_match_context_skip P trm0 k with
      | none _ => constr: (@nil nat)
      | some (?a, _) => constr: (a :: (@nil nat)) 
      end
    end
  | (?trms', ?trm) =>
    let l := (trms_to_idxs_skip trms') in 
    match trm with 
    | (?trm0, _N_ ?k) =>
      match goal with
      | |- _ |= ?P =>
        match find_match_context_skip P trm0 k with
        | none _ => l
        | some (?a, _) => constr: (a :: l)
        end
      end
    | _ => 
      match goal with
      | |- _ |= ?P =>
        match find_match_context P trm with
        | none _ => l 
        | some ?a => constr: (a :: l) 
        end
      end
    end
  | pnil => constr: (@nil nat)
  | ?trm =>
    match goal with
    | |- _ |= ?P =>
      match find_match_context P trm with
      | none _ => constr: (@nil nat) 
      | some ?a => constr: (a :: (@nil nat))
      end
    end
  end.  

Ltac trms_to_idxs_in H trms :=
  match trms with
    (?trms', ?trm) =>
    let l := (trms_to_idxs_in H trms') in
    match trm with
      _N_ ?n => constr: (n :: l)
    | _ => 
      match type of H with 
      | _ |= ?P =>
        match find_match_context P trm with
        | none _ => l 
        | some ?a => constr: (a :: l)
        end 
      end
    end
  | pnil => constr: (@nil nat)
  | ?trm =>
    match trm with
      _N_ ?n => constr: (n :: (@nil nat))
    | _ => 
      match type of H with
      | _ |= ?P =>
        match find_match_context P trm with
        | none _ => constr: (@nil nat) 
        | some ?a => constr: (a :: (@nil nat))
        end
      end
    end
  end.

Ltac trms_to_idxs_skip_in H trms :=
  match trms with
  | (?trm0, _N_ ?k) =>
    match type of H with
    | _ |= ?P =>
      match find_match_context_skip P trm0 k with
      | none _ => constr: (@nil nat)
      | some (?a, _) => constr: (a :: (@nil nat))
      end
    end
  | (?trms', ?trm) =>
    let l := (trms_to_idxs_skip_in H trms') in
    match trm with
    | (?trm0, _N_ ?k) =>
      match type of H with
      | _ |= ?P =>
        match find_match_context_skip P trm0 k with
        | none _ => l
        | some (?a, _) => constr: (a :: l)
        end
      end
    | _ =>
      match type of H with
      | _ |= ?P =>
        match find_match_context P trm with
        | none _ => l
        | some ?a => constr: (a :: l)
        end
      end
    end
  | pnil => constr: (@nil nat)
  | ?trm =>
    match type of H with
    | _ |= ?P =>
      match find_match_context P trm with
      | none _ => constr: (@nil nat)
      | some ?a => constr: (a :: (@nil nat))
      end
    end    
  end.

(* Ltac trms_to_idxs_skip_in H trms := *)
(*   match trms with *)
(*     (?trms', ?trm) => *)
(*     let l := (trms_to_idxs_skip_in H trms') in *)
(*     match trm with *)
(*     | (?trm0, _N_ ?k) => *)
(*       match type of H with *)
(*       | _ |= ?P => *)
(*         match find_match_context_skip P trm0 k with *)
(*         | none _ => l *)
(*         | some (?a, _) => constr: (a :: l) *)
(*         end *)
(*       end *)
(*     | _ =>  *)
(*       match type of H with  *)
(*       | _ |= ?P => *)
(*         match find_match_context P trm with *)
(*         | none _ => l  *)
(*         | some ?a => constr: (a :: l) *)
(*         end  *)
(*       end *)
(*     end *)
(*   | pnil => constr: (@nil nat) *)
(*   | ?trm => *)
(*     match trm with *)
(*     | (?trm0, _N_ ?k) => *)
(*       match type of H with *)
(*       | _ |= ?P => *)
(*         match find_match_context_skip P trm0 k with *)
(*         | none _ => constr: (@nil nat) *)
(*         | some (?a, _) => constr: (a :: (@nil nat)) *)
(*         end *)
(*       end *)
(*     | _ =>  *)
(*       match type of H with *)
(*       | _ |= ?P => *)
(*         match find_match_context P trm with *)
(*         | none _ => constr: (@nil nat)  *)
(*         | some ?a => constr: (a :: (@nil nat)) *)
(*         end *)
(*       end *)
(*     end *)
(*   end.   *)

(* ========================================== *)

Ltac sep_rmb_trms trms :=
  let l := trms_to_idxs trms in sep_remember (List.rev l).

Ltac sep_rmb_trms_in H trms :=
  let l := trms_to_idxs_in H trms in sep_remember_in H (List.rev l).

Ltac sep_lifts_trms trms :=
  let l := trms_to_idxs trms in sep lifts (List.rev l).

Ltac sep_lifts_trms_in H trms :=
  let l := trms_to_idxs_in H trms in sep lifts (List.rev l) in H.

Ltac hoare_lifts_trms_pre trms :=
  match goal with
    | |-  {| _, _, _, _, _, _ |} |- _  {{ _ //\\ _ }} _ {{ _ //\\ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule3;
       [ intros s H; let l := (trms_to_idxs_in H trms) in sep lifts (List.rev l) in H; exact H | idtac ]
    | |-  {| _, _, _, _, _,_ |} |- _ {{ _ }} _ {{ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule1;
       [ intros s H; let l := (trms_to_idxs_in H trms) in sep lifts (List.rev l) in H; exact H | idtac ]
  end.

(* ========================================== *)

Ltac sep_rmb_skp trms :=
  let l := trms_to_idxs_skip (_N_ 0, trms) in sep_remember (List.rev l).

Ltac sep_rmb_skp_in H trms :=
  let l := trms_to_idxs_skip_in H (_N_ 0, trms) in sep_remember_in H (List.rev l).

Ltac sep_lifts_skp trms :=
  let l := trms_to_idxs_skip trms in sep lifts (List.rev l).

Ltac sep_lifts_skp_in H trms :=
    let l := trms_to_idxs_skip_in H trms in sep lifts (List.rev l) in H. 

Ltac hoare_lifts_skp_pre trms :=
  match goal with
    | |-  {| _, _, _, _, _, _ |} |- _  {{ _ //\\ _ }} _ {{ _ //\\ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule3;
       [ intros s H; let l := (trms_to_idxs_skip_in H (_N_ 0, trms)) in sep lifts (List.rev l) in H; exact H | idtac ]
    | |-  {| _, _, _, _, _,_ |} |- _ {{ _ }} _ {{ _ }} => 
      let s := fresh in
      let H := fresh in
      eapply backward_rule1;
       [ intros s H; let l := (trms_to_idxs_skip_in H (_N_ 0, trms)) in sep lifts (List.rev l) in H; exact H | idtac ]
  end.

(* =================================================== *)

Ltac change_smo hyp :=
  repeat (
      match type of hyp with
      | context [substmo (?e, ?e0, ?m, ?i0, ?l, ?o, ?a) ?m' ?o'] =>
          change (substmo (e, e0, m, i0, l, o, a) m' o') with (e, e0, m', i0, l, o', a) in hyp
      end).

Ltac change_smo_hyps :=
  repeat (
      match goal with
      | H: context [substmo (?e, ?e0, ?m, ?i0, ?l, ?o, ?a) ?m' ?o'] |- _ => 
          change (substmo (e, e0, m, i0, l, o, a) m' o') with (e, e0, m', i0, l, o', a) in H
      end).

Ltac simp_mem_abst :=
  repeat (
      match goal with
      | H: context [getmem (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)] |- _ =>
          change (getmem (t1, t2, t3, t4, t5, t6, t7)) with t3 in H
      | H: context [getabst (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)] |- _ =>
          change (getabst (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)) with t6 in H
      | H: Maps.join ?t1 empenv ?t2 |- _ => (apply map_join_emp' in H; subst t1)
      | H: Maps.join empenv ?t1 ?t2 |- _ => (apply map_join_emp'' in H; subst t1)
      | H: context [?t = empenv] |- _ => subst t
      end).

Ltac simp_get_smem :=
  repeat (
      match goal with
      | H: context [getsmem (?t1, ?t2, ?t3, ?t4, ?t5, ?t6, ?t7)] |- _ =>
          change (getsmem (t1, t2, t3, t4, t5, t6, t7)) with (?t1, ?t2, ?t3) in H
      end).

Ltac simpl_sat H := unfold sat in H; fold sat in H; simpl substmo in H; simpl getmem in H; simpl getabst in H; simpl empst in H.

Ltac simpl_sat_goal := unfold sat; fold sat; unfold substmo; unfold substaskst; unfold getmem; unfold getabst; unfold get_smem; unfold get_mem.

Ltac join_to_sub := 
  match goal with
    H: Maps.join ?t1 ?t2 ?t3 |- Maps.sub ?t1 ?t => apply join_sub_l in H; auto
  | H: Maps.join ?t1 ?t2 ?t3 |- Maps.sub ?t2 ?t => apply join_sub_r in H; auto
  end; 
  repeat ( 
      match goal with
        H1: Maps.sub ?t1 ?t2 |- _ => 
          match goal with 
            H2: Maps.join t2 ?t3 ?t |- _ => apply join_sub_l in H2
          | H2: Maps.join ?t3 t2 ?t |- _ => apply join_sub_r in H2
          end
      end).

Ltac casetac trm1 trm2 Ht Hf :=
  let h := fresh in 
  assert (h: trm1 = trm2 \/ trm1 <> trm2) by tauto;
  destruct h as [Ht | Hf].
