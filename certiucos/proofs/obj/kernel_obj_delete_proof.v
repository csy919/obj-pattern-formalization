Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Require Import kernel_obj_delete.
Require Import kernel_obj_delete_spec.

Require Import abs_infer_step.
Require Import ucos_frmaop.
Require Import seplog_lemmas.
Require Import seplog_tactics.

Require Import abs_step.

Require Import sem_common.
Require Import OSTimeTickPure.
Require Import OSQPostPure.
Require Import seplog_pattern_tacs.
Require Import tcblist_setnode_lemmas.
Require Import objauxvar_lemmas.
Require Import objaux_pure.

Require Import obj_common.
Require Import obj_common_ext.

Require Import hoare_assign_tac_ext.

Require Import kobj_delete_pure.
Require Import semdel_pure.
Require Import protect.


Lemma absinfer_kobjdel_null_err_return :
  forall P sch s0, 
    can_change_aop P ->
    absinfer sch
             (<|| spec_code_cons (kobjdel (Vnull :: nil)) s0 ||> ** P)
             ( <|| s0 ||> ** P).
Proof.
  introv Hcop.
  simpl spec_code_cons.  
  infer_solver 0%nat.
Qed.

Lemma absinfer_kobjdel_type_err :
  forall P sch els ptr s,
    can_change_aop P ->
    ~(exists n wls, get els ptr = Some (abssem n, wls)) ->
    absinfer sch
             (<|| spec_code_cons (kobjdel (Vptr ptr :: nil)) s ||> ** HECBList els ** P)
             ( <|| s ||> ** HECBList els ** P).  
Proof.
  intros.
  simpl spec_code_cons.
  infer_solver 1%nat.
Qed.

Lemma absinfer_kobjdel_succ_nex_wait :
  forall P sch els els' ptr n s0,  
    can_change_aop P ->
    get els ptr = Some (abssem n, nil) -> 
    join els' (sig ptr (abssem n, nil)) els ->
    absinfer sch
             (<|| spec_code_cons (kobjdel (Vptr ptr :: nil)) s0 ||> ** HECBList els ** P)
             ( <|| kobjdel_ret (|nil|);; s0 ||> ** HECBList els' ** P).  
Proof.
  introv Hcop Hmq Hjo.
  simpl spec_code_cons.
  infer_solver 3%nat.
Qed.

Lemma absinfer_kobjdel_succ_ex_wait :
  forall P sch tls tls' els els' ptr wls n s0,  
    can_change_aop P ->
    get els ptr = Some (abssem n, wls) -> 
    wls <> nil -> 
    join els' (sig ptr (abssem n, wls)) els ->
    tls' = set_tls_rdy wls tls ->
    absinfer sch
             (<|| spec_code_cons (kobjdel (Vptr ptr :: nil)) s0 ||> ** HECBList els ** HTCBList tls ** P)
             ( <|| isched;; kobjdel_ret (|nil|);; s0 ||> ** HECBList els' ** HTCBList tls' ** P).  
Proof.
  intros.
  simpl spec_code_cons.
  simpljoin.
  infer_solver 2%nat.
  {
    unfolds.
    eapply eqdomtls_set_tls_rdy_gen.
    unfolds.
    intros.
    split; intros; auto.
  }
Qed.

Lemma absinfer_kobjdel_ret :
  forall P sch s0, 
    can_change_aop P ->
    absinfer sch (<|| kobjdel_ret (|nil|);; s0 ||> ** P) ( <|| s0 ||> ** P).
Proof.
  introv Hcop.
  infer_solver 0%nat.
Qed.

Lemma kernel_obj_delete_proof:
  forall vl p r logicl ct, 
    Some p =
    BuildPreI os_internal kernel_obj_delete vl logicl KObjDelPre ct->
    Some r =
    BuildRetI os_internal kernel_obj_delete vl logicl KObjDelPost ct->
    exists t d1 d2 s,
      os_internal kernel_obj_delete = Some (t, d1, d2, s) /\
      {|new_OS_spec , GetHPrio, OSLInv, I, r, Afalse|}|-ct {{p}} s {{Afalse}}. 
Proof.
  init_spec.

  inverts H0.
  rename v'2 into pevent_blk.
  subst logicl.

  hoare forward prim.
  hoare unfold.

  (* If (pevent ′ ==ₑ NULL) ... *)
  hoare forward; pure_auto.
  hoare unfold pre.
  assert (pevent_blk = Vnull) by pure_auto.
  subst.

  hoare_lifts_trms_pre Aop.
  eapply abscsq_rule.
  apply noabs_oslinv. 
  eapply absinfer_kobjdel_null_err_return; eauto. 
  go.
  eapply absinfer_eq.

  (* EXIT_CRITICAL *) 
  hoare forward prim. 
  go.
  (* return (NULL) *) 
  hoare forward.

  (******* ptr != NULL *******)
  apply hoare_disj_afalseP_l_pre.
  hoare normal pre.
  hoare_split_pure_all.
  destruct H2 as [Hinjzero | Hinjnull].
  2: {
    simpl in Hinjnull.
    false.
    lets H00: isptr_val_inj_false Hinjnull; eauto. 
  }
  destruct H1.
  subst.
  simpl in Hinjzero.
  inverts Hinjzero.
  destruct H1 as ((pb & pi) & Heq).
  subst.
  (* value of ptr is now "Vptr (pb, pi)" *)
  clear Hinjzero.
  unfold AOBJ.
  hoare unfold.

  unfold tcbllsegobjaux.
  hoare_lifts_trms_pre (llsegobjaux, AOSTCBList, p_local).
  eapply backward_rule1.
  introv Hsat.
  eapply tcbllsegobjaux_split3_join2_frm''; eauto.
  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.
  rename v'25 into locmp.
  rename v'26 into ptrmp.
  assert (Hget_loc: get locmp ct = Some (V$ __Loc_objdel)).
  { eapply join_get_r; eauto.
     eapply join_sig_get; eauto.
   }
  assert (Hget_ptr: get ptrmp ct = Some (Vptr  (pb, pi))).
  { eapply join_get_r; eauto.
     eapply join_sig_get; eauto.
   }
  assert (Htsk: tsk_loc_ptr locmp ptrmp ct __Loc_objdel (pb, pi)).
  { unfolds. eauto. }
  lets Haux: Htsk. eapply obj_aux_del in Haux; eauto.
  destruct Haux as (Hget & Hnex & Hnref).
  destruct Hget as (n & wls & Hget).

  (* ptr points to an active obj *) 
  unfold AECBList.
  hoare unfold.
  rename H1 into H_elp.
  lets Hctr: ECBList_P_get_ectr_some Hget H_elp.
  destruct Hctr as (evl & etbl & petbl & Hgetectr).

  eapply backward_rule1.
  introv Hsat.
  sep_lifts_trms_in Hsat evsllseg.
  eapply get_ectr_decompose; eauto.
  hoare unfold.

  hoare_assert_pure (length v'26 = length v'34). 
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg. 
    eapply evsllseg_aux in Hsat. 
    destruct Hsat.
    eauto. 
  }
  eapply pure_split_rule'; introv Heqlen.
  lets H00: ecblist_p_decompose H_elp; eauto. 
  destruct H00 as (els1 & els2 & x' & H'').
  destruct H'' as (Hecbl1 & Hecbl2 & Hjo).
  hoare_assert_pure (x' = Vptr (v'41, Int.zero)).  
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg. 
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  hoare_split_pure_all; subst.
  rename v'41 into pb.

   assert (Hecbl' := Hecbl2).
   unfold ECBList_P in Hecbl'.
   fold ECBList_P in Hecbl'.
   destruct Hecbl' as (ptr & Hptr & Hecbetbl & Hex).
   inverts Hptr. 
   destruct Hex as (Hrpetbl & absmq & mqls' & v'' & Helptr & Hjo' & Hrlh & Hecbl20).
   unfold V_OSEventListPtr in Helptr.

  hoare_assert_pure (Int.eq i1 ($ OS_EVENT_TYPE_SEM) = true).
  { destruct (Int.eq i1 ($ OS_EVENT_TYPE_SEM)) eqn: eq1; auto.
     inverts Helptr.
     get_hsat Hsat.
     sep_lifts_trms_in Hsat AEventData.
     eapply semacc_eventtype_neq_sem in Hsat; eauto.
     sep split in Hsat.
     unfold get in Hget; unfold EcbMap in Hget.
     rewrite Hget in *.
     false. eapply H1; eauto.
     go.
   }
  eapply pure_split_rule'; introv Heqt.
  (* false If (ptr ′ .. OSEventType !=ₑ ′ OS_EVENT_TYPE_SEM)*)
  hoare forward.
  go.
  pure_auto.
  pure_auto.
  rewrite Heqt.
  hoare_split_pure_all.
  simpl in H1.
  change (Int.notbool Int.one) with Int.zero in H1.
  simpljoin.
  tryfalse.
  apply hoare_disj_afalseP_l_pre.
  hoare_split_pure_all.
  clear H1.
  apply semacc_int_eq_true in Heqt; subst.
  (* tp = OS_EVENT_TYPE_SEM *)
  hoare_assert_pure (exists wls, v'36 = DSem i2 /\ absmq = (abssem i2, wls)).  
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat AEventData.
    eapply semacc_triangle_sem in Hsat; eauto.
    2: go.
    sep split in Hsat.
    auto.
  }
  hoare_split_pure_all.
  destruct H1 as (Heq1 & Heq2); subst.
  lets Hget': Hjo'. eapply join_sig_get in Hget'; eauto.
  lets Hget'': Hget'. eapply join_get_r in Hget''; eauto.
  unfold get in Hget, Hget', Hget''; unfold EcbMap in Hget, Hget', Hget''.
  rewrite Hget in Hget''; inverts Hget''.
  rename v'5 into wls.

  eapply seq_rule.
  (* IF (ptr ′ .. OSEventGrp !=ₑ ′ 0){tasks_waiting ′ =ₑ ′ 1}
     ELSE {tasks_waiting ′ =ₑ ′ 0};ₛ *) 
  eapply lzh_if_else_rule.
  introv Hsat.
  sep get rv.
  go.
  pure_auto.
  pure_auto.
  (* branch with tasks_waiting ′ =ₑ ′ 1 *)
  hoare forward.
  (* branch with tasks_waiting ′ =ₑ ′ 0 *)
  hoare forward.

  eapply backward_rule1.
  introv Hsat.
  destruct Hsat as [Hs1 | Hs2].
  apply sep_pure_split in Hs1; destruct Hs1 as (Hinjs & Hs1).
  sep_lifts_trms_in Hs1 Apure.
  apply sep_pure_split in Hs1; destruct Hs1 as (Hinjs' & Hs1).
  match type of Hs1 with
    _ |= <|| ?ss ||> ** LV tasks_waiting @ char_t |-> _ ** ?P =>
    instantiate
      (1:=EX v', [| Int.eq i0 Int.zero = false /\ v' = Vint32 (Int.repr 1)
                    \/ Int.eq i0 Int.zero = true /\ v' = Vint32 Int.zero |]
                   ** <|| ss ||> ** LV tasks_waiting @ char_t |-> v' ** P)
  end.
  destruct Hinjs as (Hinj1 & _ & _).
  destruct (Int.eq i0 ($ 0)) eqn: Ei.
  simpl in Hinj1. 
  change (Int.notbool Int.one) with Int.zero in Hinj1.
  false.
  exists (Vint32 (Int.repr 1)). 
  sep pauto. 
  apply sep_pure_split in Hs2; destruct Hs2 as (Hinjs & Hs2). 
  sep_lifts_trms_in Hs2 Apure.
  apply sep_pure_split in Hs2; destruct Hs2 as (Hinjs' & Hs2).   
  destruct Hinjs as [Hinj1 | Hinj2].
  destruct (Int.eq i0 ($ 0)) eqn: Ei; 
    simpl in Hinj1.
  exists (Vint32 Int.zero).
  sep pauto.
  change (Int.notbool Int.zero) with Int.one in Hinj1.
  inverts Hinj1. 
  clear -Hinj2. false. 
  destruct (Int.eq i0 ($ 0)); simpl in Hinj2.
  change (Int.notbool Int.one) with Int.zero in Hinj2; inverts Hinj2.
  change (Int.notbool Int.zero) with Int.one in Hinj2; inverts Hinj2.
  (* end of if statement on "ptr ′ .. OSEventGrp !=ₑ ′ 0" *)  
  hoare_split_pure_all.
  rename H1 into Hcond1.

  fold_aux.

  (*WHILE (ptr ′ .. OSEventGrp !=ₑ ′ 0) *)

  (*1: remember irrelevant sep-conjunctions*)
  hoare_lifts_trms_pre (
      Aop, Astruct (pb, Int.zero), Aarray v'37, AEventData, AOSMapTbl, AOSUnMapTbl, AOSTCBPrioTbl,
      AOSTCBList, AOSRdyTblGrp, tcbdllflag, x, ptr, llsegobjaux
    ).
  hoare remember (1::2::3::4::5::6::7::8::9::10::11::12::13::nil)%nat pre. 
  protect HeqH1.
  unfold AOSTCBList.
  hoare unfold.
  rename v'16 into tcbls.
  rename v'8 into tcb_head.
  rename v'36 into tcb_tail.
  rename v'10 into tcbvl_l.
  rename v'11 into tcbvl_ct.
  rename v'12 into tcbvl_r. 
  rename v'13 into rtbl.
  rename v'14 into rgrp.

  destruct Hrlh as (_ & Hrh_ecb).
  simpl in Hrh_ecb.
  destruct Hrh_ecb as (Hcnt_wl_nil & Hcnt_wl_not_nil).
  rename v'15 into els.
  rename v'22 into ptls.

  rename i2 into n.

  (*2: get the while loop inv into the pre-condition,
    so the pre-condition after the while statement
    can be correctly instantiated
   *)
  eapply backward_rule1 with (p := (*below is the loop inv*)
       (EX etbl' tcbvl_l' tcbvl_r' tcbvl_ct' rtbl' rgrp' egrp subwl vx tail tcbls_l' tcbls_r',
  <|| spec_code_cons (kobjdel (Vptr (pb, Int.zero) :: nil)) v'1 ||>  **
  LV x @ Int8u |-> vx **
  AOSMapTbl **
  AOSUnMapTbl **
  AOSTCBPrioTbl v'7 rtbl' (set_tls_rdy subwl tcbls) ptls vhold_addr **
  GV OSTCBList @ OS_TCB ∗ |-> tcb_head **
  tcbdllseg tcb_head Vnull tail (Vptr ct) tcbvl_l' **
  GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
  tcbdllseg (Vptr ct) tail tcb_tail Vnull (tcbvl_ct' :: tcbvl_r') **
  [| TcbMod.join tcbls_l' tcbls_r' (set_tls_rdy subwl tcbls) |] **
  [| TCBList_P tcb_head tcbvl_l' rtbl' tcbls_l' |] **
  [| TCBList_P (Vptr ct) (tcbvl_ct' :: tcbvl_r') rtbl' tcbls_r' |] **
  [| RH_TCBList_ECBList_P (set els (pb, Int.zero) (abssem n, (remove_wls subwl wls))) (set_tls_rdy subwl tcbls) ct |] **
  tcbdllflag tcb_head (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') **
  llsegobjaux tcb_head Vnull (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') locmp ptrmp V_OSTCBNext **
  AOSRdyTblGrp rtbl' rgrp' **
  Astruct (pb, Int.zero) OS_EVENT
    (V$ OS_EVENT_TYPE_SEM :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: v'' :: Vint32 i :: x4 :: nil) **
  Aarray v'37 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl' **
  AEventData
    (V$ OS_EVENT_TYPE_SEM :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: v'' :: Vint32 i :: x4 :: nil)
    (DSem n) **
   LV ptr @ OS_EVENT ∗ |-> Vptr (pb, Int.zero) **  H1 **
     [| (RL_Tbl_Grp_P etbl' (Vint32 Int.zero)  /\ array_type_vallist_match Tint8 etbl' /\
          egrp = Int.zero /\ 
        ( ( subwl = nil \/ (forall t : Modules.tid, In t subwl -> In t wls)) /\ remove_wls subwl wls = nil) /\
         length etbl' = ∘ OS_EVENT_TBL_SIZE  /\(* egrp = 0, get out of the loop *)
         ECBList_P v'9 Vnull
           (v'26 ++
            ((V$ OS_EVENT_TYPE_SEM
              :: Vint32 Int.zero :: Vint32 n :: x0 :: x1 :: v'' :: Vint32 i :: x4 :: nil, etbl',petbl) :: nil) ++
            v'33) (v'34 ++ (DSem n :: nil) ++ v'35) 
            (set els (pb, Int.zero) (abssem n, nil)) (set_tls_rdy wls tcbls)) \/
        (is_subl subwl wls /\
         RL_Tbl_Grp_P etbl' (Vint32 egrp)  /\ array_type_vallist_match Tint8 etbl' /\
         egrp <> Int.zero /\ Int.unsigned egrp <= 255 /\  length etbl' = ∘ OS_EVENT_TBL_SIZE  /\(* egrp <> 0, still in the loop *)
         ECBList_P v'9 Vnull
           (v'26 ++
            ((V$ OS_EVENT_TYPE_SEM
              :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: v'' :: Vint32 i :: x4 :: nil, etbl',petbl) :: nil) ++
            v'33) (v'34 ++ (DSem n :: nil) ++ v'35) 
                        (set els (pb, Int.zero) (abssem n, (remove_wls subwl wls))) 
                        (set_tls_rdy subwl tcbls)) |]
       )).
 introv Hsat.
assert (Hegrp_case: i0 = Int.zero \/ i0 <> Int.zero) by tauto.
destruct Hegrp_case as [Hegrp_zero | Hegrp_nzero].
(* case1: egrp = 0*)
subst.
assert (Hwls: wls = nil).
{ eapply Grp_eq_zero_imp_wl_nil; eauto. }
subst wls.
assert(Hels: set els (pb, Int.zero) (abssem n, nil) = els ).
{ eapply EcbMod.get_set_same; eauto. }
do 7 eexists.
exists (nil: list Modules.tid).
do 4 eexists.
rewrite remove_wls_nil.
rewrite Hels.
rewrite set_tls_rdy_nil.
sep pauto; eauto.
sep cancel (tcbdllseg tcb_head).
sep cancel tcbdllseg.
sep cancel Aop.
sep cancel AOSTCBPrioTbl.
sep cancel AOSRdyTblGrp.
sep cancel tcbdllflag.
sep cancel llsegobjaux.
left.
splits; eauto.
(* case2: egrp <> 0 *)
assert (Hwls: wls <> nil).
{ eapply Grp_eq_nz_imp_wl_not_nil; eauto. }
assert(Hels: set els (pb, Int.zero) (abssem n, (remove_wls nil wls)) = els ).
{ eapply EcbMod.get_set_same; eauto. }
do 7 eexists.
exists (nil: list Modules.tid).
do 4 eexists.
rewrite Hels.
rewrite set_tls_rdy_nil.
assert (His_subl_nil: is_subl nil wls).
{  eapply nil_is_subl; eauto. }
sep pauto; eauto.
sep cancel (tcbdllseg tcb_head).
sep cancel tcbdllseg.
sep cancel Aop.
sep cancel AOSTCBPrioTbl.
sep cancel AOSRdyTblGrp.
sep cancel tcbdllflag.
sep cancel llsegobjaux.
right.
splits; eauto.
 (*3: apply the 'seq_rule' to get the while statement
    off the remaining statements, then apply the 'while_rule'
   *)
eapply seq_rule.
(*4: prove the condition expression of while is legal *)
eapply while_rule with (tp := Int32u).
introv Hsat.
sep pauto. sep get rv.
destruct H38 as [Hegrp_zero | Hegrp_nz]; mytac; go.
clear; simpl; pure_auto.
clear; simpl; pure_auto.
(*prove the condition expression of while is legal *)
(*Aistrue (ptr ′ .. OSEventGrp !=ₑ ′ 0)*)

(*5: the cond-expr of while hold implies the right part
    of the loop-inv*)
  eapply backward_rule1.
  introv Hsat.
  instantiate (1:= 
   (EX (etbl' : list val) (tcbvl_l' tcbvl_r' : list vallist)
           (tcbvl_ct' rtbl' : vallist) (rgrp' : val) (egrp : int32)
           (subwl : list addrval) (vx tail : val) (tcbls_l' tcbls_r' : TcbMod.map),
         [|
             is_subl subwl wls /\
             RL_Tbl_Grp_P etbl' (Vint32 egrp) /\
             array_type_vallist_match char_t etbl' /\
             egrp <> Int.zero /\
             Int.unsigned egrp <= 255 /\
             length etbl' = ∘ OS_EVENT_TBL_SIZE /\
             ECBList_P v'9 Vnull
               (v'26 ++
                ((V$ OS_EVENT_TYPE_SEM
                  :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: v'' :: Vint32 i :: x4 :: nil , etbl',
                 petbl) :: nil) ++ v'33) (v'34 ++ (DSem n :: nil) ++ v'35)
               (set els (pb, Int.zero) (abssem n, remove_wls subwl wls))
               (set_tls_rdy subwl tcbls)|] **
            <|| spec_code_cons (kobjdel (Vptr (pb, Int.zero) :: nil)) v'1 ||>  **
           LV x @ char_t |-> vx **
           AOSMapTbl **
           AOSUnMapTbl **
           AOSTCBPrioTbl v'7 rtbl' (set_tls_rdy subwl tcbls) ptls vhold_addr **
           GV OSTCBList @ OS_TCB ∗ |-> tcb_head **
           tcbdllseg tcb_head Vnull tail (Vptr ct) tcbvl_l' **
           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
           tcbdllseg (Vptr ct) tail tcb_tail Vnull (tcbvl_ct' :: tcbvl_r') **
           [|TcbMod.join tcbls_l' tcbls_r' (set_tls_rdy subwl tcbls)|] **
           [|TCBList_P tcb_head tcbvl_l' rtbl' tcbls_l'|] **
           [|TCBList_P (Vptr ct) (tcbvl_ct' :: tcbvl_r') rtbl' tcbls_r'|] **
           [|RH_TCBList_ECBList_P
               (set els (pb, Int.zero) (abssem n, remove_wls subwl wls))
               (set_tls_rdy subwl tcbls) ct|] **
           tcbdllflag tcb_head (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') **
           llsegobjaux tcb_head Vnull (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') locmp ptrmp
             V_OSTCBNext **
           AOSRdyTblGrp rtbl' rgrp' **
           Astruct (pb, Int.zero) OS_EVENT
             (V$ OS_EVENT_TYPE_SEM
              :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: v'' :: Vint32 i :: x4 :: nil) **
           Aarray v'37 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl' **
           AEventData
             (V$ OS_EVENT_TYPE_SEM
              :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: v'' :: Vint32 i :: x4 :: nil)
             (DSem n) **
           LV ptr @ OS_EVENT ∗ |-> Vptr (pb, Int.zero) **
           H1)
 ).
  destruct Hsat as (Hsat & Histrue).
  sep normal in Hsat. sep destruct Hsat.
  (* do 12 (eapply aexists_prop; [idtac| exact Hsat]; clear Hsat; introv Hsat).
  sep_lifts_trms_in Hsat (ECBList_P).
  match type of Hsat with
    _ |= [| ?p1 \/ ?p2 |] ** <|| ?ss ||> ** ?P =>
    instantiate
      (1:= fun _ => ([| p2 |] ** <|| ss ||> ** P))
  end. *)
  lets Hcp: aconj_intro Hsat Histrue.
  eapply sep_aconj_r_aistrue_to_astar in Hcp; eauto.
  2:{ introv Hsat'. sep get rv.
        sep split in Hsat'.
        destruct H39 (* 5 *) as [Hegrp_zero | Hegrp_nz]; mytac; go.
        clear; simpl; pure_auto.
        clear; simpl; pure_auto. }
  sep_lifts_trms_in Hcp val_inj.
  eapply sep_pure_split in Hcp; destruct Hcp as (Hif & _).
  sep pauto; eauto.
  destruct H38 (* 4 *); auto.
  simpljoin.
  change (Int.eq Int.zero ($ 0)) with true in H39.
  simpl in H39.
  change (Int.notbool  Int.one) with Int.zero in H39; tryfalse.
  (*x ′ =ₑ ′ OS_STAT_SEM;ₛ
     OS_EventTaskRdy (­ptr ′, 〈 (Void) ∗ 〉 NULL, x ′­)*)
  unprotect HeqH1.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
  hoare forward.
  (* OS_EventTaskRdy (­ptr ′, 〈 (Void) ∗ 〉 NULL, x ′­) *)
  unfold AOSTCBPrioTbl.
  hoare normal pre.
  repeat (apply ex_intro_rule; intro).
  hoare_split_pure_all.
(*   subst H1. *)
  eapply conseq_rule; [eauto | idtac | idtac].
  Focus 2.

hoare forward.
{
sep cancel Aie.
sep cancel Ais.
sep cancel Acs.
sep cancel Aisr.
sep cancel Aop.
sep cancel AOSRdyTblGrp.
sep cancel p_local.
unfold AEventNode.
unfold AOSEvent.
unfold node.
unfold AOSEventTbl.
sep normal.
sep eexists.
sep cancel AOSPostEventTbl.
sep cancel AEventData.
sep pauto;eauto.
sep cancel Aarray.
sep cancel Astruct.
eapply tcbdllseg_compose.
sep cancel tcbdllseg.
sep cancel tcbdllseg.
exact_s.
splits; auto. go.
}
unfold V_OSEventGrp; simpl; split; eauto.
simpl; eauto.
simpl; eauto.
simpl; eauto.
eapply TCBList_P_Combine; [idtac | idtac | eauto | eauto].
eapply tcbdllseg_get_last_tcb_ptr.
instantiate (4:=s).
sep cancel (tcbdllseg tcb_head).
eauto.
eauto.
(* R_ECB_ETbl_P *)
lets H_elp': e1.
eapply ecblist_p_decompose in H_elp'; eauto.
destruct H_elp' as (els1' & els2' & x' & H'').
destruct H'' as (Hecbl1' & Hecbl2' & Hjo'').
assert (Hx_eq: x' = Vptr (pb, Int.zero)).
  {
    get_hsat Hsat.
    sep_lifts_trms_in Hsat evsllseg.
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  subst x'. 
  simpl in Hecbl2'.
  mytac.
  inverts H47; auto.
  (* end of  R_ECB_ETbl_P *)
  eauto.
  eauto.
  eapply tcbdllseg_combine_ptr_in_tcblist with (s:= s).
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  eauto.
  auto.
  pure_auto.

  intros.
  sep auto.

  intros.
  sep auto.

  introv Hsat.
  unfold OS_EventTaskRdyPost in Hsat.
  unfold OS_EventTaskRdyPost' in Hsat.
  unfold getasrt in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep_lifts_trms_in Hsat (Aop, A_dom_lenv, A_isr_is_prop).
  sep remember (1 :: 2 :: 3 :: nil)%nat in Hsat.
  subst.
  unfold AEventNode in Hsat.
  unfold AOSEvent in Hsat.
  unfold node in Hsat.
  unfold AOSEventTbl in Hsat.
  sep normal in Hsat.
  sep destruct Hsat.
  sep split in Hsat.
  inverts H80.
  simpl nth_val in *.
  inverts H71; inverts H72; inverts H73.
  substs.
  rename x12 into egrp.
  rename x13 into egrp'.
  simpl update_nth_val in *.
  mytac.
  inverts H1.
  rename x53 into pb.
  inverts H45. (* V_OSEventGrp .... *)
  rewrite H14 in H44; inverts H44. (* id_addrval' OSEventTbl *)
  inverts H48. (* V_OSPostEventGrp ... *)
  rewrite H17 in H47; inverts H47. (* id_addrval' OSPostEventTbl *)
  (* renameing *)
  rename ct into ctcb.
  rename x47 into htcb_addr. (* highest tcb in pevent waitlist *)
  rename H53 into Hhtcb.
  rename H74 into Hctcb_in_tcblist.
  rename x22 into tcblist_head.
  rename v'10 into tcblist_seg1.
  rename v'12 into ctcb_node.
  rename v'11 into tcblist_seg2.
  rename H57 into Hrel_et.

  (* ** ac: Print prio_in_tbl. *)
  rename x7 into ptbl'.
  rename x8 into rtbl'.
  rename v'16 into subwl.
  rename x14 into etbl'.
  (* ** ac: Print TCBList_P. *)

  remember (tcblist_seg1 ++ ctcb_node :: tcblist_seg2) as tcblist.

  (* ** ac: Print priority. *)
  (* ** ac: Print rel_edata_tcbstat. *)
  rename x42 into hprio.
  assert (Hp: exists hprio', hprio = Vint32 hprio').
  {
    clear - H65. (* struct_type_vallist_match *)
    (* ** ac: SearchAbout struct_type_vallist_match. *)
    (* ** ac: Print struct_type_vallist_match. *)
    rename H65 into H.
    unfold struct_type_vallist_match in H.
    unfold OS_TCB_flag in H.
    unfold struct_type_vallist_match' in H.
    mytac.
    clear - H5.
    (* ** ac: SearchAbout (rule_type_val_match Int8u _). *)
    apply rule_type_val_match_int8u_elim in H5.
    mytac.
  }
  destruct Hp as (x & Hp);
  subst hprio.
  rename x into hprio.
  
  rename x36 into hnext.
  rename x43 into htcbx.
  rename x44 into htcby.
  rename x45 into hbitx.
  rename x46 into hbity.

  assert (Hhtcb_get: exists st m, get (set_tls_rdy subwl tcbls) (htcb_addr, Int.zero) = Some (hprio, st, m)).
  {
    eapply tcblist_get_TCBList_P_get.
    eauto.
    pure_auto.
    eauto.
  }
  destruct Hhtcb_get as (st & msg & Hhtcb_get).
  
  assert (Hs1: Int.unsigned x30 <= 7). 
  {
    clear - H80 H58.
    apply osunmapvallist_prop in H80.
    mytac.
    rewrite H in H58.
    inverts H58.
    auto with zarith.
  }
  assert (Hs2: Int.unsigned x31 <= 255). 
  {
    clear - H59 Hs1 H73 H81.
    assert (Z.to_nat (Int.unsigned x30) < length etbl')%nat. 
    {
      rewrite H81; unfold OS_EVENT_TBL_SIZE.
      mauto.
    }
    lets Hx: array_int8u_nth_lt_len H73 H.
    mytac.
    rewrite H59 in H0.
    inverts H0.
    auto.
  }
  assert (Hs3: Int.unsigned x29 <= 7). 
  {
    clear - H60 Hs2.
    lets Hx: osunmapvallist_prop Hs2.
    mytac.
    rewrite H in H60; inverts H60.
    auto with zarith.
  }

  lets H_elp_subwl: H88.
  eapply ecblist_p_decompose in H88; eauto. 
  destruct H88 as (els1_new & els2_new & x' & H'').
  destruct H'' as (Hecbl1_new & Hecbl2_new & Hjo_new).
  assert (Hx': x' = Vptr (pb, Int.zero)).
  {
    sep_lifts_trms_in Hsat evsllseg.
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  subst x'.
  lets Hcp: Hecbl2_new.
  simpl in Hcp.
  mytac.
  inverts H1. (* Vptr (pb, ...) = Vptr x *)
  inverts H47.
  assert (Hx2: x2 = (abssem n, remove_wls subwl wls)). 
  {
    eapply EcbMod.join_sig_get in H48.
    eapply EcbMod.join_get_r in H48; eauto.
    rewrite EcbMod.map_get_set in H48.
    inverts H48. auto.
  }
  subst x2. 
  destruct H53 as (_ &  Hrh_ecb_new). 
  rename H48 into Hjo_sig_new. 
  rename H57 into Hecb_right_new.
  clear H44. (* R_ECB_ETbl_P (pb, Int.zero) ... *)

  generalize Hhtcb_get; intro Hhtcb_join.
  apply map_join_get_sig in Hhtcb_join.
  destruct Hhtcb_join as (tcbls' & Hhtcb_join).
  remember (remove_wls subwl wls) as pwls.
  assert (Hpre: pwls <> nil /\ GetHWait (set_tls_rdy subwl tcbls) pwls (htcb_addr, Int.zero) /\
                TcbMod.get (set_tls_rdy subwl tcbls) (htcb_addr, Int.zero) = Some (hprio, st, msg) /\
                hprio = ((x30<<ᵢ$ 3) +ᵢ  x29)). (* change x28,x29 -> x29,x30 *)
  {
    apply map_join_get_sig in Hhtcb_get.
    destruct Hhtcb_get.
    Require Import sempost_pure.
    (* ** ac: Check post_exwt_succ_pre_sem. *)
    eapply post_exwt_succ_pre_sem; eauto.
  }
  destruct Hpre as (Hpwls_not_nil & Hhwait & Hhtcb_get' & Hhprio_eq).
  subst hprio.

(* ** ac: Check sem_post_get_tcb_stat. *)
  rename H79 into Htcblist_p.
  lets Hhtcb_node: TCBList_P_tcblist_get_TCBNode_P Htcblist_p Hhtcb Hhtcb_get. 
  generalize Hhtcb_node; intro Htmp.
  unfolds in Htmp.
  mytac.
  inverts H1; inverts H44.

  rename H47 into Hh_tcbblk.
  rename H48 into Hh_tcbstat.
  unfolds in Hh_tcbblk.
  mytac.
  inverts H1.
  inverts H44; inverts H47; inverts H48; inverts H53; inverts H57; inverts H92.

  rename x30 into p1.
  rename x29 into p2.
  remember ((p1<<ᵢ$ 3) +ᵢ  p2) as hprio.

  assert (Hx: x9 = $ OS_STAT_SEM).
  {
    clear - Hrel_et.
    unfolds in Hrel_et.
    auto.
  }
  subst x9.
  assert (Hp1: (hprio >>ᵢ $ 3) =  p1).
  {
    subst hprio.
    clear - Hs1 Hs2 Hs3.
    clear Hs2.
    mauto.
  }
  assert (Hp2: hprio &ᵢ ($ 7) = p2).
  {
    subst hprio.
    clear - Hs1 Hs3.
    mauto.
  } 
  assert (Hs4: Int.unsigned x48 <= 255). (* change x47 -> x48 *)
  { 
    clear - Hs1 H50 H56 H55. 
    assert (Z.to_nat (Int.unsigned p1) < length rtbl')%nat.
    {
      rewrite H56.
      unfold OS_RDY_TBL_SIZE.
      mauto.
    }
    lets Htmp: array_int8u_nth_lt_len H55 H. 
    mytac.
    rewrite H50 in H0. 
    inverts H0.
    auto.
  }
  (* ** ac: Check set_node_elim. *)
  assert (Htmp: x32 = $ 1 <<ᵢ p2).
  {
    eapply math_mapval_core_prop.
    clear - Hs3.
    mauto.
    auto.
  }
  subst x32.
  assert (Hno_dup: R_Prio_No_Dup (set_tls_rdy subwl tcbls)).
  {
    clear - H77.
    unfolds in H77.
    mytac.
  }
  sep_lifts_trms_in Hsat (tcbdllseg).
  eapply set_node_elim in Hsat; eauto.
  2: { eapply TCBNode_P_set_rdy with (row := x48); eauto.
          rewrite Hp1. 
          eapply nth_val'2nth_val; eauto.  }
   2:{ unfold rtbl_set_one_bit.
         rewrite Hp1; rewrite Hp2.
         repeat eexists; eauto.  }
   2: {  unfolds. unfold V_OSTCBNext; simpl. auto. }
   sep normal in Hsat.
   sep destruct Hsat.
   sep split in Hsat.
   rename H1 into Htcblist_new.
   rename H44 into Htcbjoin_new_set.
   rename H47 into Htcblist_p_new_left.
   rename H48 into Htcblist_p_new_right.
   assert (Htcbjoin_new_set': TcbMod.join x8 x9
                     (set_tls_rdy ((htcb_addr, Int.zero) :: nil)
                          (set_tls_rdy subwl tcbls) )).
  { clear -Htcbjoin_new_set Hhtcb_get.
     simpl set_tls_rdy.
     unfold get in *; unfold TcbMap in *.
      rewrite Hhtcb_get. auto.
    }
   clear Htcbjoin_new_set; rename Htcbjoin_new_set' into Htcbjoin_new_set.
   rewrite set_tls_rdy_succ_eq in Htcbjoin_new_set.
   assert (Hin_pwls: In (htcb_addr, Int.zero) (remove_wls subwl wls)).
   { clear -Hhwait. funfold Hhwait. mytac. }
   assert (Hst: exists xl,st = wait (os_stat_sem (pb, Int.zero)) xl).
  {  eapply rh_tcblist_ecblist_p_post_exwt_aux_sem ;eauto. }
  destruct Hst as (st_t & Hst). 
  subst st.
   assert (Hr_ptbl_new:
                 R_PrioTbl_P ptbl' (set_tls_rdy ((htcb_addr, Int.zero) :: (subwl: list tid)) tcbls) vhold_addr).
   { rewrite <- set_tls_rdy_succ_eq with (wls:= (subwl :list tid)) (tls := tcbls).
     simpl set_tls_rdy at 1.
      unfold get in Hhtcb_get; unfold TcbMap in Hhtcb_get.
     rewrite Hhtcb_get.
     eapply r_priotbl_p_set_hold; eauto.
    }
   assert (Hrh_tls_els_new: RH_TCBList_ECBList_P
    (set els (pb, Int.zero) (abssem n, remove_wls ((htcb_addr, Int.zero) :: subwl) wls))
    (set_tls_rdy ((htcb_addr, Int.zero) :: (subwl: list tid)) tcbls) ctcb).
  { rewrite <- remove_wls_succ_set_els_eq with (st':= (abssem n)).
     rewrite <- set_tls_rdy_succ_eq with (wls:= (subwl :list tid)) (tls := tcbls).
     simpl set_tls_rdy at 1.
      unfold get in Hhtcb_get; unfold TcbMap in Hhtcb_get.
     rewrite Hhtcb_get.
     eapply rh_tcblist_ecblist_p_post_exwt_sem; eauto.
   }
   assert (H_elp_new: ECBList_P v'9 Vnull
           (v'26 ++
            ((V$ OS_EVENT_TYPE_SEM
              :: Vint32 egrp' :: Vint32 n :: x0 :: x1 :: x5 :: Vint32 i :: x4 :: nil, 
             (update_nth_val (Z.to_nat (Int.unsigned p1)) etbl'
                       (Vint32 (x31&ᵢInt.not ($ 1<<ᵢp2)))),x16) :: nil) ++
            v'33) (v'34 ++ (DSem n :: nil) ++ v'35) 
           (set els (pb, Int.zero) (abssem n, (remove_wls ((htcb_addr, Int.zero) :: subwl) wls))) 
           (set_tls_rdy ((htcb_addr, Int.zero) :: subwl) tcbls) ).
   {
      rewrite <- remove_wls_succ_set_els_eq with (st':= (abssem n)).
      rewrite <- set_tls_rdy_succ_eq with (wls:= (subwl :list tid)) (tls := tcbls).
     simpl set_tls_rdy at 1.
     rewrite Hhtcb_get'.
     eapply ecblist_p_post_exwt_hold_sem; eauto.
     eapply rl_etbl_ptbl_p; auto; eauto.
     subst hprio; auto.
     clear -Hs3. mauto.
     unfold RLH_ECBData_P.
     split; auto.
    }
   lets H_elp_cp: H_elp_new.
  eapply ecblist_p_decompose in H_elp_cp; eauto. 
  destruct H_elp_cp as (els1_new' & els2_new' & x' & H'').
  destruct H'' as (Hecbl1_new' & Hecbl2_new' & Hjo_new').
  assert (Hx': x' = Vptr (pb, Int.zero)).
  {
    sep_lifts_trms_in Hsat evsllseg.
    eapply ecblistp_evsllseg_tlsame in Hsat; eauto.
  }
  subst x'.
  lets Hcp: Hecbl2_new'.
  remember ((htcb_addr, Int.zero) :: subwl) as subwl'.
   simpl in Hcp.
   mytac.
   inverts H1.
   inverts H48. (* V_OSEventListPtr ... *)
   assert (Hx0: x14 = (abssem n, remove_wls ((htcb_addr, Int.zero) :: subwl) wls)).
   {
   eapply EcbMod.join_sig_get in H53.
   eapply EcbMod.join_get_r in H53;eauto.
   rewrite EcbMod.map_get_set in H53.
   inverts H53. auto. }
   subst x14.
   destruct H57 as (_ & Hrh_ecb_new').
   rename H53 into Hjo_sig_new'.
   rename H79 into Hecb_right_new'.
   rename H44 into Hr_ecb_etbl_new'.
   rename H47 into Hr_ecb_petbl_new'.
   lets Hgete_new: EcbMod.join_sig_get Hjo_sig_new'.
   eapply EcbMod.join_get_r in Hgete_new; eauto.
   assert (His_subl_part: (forall t, In t ((htcb_addr,Int.zero) :: subwl) -> In t wls) 
                                               /\ (forall t, ~(In t wls) -> ~ (In t ((htcb_addr,Int.zero) :: subwl)))
                                               /\ NoDup ((htcb_addr,Int.zero) :: subwl) ).
   { clear -H34 Hin_pwls.
     unfold is_subl in *.
     mytac.
     splits; intros.
     eapply in_remove_wls in Hin_pwls.
     simpl in H3.
     destruct H3; try subst; auto.
     rewrite not_in_cons.
     assert (t = (htcb_addr, Int.zero)  \/ t <> (htcb_addr, Int.zero) ) by tauto.
      eapply in_remove_wls in Hin_pwls.
     destruct H4. subst; tryfalse.
     split; auto.
     eapply NoDup_cons; eauto.
     eapply in_remove_wls_nin; eauto.
    }
    destruct His_subl_part as (His_subl_part1 & His_subl_part2 & His_subl_part3).
    (* change tcbdllflag *)
    sep_lifts_trms_in Hsat (tcbdllflag).
    eapply tcbdllflag_set_node in Hsat; eauto.
    2: { unfolds. unfold V_OSTCBNext; simpl. auto. }
    (* end of change tcbdllflag *)
    (* remain llsegobjaux *)
    sep_lifts_trms_in Hsat (llsegobjaux).
    unfold llsegobjaux in Hsat.
    eapply llsegobjaux_set_node in Hsat; eauto.
    2: { unfolds. unfold V_OSTCBNext; simpl. auto. }
   (* end of tcbllsegobjaux *)
  exists (update_nth_val (Z.to_nat (Int.unsigned p1)) etbl'
               (Vint32 (x31&ᵢInt.not ($ 1<<ᵢp2)))).
  exists x x2 x6.
  exists (update_nth_val (Z.to_nat (Int.unsigned p1)) rtbl'
               (Vint32 (Int.or x48 ($ 1<<ᵢp2)))). (* new rtbl *)
  exists x11. (* new rgrp *)
  exists egrp'. (* new egrp *)
  exists ((htcb_addr, Int.zero) :: subwl).
  exists (V$ OS_STAT_SEM).
  exists x7 x8 x9.
  sep auto.
  { assert (Hegrp'_case: egrp' = Int.zero \/ egrp' <> Int.zero) by tauto.
  destruct Hegrp'_case as [Hegrp'_eq | Hegrp'_neq];
  [left | right].
  (* case1 : after OS_EventTaskRdy, will get out of loop *)
  subst egrp'.
  assert (Hpwls'_eq: remove_wls ((htcb_addr, Int.zero) :: subwl) wls = nil).
  { eapply Grp_eq_zero_imp_wl_nil with (etbl:= (update_nth_val (Z.to_nat (Int.unsigned p1)) etbl'
       (Vint32 (x31&ᵢInt.not ($ 1<<ᵢp2)))) ); eauto.
    rewrite update_nth_val_len_eq; eauto.
  }
  assert (Hsubwl_eq':  set_tls_rdy ((htcb_addr,Int.zero) :: subwl) tcbls 
                                               = set_tls_rdy wls tcbls).
  { assert (Heq: ((htcb_addr,Int.zero) :: subwl) ++ remove_wls ((htcb_addr, Int.zero) :: subwl) wls
                                = ((htcb_addr,Int.zero) :: subwl)).
     rewrite Hpwls'_eq. rewrite app_nil_end; auto.
     rewrite <- Heq.
     eapply set_tls_rdy_eq_alt_gen; eauto.
   }
  rewrite Hpwls'_eq in *.
  rewrite Hsubwl_eq' in *.
   splits; eauto.
  rewrite update_nth_val_len_eq; eauto.
   (* case 2 : after OS_EventTaskRdy, still in the loop *)
  assert (Hegrp'_range: Int.unsigned egrp' <= 255).
  {
   clear -H67.
  simpl in H67.
  destruct H67 as (_ & H & _).
  eapply int_true_le255; eauto.
   }
   splits; eauto.
   unfold is_subl.
  splits; auto.
  simpl length.
  eapply length_lt_succ; eauto.
   eapply Grp_eq_nz_imp_wl_not_nil with (etbl:= (update_nth_val (Z.to_nat (Int.unsigned p1)) etbl'
       (Vint32 (x31&ᵢInt.not ($ 1<<ᵢp2)))) ); eauto.
  rewrite update_nth_val_len_eq; eauto.
  rewrite update_nth_val_len_eq; eauto.
   }
  rewrite Hp1 in *; rewrite Hp2 in *; eauto.
  rewrite Hp1 in *; rewrite Hp2 in *; eauto.
  (* end of OS_EventTaskRdy *)
  (* Aisfalse (ptr ′ .. OSEventGrp !=ₑ ′ 0) *)
  unprotect HeqH1.
  eapply backward_rule1.
  introv Hsat.
  instantiate (1:=
  (EX (etbl' : list val) (tcbvl_l' tcbvl_r' : list vallist)
           (tcbvl_ct' rtbl' : vallist) (rgrp' : val) (egrp : int32)
           (subwl : list addrval) (vx tail : val) (tcbls_l' tcbls_r' : TcbMod.map),
            <|| spec_code_cons (kobjdel (Vptr (pb, Int.zero) :: nil)) v'1 ||>  **
           LV x @ char_t |-> vx **
           AOSMapTbl **
           AOSUnMapTbl **
           AOSTCBPrioTbl v'7 rtbl' (set_tls_rdy subwl tcbls) ptls vhold_addr **
           GV OSTCBList @ OS_TCB ∗ |-> tcb_head **
           tcbdllseg tcb_head Vnull tail (Vptr ct) tcbvl_l' **
           GV OSTCBCur @ OS_TCB ∗ |-r-> Vptr ct **
           tcbdllseg (Vptr ct) tail tcb_tail Vnull (tcbvl_ct' :: tcbvl_r') **
           [|TcbMod.join tcbls_l' tcbls_r' (set_tls_rdy subwl tcbls)|] **
           [|TCBList_P tcb_head tcbvl_l' rtbl' tcbls_l'|] **
           [|TCBList_P (Vptr ct) (tcbvl_ct' :: tcbvl_r') rtbl' tcbls_r'|] **
           [|RH_TCBList_ECBList_P
               (set els (pb, Int.zero) (abssem n, remove_wls subwl wls))
               (set_tls_rdy subwl tcbls) ct|] **
           tcbdllflag tcb_head (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') **
           llsegobjaux tcb_head Vnull (tcbvl_l' ++ tcbvl_ct' :: tcbvl_r') locmp ptrmp
             V_OSTCBNext **
           AOSRdyTblGrp rtbl' rgrp' **
           Astruct (pb, Int.zero) OS_EVENT
             (V$ OS_EVENT_TYPE_SEM
              :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: v'' :: Vint32 i :: x4 :: nil) **
           Aarray v'37 (Tarray char_t ∘ OS_EVENT_TBL_SIZE) etbl' **
           AEventData
             (V$ OS_EVENT_TYPE_SEM
              :: Vint32 egrp :: Vint32 n :: x0 :: x1 :: v'' :: Vint32 i :: x4 :: nil)
             (DSem n) **
           LV ptr @ OS_EVENT ∗ |-> Vptr (pb, Int.zero) **
           H1 **
           [|RL_Tbl_Grp_P etbl' (Vint32 Int.zero) /\
             array_type_vallist_match char_t etbl' /\
             egrp = Int.zero /\
             ((subwl = nil \/ (forall t : tid, In t subwl -> In t wls)) /\
              remove_wls subwl wls = nil) /\
             length etbl' = ∘ OS_EVENT_TBL_SIZE /\
             ECBList_P v'9 Vnull
               (v'26 ++
                ((V$ OS_EVENT_TYPE_SEM
                  :: Vint32 Int.zero
                     :: Vint32 n :: x0 :: x1 :: v'' :: Vint32 i :: x4 :: nil, etbl',
                 petbl) :: nil) ++ v'33) (v'34 ++ (DSem n :: nil) ++ v'35)
               (set els (pb, Int.zero) (abssem n, nil)) (set_tls_rdy wls tcbls)|])
   ).
  destruct Hsat as (Hsat & Hisfalse).
  (* do 12 (eapply aexists_prop; [idtac| exact Hsat]; clear Hsat; introv Hsat).
  sep_lifts_trms_in Hsat (ECBList_P).
  match type of Hsat with
    _ |= [| ?p1 \/ ?p2 |] ** <|| ?ss ||> ** ?P =>
    instantiate
      (1:= fun _ => ([| p1 |] ** <|| ss ||> ** P))
  end. *)
  sep normal in Hsat; sep destruct Hsat.
  lets Hcp: aconj_intro Hsat Hisfalse.
  eapply sep_aconj_r_aisfalse_to_astar in Hcp; eauto.
  2:{ introv Hsat'.
        sep get rv.
        sep split in Hsat'.
        destruct H39 (* 5 *) as [Hegrp_zero | Hegrp_nz]; mytac; go.
        clear; simpl; pure_auto.
        clear; simpl. pure_auto.
      }
  sep_lifts_trms_in Hcp val_inj.
  eapply sep_pure_split in Hcp; destruct Hcp as (Hif & _).
  sep pauto; eauto.
  destruct H38 (* 4 *); auto.
  simpljoin.
  lets Heq: Int.eq_false H46.
  change ($ 0) with Int.zero in *.
  rewrite Heq in Hif.
  simpl in Hif.
  change (Int.notbool  Int.zero) with Int.one in Hif; destruct Hif; tryfalse.
  hoare unfold.

  assert (Hsubwl_eq':  set_tls_rdy v'16 tcbls 
                                               = set_tls_rdy wls tcbls).
  { assert (Heq: v'16 ++ remove_wls v'16 wls
                                = v'16).
     rewrite H45. rewrite app_nil_end; auto.
     assert (Hsubwl: v'16 = nil \/ v'16 <> nil) by tauto.
     destruct Hsubwl.
     subst. rewrite remove_wls_nil in H45.
     subst. auto.
     destruct H42. subst; tryfalse.
     rewrite <- Heq.
     eapply set_tls_rdy_eq_alt_gen; eauto.
   }
  rewrite Hsubwl_eq' in *.
  rewrite H45 in *.
  (* end of while loop *)
  hoare_assert_pure ((v'9 = (Vptr (pb, Int.zero)) /\ v'26 = nil
                                         \/ get_last_ptr v'26 = Some (Vptr (pb, Int.zero)))
                                     /\ length v'26 = length v'34).
  { get_hsat Hsat.
     sep_lifts_trms_in Hsat evsllseg.
     eapply evsllseg_aux in Hsat; eauto.
   }
  hoare_split_pure_all.
  destruct H1 as ( Hlptr & _).

  eapply backward_rule1.
  introv Hsat.
  eapply lzh_evsllseg_compose.
  sep cancel evsllseg.
  sep cancel evsllseg.
  unfold AEventNode.
  unfold_msg.
  sep normal.
  sep eexists.
  sep cancel AOSPostEventTbl.
  sep cancel Astruct.
  sep cancel Aarray.
  sep cancel AEventData.
  sep split; eauto.
  split; auto.
  go.
  unfolds; simpl; auto.
  eauto.
  eauto.

  (* OS_EventRemoveDel (­ pevent ′­);ₛ *)
  hoare forward.
  sep cancel Aie.
  sep cancel Ais.
  sep cancel Acs.
  sep cancel Aisr.
  sep cancel evsllseg.
  sep cancel Aop.
  sep cancel p_local.
  eauto.
  split; introv Hc.
  destruct Hlptr as [(Heq1 & Heq2) | Hlptr]; try subst; eauto.
  tryfalse.
  destruct Hlptr as [(Heq1 & Heq2) | Hlptr]; try subst; eauto.
  false. eapply Hc; auto.
  auto.
  simpl; auto.
  go.
  introv Hsat. sep auto.
  introv Hsat. sep auto.

  (* unfold post-condition of OS_EventRemove *)
  hoare unfold pre.
  rename v'63 into pb. 
  inverts H1. (* eq. for logic_val ... *)
  (* ptr ′ .. OSEventType =ₑ ′ OS_EVENT_TYPE_UNUSED;ₛ *)
  hoare forward.
  (* ptr ′ .. OSEventListPtr =ₑ OSEventFreeList ′;ₛ *)
  unfold AOSEventFreeList.
  hoare unfold.
  hoare_assert_pure (isptr v'21). (* ecbf_sllseg ... *)
  seg_isptr.
  hoare_split_pure_all.
  rename H1 into Hptr_fr.
  hoare forward.
  pure_auto.
  (* OSEventFreeList ′ =ₑ ptr ′;ₛ *)
  hoare forward.
  (* OSTCBCur ′ .. __OSTskPtr =ₑ NULL;ₛ *)
  hoare_lifts_trms_pre (llsegobjaux, p_local).
  eapply backward_rule1.
  introv Hsat.
  eapply tcbllsegobjaux_split3_join2_frm''.
  unfold AOSTCBList.
  sep pauto; eauto.
  sep cancel llsegobjaux.
  sep cancel p_local.
  sep cancel tcbdllseg.
  sep cancel tcbdllseg.
  eauto.

  hoare normal pre.
  hoare_ex_intro.
  hoare_split_pure_all.
  subst.

  hoare_assign_aux.
  unfold isptr; auto.
  fold_aux_ptr Vnull.

  (* absdata process *)
  assert (Hjomg: join els1 mqls' (merge els1 mqls')).
  {
    apply join_merge_disj.
    apply disj_sym.
    apply EcbMod.join_comm in Hjo.
    clear -Hjo Hjo'. 
    eapply join_join_disj_r; eauto. 
  }
  assert (Hjo_rm: join (merge els1 mqls') (sig (pb, Int.zero) (abssem i4, wls)) els).
  {
    clear - Hjo Hjo'.
    apply join_comm in Hjo'.
    eapply join_lib_aux.join_join_join_merge; eauto. 
  }
  assert (Hjo_rm': EcbMod.join (merge els1 mqls') (EcbMod.sig (pb, Int.zero) (abssem i4, nil))
  (set els (pb, Int.zero) (abssem i4, nil))).
  { clear -Hjo Hjo' Hjo_rm.
      lets Heq: EcbMod.map_set_sig (pb,Int.zero) (abssem i4, wls).
      rewrite <- Heq.
      eapply EcbMod.join_set_r; eauto.
      unfold EcbMod.indom.
      rewrite EcbMod.map_get_sig; eauto.
   }
  assert(Hget_ct: RH_CurTCB ct (set_tls_rdy wls tcbls)).
  { clear -H0.
     unfold RH_CurTCB in *.
     simpljoin.
     exists x.
     eapply set_tls_rdy_get_some; eauto.
   }
  assert (H_elp_new:
            ECBList_P v'49 Vnull (v'47++v'46) (v'43++v'44) (merge els1 mqls') (set_tls_rdy wls tcbls)).
  {
    casetac v'45 (nil: list os_inv.EventCtr) Hnil Hnnil.
    - lets H00: H49 Hnil.
      destruct H00 as (Heid & Heq' & Hnil').
      substs.
      assert (v'43 = nil /\ els1 = emp).
      { simpl in Heqlen.
         eapply eq_sym in Heqlen.
         rewrite length_zero_iff_nil in Heqlen.
         subst.
         unfold ECBList_P in Hecbl1. simpljoin1. splits; auto. }
      simpljoin1.
      lets Hlem: semdel_ecblist_ecbmod_get.
      change ($ 0) with Int.zero in *.
      lets Hcp: H44.
      eapply Hlem  in Hcp; eauto.
      eapply EcbMod.join_emp_eq in Hjo; subst.
      clear - Hcp Hjo_rm'.
      simpl app in *.
      rewrite jl_merge_emp' in *.
      simpljoin.
      assert (x = mqls').
      eapply EcbMod.join_unique_r; eapply EcbMod.join_comm; eauto.
      subst; auto.
    -
    lets H00: H61 Hnnil.
    destruct H00 as (Hv'eq & Hglp & Hupd).
    subst.
    lets Hlem: semdel_ecblist_ecbmod_get'.
    change ($ 0) with Int.zero in *.
    lets Hcp: H44.
    eapply Hlem  in Hcp; eauto.
    simpljoin.
    eapply Mbox_common.ecb_list_join_join; eauto.
    clear Hlem.
    assert (Heq: merge els1 mqls' = merge x x0).
    { eapply EcbMod.join_unique_r.
       eapply EcbMod.join_comm.
       eapply EcbMod.join_set_r; eauto.
       unfold EcbMod.indom.
       rewrite EcbMod.map_get_sig; eauto.
       eapply EcbMod.join_set_l; eauto.
       eapply join_join_merge'_ecb;
       eapply EcbMod.join_comm; eauto.
       unfold EcbMod.indom.
       rewrite EcbMod.map_get_sig; eauto.
     }
   rewrite Heq.
   eapply EcbMod.join_comm.
   eapply join_join_merge_1_ecb; eauto.
  }
  assert (Hjo_new: join (merge els1 mqls') (sig (pb, Int.zero) (abssem i4, wls)) els).
 { eapply join_lib_aux.join_join_join_merge; eauto. 
    apply join_comm; eauto.
  }
   hoare_lifts_trms_pre (Aop, absecblsid, abstcblsid).
   assert (Hwls_case: wls = nil \/ wls <> nil) by tauto.
   destruct Hwls_case as [Hwls_eq | Hwls_neq].
   subst wls.
  (* case1: wls = nil *)
  eapply abscsq_rule.
  apply noabs_oslinv.
  eapply absinfer_kobjdel_succ_nex_wait; eauto.
  unfold CurTid.
  pure_auto.
  eapply absinfer_eq.
  (* actual exit critical *)
rewrite set_tls_rdy_nil in *.
assert (Hels_eq: (set els (pb, Int.zero) (abssem i4, nil)) = els).
{ eapply EcbMod.get_set_same; eauto. }
rewrite Hels_eq in *.

hoare forward prim.
unfold AOBJ.
unfold AObjs in *.
unfold AECBList.
unfold tcbllsegobjaux.
sep normal.
sep eexists.
sep cancel AObjArr.
sep cancel llsegobjaux.
sep pauto; try sep cancel evsllseg; eauto.
unfold AOSEventFreeList.
unfold p_local. unfold LINV. unfold OSLInv.
unfold ecbf_sll.
instantiate (3:=((V$ OS_EVENT_TYPE_UNUSED :: Vint32 Int.zero :: Vint32 i4 :: x2 :: x3 :: v'21 :: Vint32 i1 :: x7 ::  nil) :: v'2)).
unfold_ecbfsll.
unfold AOSPostEventTbl in *.
sep pauto; eauto.
sep cancel Astruct.
sep cancel Aarray.
sep cancel Aarray.
sep cancel ecbf_sllseg.
eauto.
unfolds; simpl; auto.
split; auto.
go.
unfold isptr.
splits; eauto.
eapply objdel_nodup_set_null_preserve; eauto.
eapply objcre_nodup_set_null_preserve; eauto.
eapply obj_aux_p_del_preserve'; eauto.
{
introv Hf.
simpljoin.
eapply objdel_del_del_contra; eauto.
}
eapply obj_ecb_delobj_preserve'; eauto.
eapply obj_aux_del in Htsk; eauto.
simpljoin. auto.
{ eapply semdel_ecb_del_prop_RHhold; eauto.
          introv Hf; destruct Hf as (qd & wt & pqwl & Hf & _); inverts Hf.  }
unfold AEventData. pure_auto.
(* end of exit critical *)
destruct Hcond1 as [(Hnz & Heq) | (Hz & Heq)].
{ eapply semacc_int_eq_false in Hnz.
   eapply Grp_eq_nz_imp_wl_not_nil with (etbl:= etbl) in Hnz; eauto.
   tryfalse. }
eapply semacc_int_eq_true in Hz; subst.
(* false If (tasks_waiting ′ ==ₑ ′ 1){OS_Sched (­)};ₛ *)
hoare forward;
change (Int.eq Int.zero ($ 1)) with false in *;
simpl val_inj in *.
hoare_split_pure_all.
simpljoin.
tryfalse.
apply hoare_disj_afalseP_l_pre.
unfold AEventData.
hoare unfold.
 eapply abscsq_rule.
 apply noabs_oslinv.
 eapply absinfer_kobjdel_ret; eauto.
 pure_auto.
 eapply absinfer_eq.
hoare forward.
(* case2: wls <> nil *)
destruct Hcond1 as [(Hnz & Heq) | (Hz & Heq)].
2: { eapply semacc_int_eq_true in Hz; subst.
       assert (wls = nil).
       eapply Grp_eq_zero_imp_wl_nil with (etbl:= etbl) (tcbls:= tcbls); eauto.
       subst.
       tryfalse. }
subst.
eapply abscsq_rule.
apply noabs_oslinv.
eapply absinfer_kobjdel_succ_ex_wait; eauto.
unfold CurTid.
pure_auto.
eapply absinfer_eq.
rewrite Hsubwl_eq' in *.
hoare forward prim.
unfold AOBJ.
unfold AObjs in *.
unfold AECBList.
unfold tcbllsegobjaux.
sep normal.
sep eexists.
sep cancel AObjArr.
sep cancel llsegobjaux.
sep pauto; try sep cancel evsllseg; eauto.
unfold AOSEventFreeList.
unfold p_local. unfold LINV. unfold OSLInv.
unfold ecbf_sll.
instantiate (3:=((V$ OS_EVENT_TYPE_UNUSED :: Vint32 Int.zero :: Vint32 i4 :: x2 :: x3 :: v'21 :: Vint32 i1 :: x7 ::  nil) :: v'2)).
unfold_ecbfsll.
unfold AOSPostEventTbl in *.
sep pauto; eauto.
sep cancel Astruct.
sep cancel Aarray.
sep cancel Aarray.
sep cancel ecbf_sllseg.
eauto.
unfolds; simpl; auto.
split; auto.
go.
unfold isptr.
splits; eauto.
eapply objdel_nodup_set_null_preserve; eauto.
eapply objcre_nodup_set_null_preserve; eauto.
eapply obj_aux_p_del_preserve'; eauto.
{
introv Hf.
simpljoin.
eapply objdel_del_del_contra; eauto.
}
eapply obj_ecb_delobj_preserve'; eauto.
eapply obj_aux_del in Htsk; eauto.
simpljoin. auto.
{ eapply semdel_ecb_del_prop_RHhold; eauto.
          introv Hf; destruct Hf as (qd & wt & pqwl & Hf & _); inverts Hf.  }
unfold AEventData. pure_auto.
(* end of exit critical *)
(* true If (tasks_waiting ′ ==ₑ ′ 1){OS_Sched (­)};ₛ *)
hoare forward;
change (Int.eq ($ 1) ($ 1)) with true in *;
simpl val_inj in *.
hoare_split_pure_all.
hoare forward.
sep cancel Aie.
sep cancel Acs.
sep cancel Ais.
sep cancel Aisr.
sep cancel Aop.
sep cancel p_local.
eauto.
unfolds; auto.
unfold AEventData; pure_auto.
intros. sep pauto. sep cancel p_local. simpl; auto.
intros. sep pauto. sep cancel p_local. simpl; auto.
hoare forward.
2: { hoare unfold. destruct H68; tryfalse. }
unfold OS_SchedPost.
unfold OS_SchedPost'.
unfold getasrt.
unfold AEventData.
hoare unfold.
inverts H68.
hoare_lifts_trms_pre Aop.
 eapply abscsq_rule.
 apply noabs_oslinv.
 eapply absinfer_kobjdel_ret; eauto.
 pure_auto.
 eapply absinfer_eq.
hoare forward.

Unshelve.
exact (1%positive).
exact Vnull.
exact Vnull.
exact (Vnull :: nil).
exact Int.zero.
exact Vnull.
exact (abssem Int.zero, (nil : list tid)).
Qed.
