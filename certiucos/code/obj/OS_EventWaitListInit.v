Require Import os_code_defs.
Require Import code_notations.
Require Import os_ucos_h.

Open Scope code_scope.

Definition ptbl1 : ident := 501%Z.

Definition OS_EventWaitListInit_impl  :=
Void · OS_EventWaitListInit·(⌞ptr @ OS_EVENT∗ ⌟)··{
       ⌞ptbl @ Int8u∗; ptbl1 @ Int8u∗⌟;

       ptr′→OSEventGrp =ₑ ′0;ₛ
       ptr′→OSPostEventGrp =ₑ ′0;ₛ
       ptbl′ =ₑ &ₐ ptr′→OSEventTbl[′0];ₛ
       ptbl1′ =ₑ &ₐ ptr′→OSPostEventTbl[′0];ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ∗ptbl1′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ++ ptbl1′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ∗ptbl1′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ++ ptbl1′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ∗ptbl1′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ++ ptbl1′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ∗ptbl1′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ++ ptbl1′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ∗ptbl1′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ++ ptbl1′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ∗ptbl1′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ++ ptbl1′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ∗ptbl1′ =ₑ ′0;ₛ
       ++ ptbl′;ₛ
       ++ ptbl1′;ₛ

       ∗ptbl′ =ₑ ′0;ₛ
       ∗ptbl1′ =ₑ ′0;ₛ
       RETURN
}·. 

Close Scope code_scope.