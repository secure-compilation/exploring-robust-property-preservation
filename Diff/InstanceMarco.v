Require Import TraceModel.
Require Import LanguageModel.
Require Import ChainModel.

Module Source.

  (* source expressions *)
  Inductive se : Set :=
  | Num : nat -> se
  | Op : se -> se -> se
  | Ifz : se -> se -> se -> se
  (* | Letin : ? -> se -> se *)
  | Pair : se -> se -> se
  | P1 : se -> se
  | P2 : se -> se
  | Send : se -> se.

  (* source values *)
  Inductive sv : se -> Prop :=
  | V_Num : forall n, sv (Num n)
  | V_Pair : forall se1 se2, sv se1 -> sv se2 -> sv (Pair se1 se2).

  (* source types *)
  Inductive st : Set :=
  | Nat : st
  | Times : st -> st -> st.

  (* source typing *)
  Inductive wt : se -> st -> Prop :=
  | T_Num : forall n, wt (Num n) Nat
  | T_Op : forall se1 se2, wt se1 Nat -> wt se2 Nat -> wt (Op se1 se2) Nat
  | T_If : forall seg se1 se2 st, wt seg Nat -> wt se1 st -> wt se2 st -> wt (Ifz seg se1 se2) st
  | T_Pair : forall se1 se2 st1 st2, wt se1 st1 -> wt se2 st2 -> wt (Pair se1 se2) (Times st1 st2)
  | T_P1 : forall se st1 st2, wt se (Times st1 st2) -> wt (P1 se) st1
  | T_P2 : forall se st1 st2, wt se (Times st1 st2) -> wt (P2 se) st2
  | T_Send : forall se st, wt se st -> wt (Send se) Nat.

  Inductive smv : Set :=
  | M_Num : nat -> smv
  | M_Pair : smv -> smv -> smv.

  (* source messages *)
  Inductive sm : Set :=
  | Msg : smv -> smv -> sm.

  Inductive sl : Set :=
  | Empty_l : sl
  | Msg_l : sm -> sl.

  Inductive sq : Set :=
  | Empty_q : sq
  | Queue : sl -> sq -> sq.

  Inductive sectx : Set :=
  | Hole : sectx
  | E_Op1 : sectx -> se -> sectx
  | E_Op2 : nat -> sectx -> sectx
  | E_Ifz : sectx -> se -> se -> sectx
  | E_P1 : sectx -> sectx
  | E_P2 : sectx -> sectx
  | E_Send : sectx -> sectx.

  Inductive ssem_p :  se -> sl -> se -> Prop :=
  (* possibly make parametric later *)
  | PR_Op : forall n1 n2 n, n = n1 + n2 -> ssem_p (Op (Num n1) (Num n2)) Empty_l (Num n)
  | PR_P1 : forall sv1 sv2, sv sv1 -> sv sv2 -> ssem_p (P1 (Pair sv1 sv2)) Empty_l sv1.

End Source.

Module Target.

  Inductive te : Set :=
  | Num : nat -> te
  | Op : te -> te -> te
  | Ifz : te -> te -> te
  (* | Letin : ? -> te -> te *)
  | Pair : te -> te -> te
  | P1 : te -> te
  | P2 : te -> te
  | Send : te -> te.

End Target.

Module Compiler.
End Compiler.

Module RTC.
End RTC.