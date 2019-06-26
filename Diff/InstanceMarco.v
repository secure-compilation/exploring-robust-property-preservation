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
    | Send : se -> se
    | Seq: se -> se -> se.

  (* source values *)
  Inductive sv : se -> Prop :=
    | V_Num : forall n, sv (Num n)
    | V_Pair : forall se1 se2, sv se1 -> sv se2 -> sv (Pair se1 se2).

  (* source types *)
  Inductive st : Set :=
    | Nat : st
    | Times : st -> st -> st.

  (* source typing *)
  Inductive swt : se -> st -> Prop :=
    | T_Num : forall n, swt (Num n) Nat
    | T_Op : forall se1 se2, swt se1 Nat -> swt se2 Nat -> swt (Op se1 se2) Nat
    | T_If : forall seg se1 se2 st, swt seg Nat -> swt se1 st -> swt se2 st -> swt (Ifz seg se1 se2) st
    | T_Pair : forall se1 se2 st1 st2, swt se1 st1 -> swt se2 st2 -> swt (Pair se1 se2) (Times st1 st2)
    | T_P1 : forall se st1 st2, swt se (Times st1 st2) -> swt (P1 se) st1
    | T_P2 : forall se st1 st2, swt se (Times st1 st2) -> swt (P2 se) st2
    | T_Send : forall se st, swt se st -> swt (Send se) Nat
    | T_Seq : forall se1 st1 se2 st2, swt se1 st1 -> swt se2 st2 -> swt (Seq se1 se2) st2.

  (*source messages - meta definition for the top-level def below*)
  Inductive smv : Set :=
    | M_Num : nat -> smv
    | M_Pair : smv -> smv -> smv.

  (* source messages *)
  Inductive sm : Set :=
    | Msg : smv -> smv -> sm.

  (*source labels*)
  Inductive sl : Set :=
    | Empty_l : sl
    | Msg_l : sm -> sl.

  (*source queues*)
  Inductive sq : Set :=
    | Empty_q : sq
    | Queue : sl -> sq -> sq.

  (*source evaluation contexts*)
  Inductive sectx : Set :=
    | Hole : sectx
    | E_Op1 : sectx -> se -> sectx
    | E_Op2 : nat -> sectx -> sectx
    | E_Ifz : sectx -> se -> se -> sectx
    | E_P1 : sectx -> sectx
    | E_P2 : sectx -> sectx
    | E_Send : sectx -> sectx
    | E_Seq : sectx -> se -> sectx.

  Inductive sv_smv : se -> smv -> Prop :=
  | Conv_Num : forall n,
      sv_smv (Num n) (M_Num n)
  | Conv_Pair : forall sv1 sv2 smv1 smv2,
      sv_smv sv1 smv1 -> sv_smv sv2 smv2 -> sv_smv (Pair sv1 sv2) (M_Pair smv1 smv2).

  (*source primitive reduction steps*)
  Inductive ssem_p : se -> sl -> se -> Prop :=
    (* possibly make parametric later *)
    | PR_Op : forall n1 n2 n, n = n1 + n2 -> ssem_p (Op (Num n1) (Num n2)) Empty_l (Num n)
    | PR_P1 : forall sv1 sv2, sv sv1 -> sv sv2 -> ssem_p (P1 (Pair sv1 sv2)) Empty_l sv1
    | PR_P2 : forall sv1 sv2, sv sv1 -> sv sv2 -> ssem_p (P2 (Pair sv1 sv2)) Empty_l sv2
    (*check these below*)
    | PR_Ift : forall n se1 se2, n=0-> ssem_p (Ifz (Num n) se1 se2) Empty_l se1
    | PR_Iff : forall n se1 se2, n<>0-> ssem_p (Ifz (Num n) se1 se2) Empty_l se2
    | PR_Send : forall sv1 sv2 smv1 smv2, sv_smv sv1 smv1 -> sv_smv sv2 smv2 -> ssem_p (Send (Pair sv1 sv2)) (Msg_l (Msg smv1 smv2)) (Num 0)
    | PR_Seq : forall sv1 se2, sv sv1 -> ssem_p (Seq sv1 se2) Empty_l se2.

  Inductive splug : sectx -> se -> se -> Prop :=
  | Plug_Hole : forall se,
      splug Hole se se
  | Plug_Op1 : forall se1 se1' se2 sctx,
      splug sctx se1 se1' -> splug (E_Op1 sctx se2) se1 (Op se1' se2)
  | Plug_Op2 : forall n1 se2 se2' sctx,
      splug sctx se2 se2' -> splug (E_Op2 n1 sctx) se2 (Op (Num n1) se2')
  | Plug_Ifz : forall se se' se1 se2 sctx,
      splug sctx se se' -> splug (E_Ifz sctx se1 se2) se (Ifz se' se1 se2)
  | Plug_P1 : forall se se' sctx,
      splug sctx se se' -> splug (E_P1 sctx) se (P1 se')
  | Plug_P2 : forall se se' sctx,
      splug sctx se se' -> splug (E_P2 sctx) se (P2 se')
  | Plug_Send : forall se se' sctx,
      splug sctx se se' -> splug (E_Send sctx) se (Send se')
  | Plug_Seq : forall se1 se1' se2 sctx,
      splug sctx se1 se1' -> splug (E_Seq sctx se2) se1 (Seq se1' se2).

  (*source nonprimitive reductions: the ctx rule*)
  (* Inductive ssem : sectx -> se -> sl -> se -> Prop := *)
  (*   | Ctx : forall ectx1 se1 sl1 se2, ssem_p se1 sl1 se2 -> ssem ectx1 se1 sl1 se2. *)

  (*source big step reduction that chains messages as queues*)
  Inductive sbsem : se -> sq -> se -> Prop :=
    | B_Refl : forall se1, sbsem se1 Empty_q se1
    (* | B_Trans : forall se1 se2 se3 sq1 sq2, sbsem se1 sq1 se2 -> sbsem se2 sq2 se3 -> sbsem se1 ?? *)
    (*case above is not ok. should it be removed? or shuld we add another case in the sq def for joining queues?*)
    | B_Act : forall se1 sl1 se2, ssem se1 sl1 se2 -> sbsem se1 (Queue sl1 Empty_q) se2.

  (*source single behaviour (fat leadsto)*)
  Inductive ssingbeh : se -> sq -> Prop :=
    | B_Sing : forall se1 sq1 se2, sbsem se1 sq1 se2 -> sbeh se1 sq1.
    (*is there a type mismatch because we have a forall se2? shoudl hte type include one more "se ->"?*)

  (*source calculation of all possible behaviours*)
  (* Inductive sbeh : se -> sq : Prop := *)
  (*   | B_Set : . *)

End Source.

Module Target.

  Inductive te : Set :=
    | Num : nat -> te
    | Op : te -> te -> te
    | Ifz : te -> te -> te -> te
    (* | Letin : ? -> te -> te *)
    | Pair : te -> te -> te
    | P1 : te -> te
    | P2 : te -> te
    | Send : te -> te
    | Seq : te -> te -> te.

  (* target values *)
  Inductive tv : te -> Prop :=
    | V_Num : forall n, tv (Num n)
    | V_Pair : forall te1 te2, tv te1 -> tv te2 -> tv (Pair te1 te2).

  (* target types *)
  Inductive tt : Set :=
    | Nat : tt
    | Times : tt -> tt -> tt.

  (* target typing *)
  Inductive twt : te -> tt -> Prop :=
    | T_Num : forall n, twt (Num n) Nat
    | T_Op : forall te1 te2, twt te1 Nat -> twt te2 Nat -> twt (Op te1 te2) Nat
    | T_If : forall teg te1 te2 tt, twt teg Nat -> twt te1 tt -> twt te2 tt -> twt (Ifz teg te1 te2) tt
    | T_Pair : forall te1 te2 tt1 tt2, twt te1 tt1 -> twt te2 tt2 -> twt (Pair te1 te2) (Times tt1 tt2)
    | T_P1 : forall te tt1 tt2, twt te (Times tt1 tt2) -> twt (P1 te) tt1
    | T_P2 : forall te tt1 tt2, twt te (Times tt1 tt2) -> twt (P2 te) tt2
    | T_Send : forall te, twt te Nat -> twt (Send te) Nat
    | T_Seq : forall te1 tt1 te2 tt2, twt te1 tt1 -> twt te2 tt2 -> twt (Seq te1 te2) tt2.

  (* target messages *)
  Inductive tm : Set :=
    | M_Num : nat -> tm.

  (* target labels*)
  Inductive tl : Set :=
    | Empty_l : tl
    | Msg_l : tm -> tl.

  (* target queues*)
  Inductive tq : Set :=
    | Empty_q : tq
    | Queue : tl -> tq -> tq.

  (* target evaluation contexts*)
  Inductive tectx : Set :=
    | Hole : tectx
    | E_Op1 : tectx -> te -> tectx
    | E_Op2 : nat -> tectx -> tectx
    | E_Ifz : tectx -> te -> te -> tectx
    | E_P1 : tectx -> tectx
    | E_P2 : tectx -> tectx
    | E_Send : tectx -> tectx 
    | E_Seq : tectx -> te -> tectx.

  (* target primitive reduction steps*)
  Inductive tsem_p :  te -> tl -> te -> Prop :=
    (* possibly make parametric later *)
    | PR_Op : forall n1 n2 n, n = n1 + n2 -> tsem_p (Op (Num n1) (Num n2)) Empty_l (Num n)
    | PR_P1 : forall tv1 tv2, tv tv1 -> tv tv2 -> tsem_p (P1 (Pair tv1 tv2)) Empty_l tv1
    | PR_P2 : forall tv1 tv2, tv tv1 -> tv tv2 -> tsem_p (P2 (Pair tv1 tv2)) Empty_l tv2
    (*check these below*)
    | PR_Ift : forall n te1 te2, n=0-> tsem_p (Ifz (Num n) te1 te2) Empty_l te1
    | PR_Iff : forall n te1 te2, n<>0-> tsem_p (Ifz (Num n) te1 te2) Empty_l te2
    | PR_Send : forall n, (*tv n ->*) tsem_p (Send (Num n)) (Msg_l (M_Num n)) (Num 0)
    | PR_Seq : forall tv1 te2, tv tv1 -> tsem_p (Seq tv1 te2) Empty_l te2.

  (* target nonprimitive reductions: the ctx rule*)
  Inductive tsem : tectx -> te -> tl -> te -> Prop :=
    | Ctx : forall ectx1 te1 tl1 te2, tsem_p te1 tl1 te2 -> tsem ectx1 te1 tl1 te2.

  (* target big step reduction that chains messages as queues*)
  Inductive tbsem : te -> tq -> te -> Prop :=
    | B_Refl : forall te1, tbsem te1 Empty_q te1
    (* | B_Trans : forall te1 te2 te3 tq1 tq2, tbsem te1 tq1 te2 -> tbsem te2 tq2 te3 -> tbsem te1 ?? *)
    (*case above is not ok. should it be removed? or shuld we add another case in the sq def for joining queues?*)
    | B_Act : forall te1 tl1 te2, tsem te1 tl1 te2 -> tbsem te1 (Queue tl1 Empty_q) te2.

  (* target single behaviour (fat leadsto)*)
  Inductive tsingbeh : te -> tq -> Prop :=
    | B_Sing : forall te1 tq1 te2, tbsem te1 tq1 te2 -> tbeh te1 tq1.
    (*is there a type mismatch because we have a forall se2? shoudl hte type include one more "se ->"?*)

  (*source calculation of all possible behaviours*)
  Inductive tbeh : te -> tq : Prop :=
    | B_Set : .

End Target.

Module Compiler.

  (*given a source expression with a type, translate that into a target expression.*)
  (*TODO: problem, i need a concatenation, which i encoded as let. *)
  Inductive gensend : se -> st -> te : Type :=
    | Snd_N : forall sn tn, sn == tn -> wt (Num sn) Nat -> Target.Send (Num tn)
    | Snd_P : forall se1 st1 se2 st2, (Target.Seq (gensend se1 st1) (gensend se2 st2)) .

  Inductive cmp : swt -> te -> Prop :=
    | CMP_Nat : forall sn tn, swt (Num sn) Nat -> sn == tn -> Num tn
    | CMP_Op : forall se1 se2, swt (Op se1 se2) Nat -> Op (cmp (swt se1 Nat)) (cmp (swt se2 Nat))
    (*ok. no clue here. should the namespace be there? should the recursive call be done this way? many questions.*)
    | CMP_Pair
    | CMP_P1
    | CMP_P2
    | CMP_Ifz
    | CMP_Send.

End Compiler.

Module TraceRelation.

  Inductive trel_msg : sm -> tm -> Prop :=
    | TR_NN
    | TR_NM
    | TR_NM
    | TR_MM.

  Inductive trel_q : sq -> tq -> Prop :=
    | TRQ_e
    | TRQ_m.

End TraceRelation.

Module RTC.
End RTC.