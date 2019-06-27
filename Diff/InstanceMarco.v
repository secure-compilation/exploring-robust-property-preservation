Require Import TraceModel.
Require Import LanguageModel.
Require Import ChainModel.

Module Source.

  (* source expressions *)
  Inductive se : Set :=
    | Num : nat -> se
    | Op : se -> se -> se
    | Ifz : se -> se -> se -> se
    | Letin : sx -> st -> se -> se -> se
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

  (*source typing env*)
  Inductive sg : Set :=
    | Empty_g : sq
    | Elem_g : sx -> st -> sq -> sq.

  (* source typing *)
  (*TODO add Gamma to signature and to all swt *)
  Inductive swt : sg -> se -> st -> Prop :=
    (*| T_Var : TODO do with ?*)
    | T_Num : forall n sg1, swt sg1 (Num n) Nat
    | T_Op : forall se1 se2 sg1, swt sg1 se1 Nat -> swt sg1 se2 Nat -> swt sg1 (Op se1 se2) Nat
    | T_If : forall seg se1 se2 st sg1, swt sg1 seg Nat -> swt sg1 se1 st -> swt sg1 se2 st -> swt sg1 (Ifz seg se1 se2) st
    | T_Pair : forall se1 se2 st1 st2 sg1, swt sg1 se1 st1 -> swt sg1 se2 st2 -> swt sg1 (Pair se1 se2) (Times st1 st2)
    | T_P1 : forall se st1 st2 sg1, swt sg1 se (Times st1 st2) -> swt sg1 (P1 se) st1
    | T_P2 : forall se st1 st2 sg1, swt sg1 se (Times st1 st2) -> swt sg1 (P2 se) st2
    | T_Send : forall se st sg1, swt sg1 se st -> swt sg1 (Send se) Nat
    | T_Letin : forall sg1 sx1 st1 se1 se2 st2, swt sg1 se1 st1 -> swt (Elem_g sx1 st1 sg1) se2 st2 -> swt sg1 (Letin sx1 st1 se1 se2) st2
    | T_Seq : forall se1 st1 se2 st2 sg1, swt sg1 se1 st1 -> swt sg1 se2 st2 -> swt sg1 (Seq se1 se2) st2.

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
    | Conv_Num : forall n, sv_smv (Num n) (M_Num n)
    | Conv_Pair : forall sv1 sv2 smv1 smv2, sv_smv sv1 smv1 -> sv_smv sv2 smv2 -> sv_smv (Pair sv1 sv2) (M_Pair smv1 smv2).

  (*source primitive reduction steps*)
  Inductive ssem_p :  se -> sl -> se -> Prop :=
    (* possibly make parametric later *)
    | PR_Op : forall n1 n2 n, n = n1 + n2 -> ssem_p (Op (Num n1) (Num n2)) Empty_l (Num n)
    (*| PR_Let : forall sx1 sv1 se1 st1, sv sv1 -> ssem_p (Letin sx1 st1 sv1 se1) Empty_l se1  (* TODO with subs *)*)
    | PR_P1 : forall sv1 sv2, sv sv1 -> sv sv2 -> ssem_p (P1 (Pair sv1 sv2)) Empty_l sv1
    | PR_P2 : forall sv1 sv2, sv sv1 -> sv sv2 -> ssem_p (P2 (Pair sv1 sv2)) Empty_l sv2
    | PR_Ift : forall n se1 se2, n=0 -> ssem_p (Ifz (Num n) se1 se2) Empty_l se1
    | PR_Iff : forall n se1 se2, n<>0 -> ssem_p (Ifz (Num n) se1 se2) Empty_l se2
    | PR_Send : forall sv1 sv2 smv1 smv2, sv_smv sv1 smv1 -> sv_smv sv2 smv2 -> ssem_p (Send (Pair sv1 sv2)) (Msg_l (Msg smv1 smv2)) (Num 0)
    | PR_Seq : forall sv1 se2, sv sv1 -> ssem_p (Seq sv1 se2) Empty_l se2.

  Inductive splug : sectx -> se -> se -> Prop :=
    | Plug_Hole : forall se, splug Hole se se
    | Plug_Op1 : forall se1 se1' se2 sctx, splug sctx se1 se1' -> splug (E_Op1 sctx se2) se1 (Op se1' se2)
    | Plug_Op2 : forall n1 se2 se2' sctx, splug sctx se2 se2' -> splug (E_Op2 n1 sctx) se2 (Op (Num n1) se2')
    | Plug_Ifz : forall se se' se1 se2 sctx, splug sctx se se' -> splug (E_Ifz sctx se1 se2) se (Ifz se' se1 se2)
    | Plug_P1 : forall se se' sctx, splug sctx se se' -> splug (E_P1 sctx) se (P1 se')
    | Plug_P2 : forall se se' sctx, splug sctx se se' -> splug (E_P2 sctx) se (P2 se')
    | Plug_Send : forall se se' sctx, splug sctx se se' -> splug (E_Send sctx) se (Send se')
    | Plug_Seq : forall se1 se1' se2 sctx, splug sctx se1 se1' -> splug (E_Seq sctx se2) se1 (Seq se1' se2).

  (*source nonprimitive reductions: the ctx rule*)
  Inductive ssem : sectx -> se -> sl -> se -> Prop :=
    | Ctx : forall ectx1 se1 sl1 se2, ssem_p se1 sl1 se2 -> ssem ectx1 se1 sl1 se2.

  (*source small step structural semantics*)
  Inductive ssm_sem : se -> sl -> se -> Prop :=
    | SM_OP1 : forall se1 se2 se3 sl1, ssm_sem se1 sl1 se2 -> ssm_sem (Op se1 se3) sl1 (Op se2 se3)
    | SM_OP2 : forall se1 se2 n sl1, ssm_sem se1 sl1 se2 -> ssm_sem (Op (Num n) se1) sl1 (Op (Num n) se2)
    | SM_OP : forall n1 n2 n, n = n1 + n2 -> ssm_sem (Op (Num n1) (Num n2)) Empty_l (Num n)
    | SM_Let1 : forall sx1 st1 se1 se2 se3 sl1, ssm_sem se1 sl1 se2 -> ssm_sem (Letin sx1 st1 se1 se3) sl1 (Letin sx1 st1 se2 se3)
    (*| SM_Let : forall sx1 sv1 se1 st1, sv sv1 -> ssem_p (Letin sx1 st1 sv1 se1) Empty_l se1  (* TODO with subs *)*)
    | SM_Ifg : forall se1 se2 sl1 se3 se4, ssm_sem se1 sl1 se2 -> ssm_sem (Ifz se1 se3 se4) sl1 (Ifz se2 se3 se4)
    | SM_Ift : forall n se1 se2, n=0-> ssm_sem (Ifz (Num n) se1 se2) Empty_l se1 
    | SM_Iff : forall n se1 se2, n<>0-> ssm_sem (Ifz (Num n) se1 se2) Empty_l se2
    | SM_Pair1 : forall se1 se2 se3 sl1, ssm_sem se1 sl1 se2 -> ssm_sem (Pair se1 se3) sl1 (Pair se2 se3) 
    | SM_Pair2 : forall se1 se2 sv1 sl1, ssm_sem se1 sl1 se2 -> ssm_sem (Pair sv1 se1) sl1 (Pair sv1 se2)
    | SM_P11 : forall se1 se2 sl1, ssm_sem se1 sl1 se2 -> ssm_sem (P1 se1) sl1 (P1 se2)
    | SM_P21 : forall se1 se2 sl1, ssm_sem se1 sl1 se2 -> ssm_sem (P2 se1) sl1 (P2 se2)
    | SM_P1 : forall sv1 sv2, sv sv1 -> sv sv2 -> ssm_sem (P1 (Pair sv1 sv2)) Empty_l sv1
    | SM_P2 : forall sv1 sv2, sv sv1 -> sv sv2 -> ssm_sem (P2 (Pair sv1 sv2)) Empty_l sv2
    | SM_Send1 : forall se1 se2 sl1, ssm_sem se1 sl1 se2 -> ssm_sem (Send se1) sl1 (Send se2)
    | SM_Send : forall sv1 sv2 smv1 smv2, sv_smv sv1 smv1 -> sv_smv sv2 smv2 -> ssm_sem (Send (Pair sv1 sv2)) (Msg_l (Msg smv1 smv2)) (Num 0)
    | SM_Seq1 : forall se1 se2 sl1 se3, ssm_sem se1 sl1 se2 -> ssm_sem (Seq se1 se3) sl1 (Seq se2 se3)
    | SM_Seq : forall sv1 se2, sv sv1 -> ssm_sem (Seq sv1 se2) Empty_l se2.

  (*source big step reduction that chains messages as queues*)
  Inductive sbsem : se -> sq -> se -> Prop :=
    | B_Refl : forall se1, sbsem se1 Empty_q se1
    (*| B_Trans : forall se1 se2 se3 sq1 sq2, sbsem se1 sq1 se2 -> sbsem se2 sq2 se3 -> sbsem se1 ??*)
    (*case above is not ok. should it be removed? or shuld we add another case in the sq def for joining queues?*)
    (* | B_Act : forall se1 sl1 se2 sq1 se3, ssm_sem se1 sl1 se2 -> sbsem se2 sq1 se3 -> sbsem se1 (Queue sl1 sq1) se3. *)
  (* | B_Act : forall se1 ctx se10 se2 se20 sl1 sq1 se3, se1 = plug ctx se1o -> se2 = plug ctx se20 -> ssm se1 sl1 se2 ->   sbsem se2 sq1 se3 -> sbsem se1 (Queue sl1 sq1) se3. *)
  | B_Act : forall ctx se1 se1' sl1 se2 se2' sq1 se3, ssem ctx se1 sl1 se2 -> splug ctx se1 se1' -> splug ctx se2 se2' -> sbsem se2' sq1 se3 -> sbsem se1' (Queue sl1 sq1) se3.

  (*source single behaviour (fat leadsto)*)
  Inductive sbeh : se -> sq -> Prop :=
    | B_Sing : forall se1 sq1 se2, sbsem se1 sq1 se2 -> sbeh se1 sq1.

  (*source calculation of all possible behaviours*)
  (*Inductive sbeh : se -> sq : Prop :=*)
    (*| B_Set : .*)

End Source.

Module Target.

  Inductive te : Set :=
    | Num : nat -> te
    | Op : te -> te -> te
    | Ifz : te -> te -> te -> te
    | Letin : tx -> te -> te -> te 
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
  (*TODO add Gamma to signature and to all swt *)
  Inductive twt : te -> tt -> Prop :=
    (*| T_Var : TODO do with ?*)
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
    (*| PR_Let : forall sx1 sv1 se1 st1, sv sv1 -> ssem_p (Letin sx1 st1 sv1 se1) Empty_l se1  (* TODO with subs *)*)
    | PR_P1 : forall tv1 tv2, tv tv1 -> tv tv2 -> tsem_p (P1 (Pair tv1 tv2)) Empty_l tv1
    | PR_P2 : forall tv1 tv2, tv tv1 -> tv tv2 -> tsem_p (P2 (Pair tv1 tv2)) Empty_l tv2
    | PR_Ift : forall n te1 te2, n=0 -> tsem_p (Ifz (Num n) te1 te2) Empty_l te1
    | PR_Iff : forall n te1 te2, n<>0 -> tsem_p (Ifz (Num n) te1 te2) Empty_l te2
    | PR_Send : forall n, (*tv n ->*) tsem_p (Send (Num n)) (Msg_l (M_Num n)) (Num 0) (* this ok? *)
    | PR_Seq : forall tv1 te2, tv tv1 -> tsem_p (Seq tv1 te2) Empty_l te2.

  Inductive tplug : tectx -> te -> te -> Prop :=
    | Plug_Hole : forall te, tplug Hole te te
    | Plug_Op1 : forall te1 te1' te2 tctx, tplug tctx te1 te1' -> tplug (E_Op1 tctx te2) te1 (Op te1' te2)
    | Plug_Op2 : forall n1 te2 te2' tctx, tplug tctx te2 te2' -> tplug (E_Op2 n1 tctx) te2 (Op (Num n1) te2')
    | Plug_Ifz : forall te te' te1 te2 tctx, tplug tctx te te' -> tplug (E_Ifz tctx te1 te2) te (Ifz te' te1 te2)
    | Plug_P1 : forall te te' tctx, tplug tctx te te' -> tplug (E_P1 tctx) te (P1 te')
    | Plug_P2 : forall te te' tctx, tplug tctx te te' -> tplug (E_P2 tctx) te (P2 te')
    | Plug_tend : forall te te' tctx, tplug tctx te te' -> tplug (E_Send tctx) te (Send te')
    | Plug_teq : forall te1 te1' te2 tctx, tplug tctx te1 te1' -> tplug (E_Seq tctx te2) te1 (Seq te1' te2).

  (* target nonprimitive reductions: the ctx rule*)
  Inductive tsem : tectx -> te -> tl -> te -> Prop :=
    | Ctx : forall ectx1 te1 tl1 te2, tsem_p te1 tl1 te2 -> tsem ectx1 te1 tl1 te2.

  (* target big step reduction that chains messages as queues*)
  Inductive tbsem : te -> tq -> te -> Prop :=
    | B_Refl : forall te1, tbsem te1 Empty_q te1
    (* see missing option cases form source *)
    | B_Act : forall te1 te1' tl1 te2 te2' tq1 te3 ctx, tsem ctx te1 tl1 te2 -> tplug ctx te1 te1' -> tplug ctx te2 te2' -> tbsem te2' tq1 te3 -> tbsem te1' (Queue tl1 tq1) te3.

  (* target single behaviour (fat leadsto)*)
  Inductive tbeh : te -> tq -> Prop :=
    | B_Sing : forall te1 tq1 te2, tbsem te1 tq1 te2 -> tbeh te1 tq1.

  (*source calculation of all possible behaviours*)
  (*Inductive tbeh : te -> tq : Prop :=
    | B_Set : .*)

End Target.

Module Compiler.
  Module S := Source.
  Module T := Target.

  (*given a source expression with a type, translate that into a target expression.*)
  (*TODO: typing needs an environment *)
  Inductive gensend : T.te -> S.st -> T.te -> Prop :=
    | Snd_N : forall tn tn, gensend (T.Num sn) (S.Nat) (T.Send (T.Num tn))
    | Snd_P : forall te1 st1 te2 st2 te1' te2', gensend te1 st1 te1' -> gensend te2 st2 te2'-> gensend (T.Pair te1 te2) (S.Times st1 st2) (T.Seq te1' te2').

  Inductive tcmp : S.st -> T.tt -> Prop :=
    | TCMP_N : tcmp S.Nat T.Nat
    | TCMP_P : forall st1 st2 tt1 tt2, tcmp st1 tt1 -> tcmp st2 tt2 -> tcmp (S.Times st1 st2) (T.Times tt1 tt2).

  Inductive cmp : S.se -> S.st -> T.te -> Prop :=
    | CMP_Nat : forall sn tn, sn = tn -> S.swt (S.Num sn) S.Nat -> cmp (S.Num sn) (S.Nat) (T.Num tn)
    | CMP_Op : forall se1 se2 te1 te2, S.swt (S.Op se1 se2) S.Nat -> cmp se1 S.Nat te1 -> cmp se2 S.Nat te2 -> cmp (S.Op se1 se2) S.Nat (T.Op te1 te2)
      (*why bother with the well typed assumption below?*)
    | CMP_Pair : forall se1 st1 te1 se2 st2 te2, S.swt (S.Pair se1 se2) (S.Times st1 st2) -> cmp se1 st1 te1 -> cmp se2 st2 te2 -> cmp (S.Pair se1 se2) (S.Times st1 st2) (T.Pair te1 te2)
    | CMP_P1 : forall se1 st1 te1, S.swt (S.P1 se1) st1 -> cmp se1 st1 te1 -> cmp (S.P1 se1) st1 (T.P1 te1)
    | CMP_P2 : forall se1 st1 te1, S.swt (S.P2 se1) st1 -> cmp se1 st1 te1 -> cmp (S.P2 se1) st1 (T.P2 te1)
    | CMP_Ifz : forall seg se1 se2 st1 teg te1 te2, S.swt (S.Ifz seg se1 se2) st1 -> cmp seg S.Nat teg -> cmp se1 st1 te1 -> cmp se2 st2 te2 -> cmp (S.Ifz seg se1 se2) st1 (T.Ifz teg te1 te2)
    | CMP_Letin : forall sx1 tx1 st1 tt1 se1 se2 te1 te2 st2, S.swt (S.Letin sx1 st1 se1 se2) st2 -> cmp sx1 tx1 -> tcmp st1 tt1 -> cmp se1 te1 -> cmp se2 te2 -> cmp (S.Letin sx1 st1 se1 se2) st2 (T.Letin tx1 tt1 te1 te2)
    | CMP_Send : forall se1 st1 te1 te2, S.swt (S.Send se1) S.Nat -> cmp se1 st1 te1 -> gensend tx1 st1 te2 -> cmp (S.Send se1) S.Nat (T.Letin tx1 tt1 te1 te2)
    (*TODO above: add that the new target variable is fresh*)
    | CMP_Seq : forall se1 se2 st1 st2 te1 te2, S.swt (S.Seq se1 se2) st2 -> cmp se1 st1 te1 -> cmp se2 st2 te2 -> cmp (S.Seq se1 se2) st2 (S.Seq te1 te2).

End Compiler.

Module TraceRelation.
  Module S := Source.
  Module T := Target.

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
  Module S := Source.
  Module T := Target.
  Module C := Compiler.
  Module R := TraceRelation.

End RTC.