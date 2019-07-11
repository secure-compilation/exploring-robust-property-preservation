(* M: personal note: on sublimetext, use sublimecoq-run and the menu-noted *)
(*inversion -> pattern match on stuff in the HP*)
(*constructor -> pattern match on stuff in the conclusion*)

Require Import TraceModel.
Require Import LanguageModel.
Require Import ChainModel.
Require Import NonRobustTraceCriterion.

Set Bullet Behavior "Strict Subproofs".

Module Source.

  (* source expressions *)
  Inductive se : Set :=
    | Num : nat -> se
    | Op : se -> se -> se
    | Pair : se -> se -> se
    | P1 : se -> se
    | P2 : se -> se.

  (*source statements*)
  Inductive ss : Set :=
    | Skip : ss
    | Seq: ss -> ss -> ss
    | Ifz : se -> ss -> ss-> ss
    | Send : se -> ss.

  (* source values *)
  Inductive sv : se -> Prop :=
    | V_Num : forall n, sv (Num n)
    | V_Pair : forall se1 se2, sv se1 -> sv se2 -> sv (Pair se1 se2).

  (* source types *)
  Inductive st : Set :=
    | Nat : st
    | Times : st -> st -> st.

  (* source typing for expressions *)
  Inductive swte : se -> st -> Prop :=
    | T_Num : forall n, swte (Num n) Nat
    | T_Op : forall se1 se2, swte se1 Nat -> swte se2 Nat -> swte (Op se1 se2) Nat
    | T_Pair : forall se1 se2 st1 st2, swte se1 st1 -> swte se2 st2 -> swte (Pair se1 se2) (Times st1 st2)
    | T_P1 : forall se st1 st2, swte se (Times st1 st2) -> swte (P1 se) st1
    | T_P2 : forall se st1 st2, swte se (Times st1 st2) -> swte (P2 se) st2.

  (*source typing for statements*)
  Inductive swts : ss -> Prop :=
    | T_Skip : swts Skip
    | T_If : forall seg ss1 ss2, swte seg Nat -> swts ss1 -> swts ss2 -> swts (Ifz seg ss1 ss2)
    | T_Send : forall se st1 st2, swte se (Times st1 st2) -> swts (Send se)
    | T_Seq : forall ss1 ss2, swts ss1 -> swts ss2 -> swts (Seq ss1 ss2).

  (*source messages*)
  Inductive sm : Set :=
    | Msg_base : nat -> sm
    | Msg_ind : sm -> sm -> sm.

  (*how to relate values and messages*)
  Inductive sv_sm : se -> sm -> Prop :=
    | Conv_base : forall n1,
      sv_sm (Num n1) (Msg_base n1)
    | Conv_ind : forall se1 se2 sm1 sm2,
      sv_sm se1 sm1 ->
      sv_sm se2 sm2 ->
      sv_sm (Pair se1 se2) (Msg_ind sm1 sm2).

  (*source labels*)
  Inductive sl : Set :=
    | Empty_l : sl
    | Msg_l : sm -> sl.

  (*source queues*)
  Inductive sq : Set :=
    | Empty_q : sq
    | Sing_q : sl -> sq -> sq
    | Queue : sq -> sq -> sq.

  (*source evaluation contexts*)
  Inductive sectx : Set :=
    | Hole : sectx
    | E_Op1 : sectx -> se -> sectx
    | E_Op2 : nat -> sectx -> sectx
    | E_P1 : sectx -> sectx
    | E_P2 : sectx -> sectx
    | E_Pair1 : sectx -> se -> sectx
    | E_Pair2 : se -> sectx -> sectx.
  (* TODO: not sure why i cannot write sv instead of se here *)

  (*source primitive reduction steps*)
  Inductive ssem_p :  se -> se -> Prop :=
    (* TODO possibly make parametric later *)
    | PR_Op : forall n1 n2 n, n = n1 + n2 -> ssem_p (Op (Num n1) (Num n2)) (Num n)
    | PR_P1 : forall sv1 sv2, sv sv1 -> sv sv2 -> ssem_p (P1 (Pair sv1 sv2)) sv1
    | PR_P2 : forall sv1 sv2, sv sv1 -> sv sv2 -> ssem_p (P2 (Pair sv1 sv2)) sv2.

  Inductive splug : sectx -> se -> se -> Prop :=
    | Plug_Hole : forall se, splug Hole se se
    | Plug_Op1 : forall se1 se1' se2 sctx, splug sctx se1 se1' -> splug (E_Op1 sctx se2) se1 (Op se1' se2)
    | Plug_Op2 : forall n1 se2 se2' sctx, splug sctx se2 se2' -> splug (E_Op2 n1 sctx) se2 (Op (Num n1) se2')
    | Plug_P1 : forall se se' sctx, splug sctx se se' -> splug (E_P1 sctx) se (P1 se')
    | Plug_P2 : forall se se' sctx, splug sctx se se' -> splug (E_P2 sctx) se (P2 se')
    | Plug_Pair1 : forall se1 se se' sctx, splug sctx se se' -> splug (E_Pair1 sctx se1) se (Pair se1 se')
    | Plug_Pair2 : forall sv1 se se' sctx, splug sctx se se' -> splug (E_Pair2 sv1 sctx) se (Pair sv1 se').

  (*source nonprimitive reductions: the ctx rule*)
  Inductive ssem : sectx -> se -> se -> Prop :=
    | Ctx : forall ectx1 se1 se2, ssem_p se1 se2 -> ssem ectx1 se1 se2.

  (* source small step structural semantics *)
  Inductive ssm_sem : se -> se -> Prop :=
    | SM_OP1 : forall se1 se2 se3, ssm_sem se1 se2 -> ssm_sem (Op se1 se3) (Op se2 se3)
    | SM_OP2 : forall se1 se2 n, ssm_sem se1 se2 -> ssm_sem (Op (Num n) se1) (Op (Num n) se2)
    | SM_OP : forall n1 n2 n, n = n1 + n2 -> ssm_sem (Op (Num n1) (Num n2)) (Num n)
    | SM_Pair1 : forall se1 se2 se3, ssm_sem se1 se2 -> ssm_sem (Pair se1 se3) (Pair se2 se3)
    | SM_Pair2 : forall se1 se2 sv1, ssm_sem se1 se2 -> ssm_sem (Pair sv1 se1) (Pair sv1 se2)
    | SM_P11 : forall se1 se2, ssm_sem se1 se2 -> ssm_sem (P1 se1) (P1 se2)
    | SM_P21 : forall se1 se2, ssm_sem se1 se2 -> ssm_sem (P2 se1) (P2 se2)
    | SM_P1 : forall sv1 sv2, sv sv1 -> sv sv2 -> ssm_sem (P1 (Pair sv1 sv2)) sv1
    | SM_P2 : forall sv1 sv2, sv sv1 -> sv sv2 -> ssm_sem (P2 (Pair sv1 sv2)) sv2.

  (*reflexive transitive closure of the single semantic step*)
  Inductive ssemrt : se -> se -> Prop :=
    | Refl : forall se1, ssemrt se1 se1
    | Tran: forall ctx se1 se2 se3 se1' se2', ssem ctx se1 se2 -> splug ctx se1 se1' -> splug ctx se2 se2' -> ssemrt se2' se3 -> ssemrt se1' se3.
    (*| Tran : forall se1 se2 se3, ssm_sem se1 se2 -> ssemrt se2 se3 -> ssemrt se1 se3.*)

  (*source big step reduction that chains messages as queues*)
  Inductive sbsem : ss -> sq -> ss -> Prop :=
    | B_Skip : sbsem Skip Empty_q Skip
    | B_Seq : forall ss1 ss2 sq1 sq2, sbsem ss1 sq1 Skip -> sbsem ss2 sq2 Skip -> sbsem (Seq ss1 ss2) (Queue sq1 sq2) Skip
    | B_Ift : forall se1 ss1 ss2 sq1 n, n= 0 -> ssemrt se1 (Num n) -> sbsem ss1 sq1 Skip -> sbsem (Ifz se1 ss1 ss2) sq1 Skip
    | B_iff : forall se1 ss1 ss2 sq1 n, n<>0 -> ssemrt se1 (Num n) -> sbsem ss2 sq1 Skip -> sbsem (Ifz se1 ss1 ss2) sq1 Skip
    | B_Send : forall se1 sv1 sv2 smv1 smv2, sv_sm sv1 smv1 -> sv_sm sv2 smv2 -> ssemrt se1 (Pair sv1 sv2) -> sbsem (Send se1) (Sing_q (Msg_l (Msg_ind smv1 smv2)) Empty_q) Skip.

  (*source single behaviour (fat leadsto)*)
  Inductive sbeh : ss -> sq -> Prop :=
    | B_Sing : forall ss1 sq1 , sbsem ss1 sq1 Skip -> sbeh ss1 sq1.

  (* source language with vacuous context linking *)
  Definition slang := Build_Language (fun (par : ss) (_ : unit) => par).

  (* source semantics *)
  Theorem exists_trace : forall s, exists q, sbeh s q.
  Admitted.

  Definition ssemt := Build_Semantics slang sbeh exists_trace.

End Source.

Module Target.

  Inductive te : Set :=
    | Num : nat -> te
    | Op : te -> te -> te
    | Pair : te -> te -> te
    | P1 : te -> te
    | P2 : te -> te.

  Inductive ts : Set :=
    | Skip : ts
    | Seq: ts -> ts -> ts
    | Ifz : te -> ts -> ts-> ts
    | Send : te -> ts.

  (* target values *)
  Inductive tv : te -> Prop :=
    | V_Num : forall n, tv (Num n)
    | V_Pair : forall te1 te2, tv te1 -> tv te2 -> tv (Pair te1 te2).

  (* target types *)
  Inductive tt : Set :=
    | Nat : tt
    | Times : tt -> tt -> tt.

  (* target typing *)
  Inductive twte : te -> tt -> Prop :=
    | T_Num : forall n, twte (Num n) Nat
    | T_Op : forall te1 te2, twte te1 Nat -> twte te2 Nat -> twte (Op te1 te2) Nat
    | T_Pair : forall te1 te2 tt1 tt2, twte te1 tt1 -> twte te2 tt2 -> twte (Pair te1 te2) (Times tt1 tt2)
    | T_P1 : forall te tt1 tt2, twte te (Times tt1 tt2) -> twte (P1 te) tt1
    | T_P2 : forall te tt1 tt2, twte te (Times tt1 tt2) -> twte (P2 te) tt2.

  (*target statement typing*)
  Inductive twts : ts -> Prop :=
    | T_Skip : twts Skip
    | T_If : forall teg ts1 ts2, twte teg Nat -> twts ts1 -> twts ts2 -> twts (Ifz teg ts1 ts2)
    | T_Send : forall te tt, twte te tt -> twts (Send te)
    | T_Seq : forall ts1 ts2, twts ts1 -> twts ts2 -> twts (Seq ts1 ts2).

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
    | Sing_q : tl -> tq -> tq
    | Queue : tq -> tq -> tq.

  (* target evaluation contexts*)
  Inductive tectx : Set :=
    | Hole : tectx
    | E_Op1 : tectx -> te -> tectx
    | E_Op2 : nat -> tectx -> tectx
    | E_P1 : tectx -> tectx
    | E_P2 : tectx -> tectx
    | E_Pair1 : tectx -> te -> tectx
    | E_Pair2 : te -> tectx -> tectx.

  (* target primitive reduction steps*)
  Inductive tsem_p :  te -> te -> Prop :=
    (* possibly make parametric later *)
    | PR_Op : forall n1 n2 n, n = n1 + n2 -> tsem_p (Op (Num n1) (Num n2)) (Num n)
    | PR_P1 : forall tv1 tv2, tv tv1 -> tv tv2 -> tsem_p (P1 (Pair tv1 tv2)) tv1
    | PR_P2 : forall tv1 tv2, tv tv1 -> tv tv2 -> tsem_p (P2 (Pair tv1 tv2)) tv2.

  (*plug target contexts and expressions*)
  Inductive tplug : tectx -> te -> te -> Prop :=
    | Plug_Hole : forall te, tplug Hole te te
    | Plug_Op1 : forall te1 te1' te2 tctx, tplug tctx te1 te1' -> tplug (E_Op1 tctx te2) te1 (Op te1' te2)
    | Plug_Op2 : forall n1 te2 te2' tctx, tplug tctx te2 te2' -> tplug (E_Op2 n1 tctx) te2 (Op (Num n1) te2')
    | Plug_P1 : forall te te' tctx, tplug tctx te te' -> tplug (E_P1 tctx) te (P1 te')
    | Plug_P2 : forall te te' tctx, tplug tctx te te' -> tplug (E_P2 tctx) te (P2 te')
    | Plug_Pair1 : forall te te' tctx te1, tplug tctx te te' -> tplug (E_Pair1 tctx te1) te (Pair te' te1)
    | Plug_Pair2 : forall te te' tctx tv1, tplug tctx te te' -> tplug (E_Pair2 tv1 tctx) te (Pair tv1 te').

  (* target nonprimitive reductions: the ctx rule*)
  Inductive tsem : tectx -> te -> te -> Prop :=
    | Ctx : forall ectx1 te1 te2, tsem_p te1 te2 -> tsem ectx1 te1 te2.

  (* source small step structural semantics *)
  Inductive tsm_sem : te -> te -> Prop :=
    | SM_OP1 : forall te1 te2 te3, tsm_sem te1 te2 -> tsm_sem (Op te1 te3) (Op te2 te3)
    | SM_OP2 : forall te1 te2 n, tsm_sem te1 te2 -> tsm_sem (Op (Num n) te1) (Op (Num n) te2)
    | SM_OP : forall n1 n2 n, n = n1 + n2 -> tsm_sem (Op (Num n1) (Num n2)) (Num n)
    | SM_Pair1 : forall te1 te2 te3, tsm_sem te1 te2 -> tsm_sem (Pair te1 te3) (Pair te2 te3)
    | SM_Pair2 : forall te1 te2 tv1, tsm_sem te1 te2 -> tsm_sem (Pair tv1 te1) (Pair tv1 te2)
    | SM_P11 : forall te1 te2, tsm_sem te1 te2 -> tsm_sem (P1 te1) (P1 te2)
    | SM_P21 : forall te1 te2, tsm_sem te1 te2 -> tsm_sem (P2 te1) (P2 te2)
    | SM_P1 : forall tv1 tv2, tv tv1 -> tv tv2 -> tsm_sem (P1 (Pair tv1 tv2)) tv1
    | SM_P2 : forall tv1 tv2, tv tv1 -> tv tv2 -> tsm_sem (P2 (Pair tv1 tv2)) tv2.

  (*reflexive transitive closure of the single semantic step*)
  Inductive tsemrt : te -> te -> Prop :=
    | Refl : forall te1, tsemrt te1 te1
    | Tran: forall ctx te1 te2 te3 te1' te2', tsem ctx te1 te2 -> tplug ctx te1 te1' -> tplug ctx te2 te2' -> tsemrt te2' te3 -> tsemrt te1' te3.
    (*| Tran : forall te1 te2 te3, tsm_sem te1 te2 -> tsemrt te2 te3 -> tsemrt te1 te3.*)

(*target big step reduction that chains messages as queues*)
  Inductive tbsem : ts -> tq -> ts -> Prop :=
    | B_Skip : tbsem Skip Empty_q Skip
    | B_Seq : forall ts1 ts2 tq1 tq2, tbsem ts1 tq1 Skip -> tbsem ts2 tq2 Skip -> tbsem (Seq ts1 ts2) (Queue tq1 tq2) Skip
    | B_Ift : forall te1 ts1 ts2 tq1 n, n= 0 -> tsemrt te1 (Num n) -> tbsem ts1 tq1 Skip -> tbsem (Ifz te1 ts1 ts2) tq1 Skip
    | B_iff : forall te1 ts1 ts2 tq1 n, n<>0 -> tsemrt te1 (Num n) -> tbsem ts2 tq1 Skip -> tbsem (Ifz te1 ts1 ts2) tq1 Skip
    | B_Send : forall te1 n, tsemrt te1 (Num n) -> tbsem (Send te1) ( Sing_q (Msg_l (M_Num n)) Empty_q) Skip.

  (*target single behaviour (fat leadsto)*)
  Inductive tbeh : ts -> tq -> Prop :=
    | B_Sing : forall ts1 tq1 , tbsem ts1 tq1 Skip -> tbeh ts1 tq1.

  (* source language with vacuous context linking *)
  Definition tlang := Build_Language (fun (par : ts) (_ : unit) => par).

  (* source semantics *)
  Theorem exists_trace : forall s, exists q, tbeh s q.
  Admitted.

  Definition tsemt := Build_Semantics tlang tbeh exists_trace.

End Target.

Module Compiler.
  Module S := Source.
  Module T := Target.

  (*TODO: why bother with the well typed assumption below?*)
  (*compile expressions*)
  Inductive cmpe : S.se -> S.st -> T.te -> Prop :=
    | CMPE_Nat : forall sn tn, sn = tn -> S.swte (S.Num sn) S.Nat -> cmpe (S.Num sn) (S.Nat) (T.Num tn)
    | CMPE_Op : forall se1 se2 te1 te2, S.swte (S.Op se1 se2) S.Nat -> cmpe se1 S.Nat te1 -> cmpe se2 S.Nat te2 -> cmpe (S.Op se1 se2) S.Nat (T.Op te1 te2)
    | CMPE_Pair : forall se1 st1 te1 se2 st2 te2, S.swte (S.Pair se1 se2) (S.Times st1 st2) -> cmpe se1 st1 te1 -> cmpe se2 st2 te2 -> cmpe (S.Pair se1 se2) (S.Times st1 st2) (T.Pair te1 te2)
    | CMPE_P1 : forall se1 st1 te1, S.swte (S.P1 se1) st1 -> cmpe se1 st1 te1 -> cmpe (S.P1 se1) st1 (T.P1 te1)
    | CMPE_P2 : forall se1 st1 te1, S.swte (S.P2 se1) st1 -> cmpe se1 st1 te1 -> cmpe (S.P2 se1) st1 (T.P2 te1).

  (*given a source expression with a type, translate that into a target sequence.*)
  Inductive gensend : S.se -> S.st -> T.ts -> Prop :=
    | Snd_Base : forall n1 n2 n1' n2',
      S.swte (S.Pair (S.Num n1) (S.Num n2)) (S.Times S.Nat S.Nat) ->
      cmpe (S.Num n1) (S.Nat) (T.Num n1') ->
      cmpe (S.Num n2) (S.Nat) (T.Num n2') ->
      gensend (S.Pair (S.Num n1) (S.Num n2)) (S.Times S.Nat S.Nat) (T.Seq (T.Send (T.Num n1')) (T.Send (T.Num n2') ))
    | Snd_Ind : forall se1 st1 st2 ts1 ts2,
      gensend (S.P1 se1) (st1) (ts1) ->
      gensend (S.P2 se1) (st1) (ts2) ->
      gensend (se1) (S.Times st1 st2) (T.Seq ts1 ts2).

  (*compile statements*)
  Inductive cmp : S.ss -> T.ts -> Prop :=
    | CMP_Skip : cmp S.Skip T.Skip
    | CMP_Ifz : forall seg ss1 ss2 teg ts1 ts2, S.swts (S.Ifz seg ss1 ss2)-> cmpe seg S.Nat teg -> cmp ss1 ts1 -> cmp ss2 ts2 -> cmp (S.Ifz seg ss1 ss2) (T.Ifz teg ts1 ts2)
    (* What information is te1 giving us here? *)
    | CMP_Send : forall se1 st1 te1 ts1, S.swts (S.Send se1) -> cmpe se1 st1 te1 -> gensend se1 st1 ts1 -> cmp (S.Send se1) ts1
    | CMP_Seq : forall ss1 ss2 ts1 ts2, S.swts (S.Seq ss1 ss2) -> cmp ss1 ts1 -> cmp ss2 ts2 -> cmp (S.Seq ss1 ss2) (T.Seq ts1 ts2).

End Compiler.

Module TraceRelation.
  Module S := Source.
  Module T := Target.

  (*relate a source message to a target queue of msgs*)
  Inductive trel_msg : S.sm -> T.tq -> Prop :=
    | TR_NN : forall sn1 sn2 tn1 tn2,
      sn1=tn1 ->
      sn2=tn2 ->
      trel_msg  (S.Msg_ind (S.Msg_base sn1) (S.Msg_base sn2))
                (T.Queue
                    (T.Sing_q (T.Msg_l (T.M_Num tn1)) T.Empty_q)
                    (T.Sing_q (T.Msg_l (T.M_Num tn2)) T.Empty_q))
    | TR_NM : forall sn1 tn1 sm1 tq1,
      sn1=tn1 ->
      trel_msg  sm1
                tq1  ->
      trel_msg  (S.Msg_ind (S.Msg_base sn1) sm1 )
                (T.Queue
                  (T.Sing_q (T.Msg_l (T.M_Num tn1)) T.Empty_q)
                  (tq1))
    | TR_MN : forall tn2 sm1 tq1 tn1 sn1,
      sn1=tn1 ->
      trel_msg sm1 tq1 ->
      trel_msg  (S.Msg_ind sm1 (S.Msg_base sn1))
                (T.Queue
                    (T.Sing_q (T.Msg_l (T.M_Num tn1)) T.Empty_q)
                    (T.Sing_q (T.Msg_l (T.M_Num tn2)) T.Empty_q))
    | TR_MM : forall tq1 tq2 sm1 sm2,
      trel_msg sm1 tq1 ->
      trel_msg sm2 tq2 ->
      trel_msg  (S.Msg_ind sm1 sm2)
                (T.Queue tq1 tq2).

  (*relate a source queue to a target queue*)
  Inductive trel_q : S.sq -> T.tq -> Prop :=
    | TRQ_e : trel_q S.Empty_q T.Empty_q
    | TRQ_m : forall sq1 tq1 sm1 tq2,
      trel_q sq1 tq1 ->
      trel_msg sm1 tq2 ->
      trel_q
        (S.Queue sq1 (S.Sing_q (S.Msg_l sm1) S.Empty_q))
        (T.Queue tq1 tq2).
End TraceRelation.

(*proving RTCtilde for our instance with our definition*)
Module RTCprop.
  Module S := Source.
  Module T := Target.
  Module C := Compiler.
  Module R := TraceRelation.

(*the expression compiler is correct. i.e., it refines execution*)
  Theorem cc_expr : forall se1 se2 st te1 te2,
    C.cmpe se1 st te1 ->
    C.cmpe se2 st te2 ->
    T.tv te2 ->
    T.tsemrt te1 te2 ->
    S.ssemrt se1 se2 /\ S.sv se2.
  Proof.
    intros se1.
    induction se1; intros se2 st te1 te2 HCMPe1 HCMPe2 HTVe2 HTSeme1.
    - (* e = num *)
      inversion HCMPe1; subst.
      inversion HTSeme1; subst.
      +
        inversion HCMPe2; subst.
        split.
        *
          constructor.
        *
          constructor.
      + (* trans case should be contradictory *)
        inversion H;subst.
        inversion H0; subst.
        inversion H4; subst.
    - (* e = op*)
      inversion HCMPe1; subst.
      inversion HTSeme1; subst.
      * (* refl case should be contrad*)
        admit.
      * (* trans case*)
        inversion H; subst.
        inversion H4; subst.
        (* lost. i need to instatntiate the IH but i can't seem to get that the te1 ->* to a value te2, all i have is that the general expr reduces to a value but FFFF *)
         specialize (IHse1_1 _ _ _ _ H2 HCMPe2 HTVe2 HTSeme1) as [HR1 HV1].

  Admitted.

(*gensend is correct*)
  Theorem gensend_correct :
    forall se1 st1 st2 ts1 tq1,
      C.gensend se1 (S.Times st1 st2) ts1 ->
      T.tbsem ts1 tq1 T.Skip ->
    exists se2 sm1,
      S.ssemrt se1 se2 /\
      S.sv se2 /\
      S.sv_sm se2 sm1 /\
      R.trel_msg sm1 tq1.
  Proof.
  Admitted.

(*the statements compiler is correct with respect to tctilde*)
  Theorem rel_TC :
    forall ss ts tq,
      C.cmp ss ts ->
      T.tbeh ts tq ->
    exists sq,
      R.trel_q sq tq /\ S.sbeh ss sq.
  Proof.
    (* Induction on source statements. *)
    intros ss.
    induction ss; intros ts tq Hcmp Htbeh.
    - (* Skip. *)
      exists S.Empty_q.       (*instantiate existential*)
      inversion Hcmp; subst.  (* obtain what the compiled statement is by applying the definition of compilation to the current statment: skip  *)
      inversion Htbeh; subst. (* apply the definition of tbeh, obtain a tbsem step*)
      inversion H; subst. (* apply definition of tbsem and obtain the only queue produced by skip: the empty queue*)
      split. (* split the AND conjuncts *)
      + constructor. (* apply definiion (empty queue relation) to obtain that source and target empty queues are related*)
      + constructor. (* apply definition of sbeh to say that skip produces empty queue *)
        constructor. (* by definition of sbeh that amounts to proving sbsem step for skip, which we have in the S_Skip case, so this holds*)
    - (* inductive cases: seq, if and send *)
      (* Seq. *)
      inversion Hcmp; subst. (* by definition of the compiler we obtain a compiled target seq, we know the source is well typed and each subpart of the seq is compiled to target statements *)
      inversion Htbeh; subst. (* apply definition of tbeh and obtain a tbsem step for the target seq *)
      inversion H; subst. (* apply definition of tbsem for seq to know taht each substatement reduces with its own quque*)
      apply T.B_Sing in H5. (* apply the definition of tbsem in the B_sing case with the tbsem assumption to obtain the related tbeh -- we need this to apply the IH  *)
      apply T.B_Sing in H7. (* same as above *)
      specialize (IHss1 ts1 tq1 H2 H5) as [sq1 [Htrel1 Hsbeh1]]. (* instantiate the IH with the required things . . . (H5 is now rewritten to mathc the tbeh) and give the right names to the obtained HPs *)
      specialize (IHss2 ts2 tq2 H4 H7) as [sq2 [Htrel2 Hsbeh2]]. (* same *)
      exists (S.Queue sq1 sq2). (* we now have the two queues, which we join. *)
      split.
      + (* Either nested induction on queues or revised cases? *)
        admit.
      + constructor. (* apply definition of sbeh*)
        constructor. (* apply definition of sbsem, we need to prove that each substatement steps to skip, which we have in the sbeh format so we need to extract the sbsem out of each IH *)
        * inversion Hsbeh1; subst. (* extract the sbsem for the first statement *)
          assumption. (* we have it by IH*)
        * inversion Hsbeh2; subst.
          assumption. (* same as above for s2*)
    - (* Ifz. *)
      (*most of the rules follow the same intuition above, so nothing is commented there*)
      inversion Hcmp; subst. (*a*)
      inversion Htbeh; subst. (*a*)
      inversion H; subst. (*a*)
      + (* Then case. *)
        apply T.B_Sing in H10. (*a*)
        specialize (IHss1 ts1 tq H5 H10) as [sq1 [Htrel1 Hsbeh1]]. (*a*)
        exists sq1. (*a*)
        split. (*a*)
        * assumption. (*a*)
        * constructor.  (*a*)
          inversion H2; subst. (*a*)
          (* the next asserts build what is required to call teh auxiliary lemma to proceed *)
          assert (Hcmp' : C.cmpe (S.Num 0) S.Nat (T.Num 0)).
            (*proof of the assert*) constructor. reflexivity. apply S.T_Num. (*a*)
          assert (Htv : T.tv (T.Num 0)) by apply T.V_Num. (*a*)
          pose proof cc_expr _ _ _ _ _ H3 Hcmp' Htv H9 as [Hssemrt Hsv]. (*a*)
          inversion Hsbeh1; subst. (* obtain the sbsem step for the then branch *)
          apply S.B_Ift with 0. (* the sbsem of the if now holds by the related reduction, supply 0 as the value the guard reduces to (coq can't figure it out alone)*)
          (* these 3 below are the assumptions needed to call the b_ift rule above, they are all trivial*)
          reflexivity.
          assumption.
          assumption. (*a*)
          (* REMARK: instead of inversion 5 lines above, we had the following:
          econstructor.
          -- reflexivity.
          -- assumption.
          then here we had the inversion followed by assumption. This way seems cleaneer *)
      + (* Else case. *)
        apply T.B_Sing in H10.
        specialize (IHss2 ts2 tq H6 H10) as [sq2 [Htrel2 Hsbe2]].
        exists sq2.
        split.
        * assumption.
        * constructor.
          inversion H2; subst.
          assert (Hcomp2 : C.cmpe (S.Num n) S.Nat (T.Num n)).
            (* prove the assert *) constructor. reflexivity. apply S.T_Num.
          assert (Htv : T.tv (T.Num n)) by apply T.V_Num.
          pose proof cc_expr _ _ _ _ _ H3 Hcomp2 Htv H9 as [ Hssemrt Hsv].
          inversion Hsbe2; subst.
          apply S.B_iff with n; assumption.
    - (* Send. *)
      inversion Hcmp; subst.
      inversion Htbeh; subst.
      inversion H0; subst.
      Print gensend_correct.
      inversion H1; subst.
      inversion H4; subst.
      -- inversion H2; subst. (* op *)
      -- inversion H; subst ; try inversion H2. (* we analyse what gensend gives back. most are contradictions, only seq is valid *)
         pose proof gensend_correct _ _ _ _ _ H2 H.
         (* 2 cases: a flat pair of nums or a nested pair of pairs*)
         ** exists (S.Sing_q (S.Msg_l (S.Msg_ind (S.Msg_base n1) (S.Msg_base n2) )) S.Empty_q).
            destruct (H18) as [sexpr [smess [ Hssemrt [Hsv [Hsm_sv Htrelmsg] ] ] ] ].
         subst.
      admit.
  Admitted.

End RTCprop.
(* all that is below is garbage *)




(* tentative proof of cc_expr. old stuff, maybe useful*)
    induction se1 ; intros te1 te2 HCMPe1 HCMPe2 HTVe2 HTSeme1.
    - (*e = num*)
      inversion HCMPe1; subst.
      split.
      + (* two cases of the and*)
        inversion HTSeme1; subst. (* from the target semantics we get te2 is a the same tn*)
        inversion HCMPe2; subst. (* so from the compilation we get taht se2 is the same tn*)
        constructor. (* from the semrt perspective, this holds by refl.*)
        inversion H; subst. (* ? looking for a contradiction? *)
      +  (* prove the value *)
        inversion HTSeme1; subst. (* again from the target sem we know no step is taken*)
        * (* so in the refl case*)
          inversion HCMPe2; subst. (* we apply the related compiler case*)
          constructor.
        * (* in the non refl case -> look for contradiction*)
          inversion H; subst.
    - (* e = op*)
      inversion HCMPe1; subst.
      inversion HTSeme1; subst.
      * (* refl case: should be contradictory? *)
        admit.
      * (* trans case*)
        inversion H; subst.
        --
      specialize (IHse1_1 _ _ H2 HCMPe2 HTVe2 _) as [ IHSSem1 IHSv1].
      admit.
    - (* e = pair*)
      admit.
    - (* e = p1*)
      admit.
    - (* e = p2*)
      admit.



       intros se1 se2 st te1 te2 HCMPe1 HCMPe2 HTVe2 HTSeme1.
    (* i'd proceed by induction on the target reductions, so i invert that assumption*)
    inversion HTSeme1; subst.
    - (* refl case ... only the case for num should work here, the others are all contrad*)
      admit.
    - (* trans case .. now i have the IH for the second part of the reduction and a case analysis on the single reduction*)
      inversion H; subst.
      + (* primitive red = op*)
        split.
        *
          (* where are my IH?? *)
        admit.
      + (* pr = p1 *)
        admit.
      + (* pr = p2*)
        admit.



    - (* trans case .. now i have the IH for the second part of the reduction and a case analysis on the single reduction*)
      inversion H; subst.
      + (* primitive red = op*)
        split.
        *
          (* where are my IH?? *)
        admit.
      + (* pr = p1 *)
        admit.
      + (* pr = p2*)
        admit.





























































(*tctilde proven in the general framework. equivalent to ours but more convoluted*)
Module RTC.
  Module S := Source.
  Module T := Target.
  Module C := Compiler.
  Module R := TraceRelation.

  (* moved these here, this section is hopefully going to the dumpster*)
  Fixpoint cmpe' (se : S.se) : T.te :=
    match se with
    | S.Num n => T.Num n
    | S.Op se1 se2 => T.Op (cmpe' se1) (cmpe' se2)
    | S.Pair se1 se2 => T.Pair (cmpe' se1) (cmpe' se2)
    | S.P1 se1 => T.P1 (cmpe' se1)
    | S.P2 se2 => T.P2 (cmpe' se2)
    end.
  Fixpoint gensend' (se : S.se) : T.ts :=
    match se with
    | S.Pair (S.Num n1) (S.Num n2) => T.Seq (T.Send (T.Num n1)) (T.Send (T.Num n2))
    | S.Pair se1 se2 => T.Seq (gensend' se1) (gensend' se2)
    | _ => T.Skip (* bad case *)
    end.

  Fixpoint cmp' (ss : S.ss) : T.ts :=
    match ss with
    | S.Skip => T.Skip
    | S.Ifz seg ss1 ss2 => T.Ifz (cmpe' seg) (cmp' ss1) (cmp' ss2)
    | S.Send se1 => gensend' se1
    | S.Seq ss1 ss2 => T.Seq (cmp' ss1) (cmp' ss2)
    end.

  Definition chain := Build_CompilationChain S.slang T.tlang cmp' cmp' id.

  Fixpoint tcmp (st : S.st) : T.tt :=
    match st with
    | S.Nat => T.Nat
    | S.Times st1 st2 => T.Times (tcmp st1) (tcmp st2)
    end.

  Theorem cc_expr_val : forall se1 st1 te1, C.cmpe se1 st1 te1 -> T.tv te1 -> S.sv se1.
  Proof.
    intros se1 st1
  Admitted.


  (* Compilation is well-typed (if the input is well-typed). *)
  (* Theorem cc_wf : forall se st, S.swte se st -> T.twte (C.cmpe' se) (... st). *)
  Theorem cc_expr : forall se1 se2,
    T.tv (C.cmpe' se2) ->
    T.tsemrt (C.cmpe' se1) (C.cmpe' se2) ->
    S.ssemrt se1 se2 /\ S.sv se2.
  Proof.

    (* A not very promising start. *)

    induction se1;
      intros se2 Hval Hsem;
      simpl in *.
    - split.
      +

      inversion Hsem; subst. split.
      + econstructor.
    Restart.

    (* The intuitive starting point is promising. *)

    intros se1 se2 Hval Hsem.
    remember (C.cmpe' se1) as se1_comp eqn:Hse1.
    remember (C.cmpe' se2) as se2_comp eqn:Hse2.
    revert se1 se2 Hse1 Hse2 Hval.
    induction Hsem;
      intros se1 se2 Hse1 Hse2 Hval;
      subst.
    - assert (se1 = se2) by admit; subst se2.
      split.
      + constructor.
      + admit. (* Theorem out. *)
    - apply IHHsem.
      + (* After applying the IH, hopefully at the proper time, only this
           sub-goal is interesting. *)

        (* This sequence of inversions seems natural, but the equality seems
           too strong to prove. *)

        inversion H; subst.
        inversion H2; subst.
        * inversion H0; subst;
            inversion H1; subst.
          -- Print Target.Op.

        (* This variant leads to similar sub-goals. *)

        (* inversion H0; subst. *)
        (* * inversion H; subst. *)
        (*   inversion H2; subst. *)
        (*   -- inversion H1; subst. *)
        (*      rewrite <- H3 in H2. *)
        (*      (* Check T.PR_Op. *) *)
        (*      admit. *)
        (*   -- inversion H1; subst. *)
        (*      rewrite <- H3 in H2. *)
        (*      (* Check T.PR_P1. *) *)
        (*      admit. *)
        (*   -- admit. *)

        admit.

      + reflexivity.
      + assumption.
  Admitted.

  Theorem RTC :
    rel_TC Compiler.chain Source.ssemt Target.tsemt TraceRelation.trel_q.
  Admitted.
End RTC.








