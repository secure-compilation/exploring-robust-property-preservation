(** * Imp: Simple Imperative Programs *)

Set Warnings "-notation-overridden,-parsing".
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.

Require Import LanguageModel.
Require Import TraceModel.

Require Import Maps.

Set Bullet Behavior "Strict Subproofs".
(* ================================================================= *)
(** ** States *)

Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.

(* ################################################################# *)
(** * Expressions *)
(* ================================================================= *)
(** ** Syntax  *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(* ================================================================= *)
(** ** Evaluation *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

(* ################################################################# *)
(** * Commands *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.  (We choose this slightly awkward concrete syntax for the
    sake of being able to define Imp syntax using Coq's Notation
    mechanism.  In particular, we use [IFB] to avoid conflicting with
    the [if] notation from the standard library.)

     c ::= SKIP | x ::= a | c ;; c | IFB b THEN c ELSE c FI
         | WHILE b DO c END
*)
(**
    For example, here's factorial in Imp:

     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END

   When this command terminates, the variable [Y] will contain the
   factorial of the initial value of [X]. *)

(** Here is the formal definition of the abstract syntax of
    commands: *)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | COutput : aexp -> com.

(** As usual, we can use a few [Notation] declarations to make things
    more readable.  To avoid conflicts with Coq's built-in notations,
    we keep this light -- in particular, we don't introduce any
    notations for [aexps] and [bexps] to avoid confusion with the
    numeric and boolean operators we've already defined. *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'OUT' a" :=
  (COutput a) (at level 60).

(* ----------------------------------------------------------------- *)
(** *** An infinite loop: *)

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.
(* ================================================================= *)
(** ** Evaluation *)

Definition event : Events :=
  {| ev := nat;
     an_ev := 0;
     another_ev := 1;
     different_evs := O_S 0;
     eq_ev_dec := Nat.eq_dec
  |}.

Reserved Notation " c '/' st '==>' c' '/' st' '!' e" (at level 40, st at level 39, c' at level 39).


Inductive cstep : (com * state) -> list (ev event) -> (com * state)  -> Prop :=
  | CS_Ass : forall st i a n,
      aeval st a = n ->
      (i ::= a) / st ==> SKIP / (t_update st i n) ! []
  | CS_SeqStep : forall st c1 c1' st' c2 e,
      c1 / st ==> c1' / st' ! e ->
      (c1 ;; c2) / st ==> (c1' ;; c2) / st' ! e
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ==> c2 / st ! []
  | CS_IfTrue : forall st b c1 c2,
      beval st b = true ->
      IFB b THEN c1 ELSE c2 FI / st ==> c1 / st ! []
  | CS_IfFalse : forall st b c1 c2,
      beval st b = false ->
      IFB b THEN c1 ELSE c2 FI / st ==> c2 / st ! []
  | CS_While : forall st b c1,
      (WHILE b DO c1 END) / st
       ==> (IFB b THEN (c1 ;; (WHILE b DO c1 END)) ELSE SKIP FI) / st ! []
  | CS_Output : forall st a n,
      aeval st a = n ->
      (OUT a) / st ==> SKIP / st ! [n]

  where " c '/' st '==>' c' '/' st' '!' e" := (cstep (c,st) e (c',st')).

(** An important property of this reduction relation is that it is functional,
  in the sense that a given configuration can reduce to at most one configuration. *)

Reserved Notation "c1 '/' st '\\' st' '-->' l"
                  (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> list (ev event) -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st --> []
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ (t_update st x n) --> []
  | E_Seq : forall c1 c2 st st' st'' l l',
      c1 / st  \\ st' --> l ->
      c2 / st' \\ st'' --> l' ->
      (c1 ;; c2) / st \\ st'' --> (l ++ l')
  | E_IfTrue : forall st st' b c1 c2 l,
      beval st b = true ->
      c1 / st \\ st' --> l ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st' --> l
  | E_IfFalse : forall st st' b c1 c2 l,
      beval st b = false ->
      c2 / st \\ st' --> l ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st' --> l
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st --> []
  | E_WhileTrue : forall st st' st'' b c l l',
      beval st b = true ->
      c / st \\ st' --> l ->
      (WHILE b DO c END) / st' \\ st'' --> l' ->
      (WHILE b DO c END) / st \\ st'' --> (l ++ l')
  | E_Output : forall st a n,
      aeval st a = n ->
      (OUT a) / st \\ st --> [n]

  where "c1 '/' st '\\' st' '-->' l" := (ceval c1 st st' l).

(* ================================================================= *)
(** ** Determinism of Evaluation *)

(** Changing from a computational to a relational definition of
    evaluation is a good move because it frees us from the artificial
    requirement that evaluation should be a total function.  But it
    also raises a question: Is the second definition of evaluation
    really a partial function?  Or is it possible that, beginning from
    the same state [st], we could evaluate some command [c] in
    different ways to reach two different output states [st'] and
    [st'']?

    In fact, this cannot happen: [ceval] _is_ a partial function: *)
Theorem ceval_deterministic_states : forall c st st1 st2 l1 l2,
    c / st \\ st1 --> l1 ->
    c / st \\ st2 --> l2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 l1 l2 E1 E2.
  generalize dependent l2. generalize dependent st2. 
  induction E1;
           intros st2 l2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { eapply IHE1_1; eassumption. }
    subst st'0.
    eapply IHE1_2. eassumption.
  - (* E_IfTrue, b1 evaluates to true *)
    eapply IHE1. eassumption.
  - (* E_IfTrue,  b1 evaluates to false (contradiction) *)
    now rewrite H in *. 
  - (* E_IfFalse, b1 evaluates to true (contradiction) *)
    now rewrite H in *.
  - (* E_IfFalse, b1 evaluates to false *)
    eapply IHE1. eassumption.
  - (* E_WhileFalse, b1 evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b1 evaluates to true (contradiction) *)
    now rewrite H in *. 
  - (* E_WhileTrue, b1 evaluates to false (contradiction) *)
    now rewrite H in *.
  - (* E_WhileTrue, b1 evaluates to true *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) eapply IHE1_1; eassumption. }
    subst st'0.
    eapply IHE1_2. eassumption.
  - (* E_Output *)
    reflexivity.
Qed.

Theorem ceval_deterministic_output : forall c st st' l1 l2,
    c / st \\ st' --> l1 ->
    c / st \\ st' --> l2 ->
    l1 = l2.
Proof.
  intros c st st' l1 l2 E1 E2.
  generalize dependent l2.
  induction E1;
    intros l2 E2; inversion E2; subst;
      try reflexivity;
      try congruence.
  - assert (st'0 = st').
    { eapply ceval_deterministic_states.
      eapply H1. eassumption. }
    subst st'0.
    rewrite (IHE1_1 _ H1).
    rewrite (IHE1_2 _ H5).
    reflexivity.
  - eapply IHE1; eassumption.
  - auto.
  - assert (st'0 = st') by (now eapply ceval_deterministic_states; eauto).
    subst st'0.
    rewrite (IHE1_1 _ H3).
    rewrite (IHE1_2 _ H7).
    reflexivity.
Qed.

Theorem ceval_deterministic: forall c st st1 st2 l l',
     c / st \\ st1 --> l ->
     c / st \\ st2 --> l' ->
     st1 = st2 /\ l = l'.
Proof.
  intros c st st1 st2 l l' H H0.
  rewrite (ceval_deterministic_states c st st1 st2 l l') in *;
    try assumption.
  split; first reflexivity.
  eapply ceval_deterministic_output; eassumption.
Qed.

Definition imp : LanguageModel.Language :=
  {| prg := com;
     par := com;
     ctx := unit;
     plug := fun p c => p
  |}.

Definition event_imp : TraceModel.Events := event.

Definition endstate_imp : TraceModel.Endstates :=
  {| es := state;
     an_es := empty_state
  |}.

Definition trace_imp := @TraceModel.trace event_imp endstate_imp.
