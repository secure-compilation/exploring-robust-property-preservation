Require Import Bool Arith Omega List Coq.Program.Equality.
Require Import Maps Imp.
Require Import List.
Import ListNotations.
Require Import Sequences.
Require Import TraceModel.


Set Bullet Behavior "Strict Subproofs".
(** This chapter defines a compiler from the Imp language to a virtual machine
  (a small subset of the Java Virtual Machine) and proves that this
  compiler preserves the semantics of the source programs. *)

(** * 1. The virtual machine. *)

(** The machine operates on a code [c] (a fixed list of instructions)
  and three variable components:
- a program counter, denoting a position in [c]
- a state assigning integer values to variables
- an evaluation stack, containing integers.
*)

(** The instruction set of the machine. *)

Inductive instruction: Type :=
  | Iconst(n: nat)                 (**r push integer [n] on stack *)
  | Ivar(x: id)                    (**r push the value of variable [x] *)
  | Isetvar(x: id)                 (**r pop an integer, assign it to variable [x] *)
  | Iadd                           (**r pop [n2], pop [n1], push back [n1+n2] *)
  | Isub                           (**r pop [n2], pop [n1], push back [n1-n2] *)
  | Imul                           (**r pop [n2], pop [n1], push back [n1*n2] *)
  | Ibranch_forward(ofs: nat)      (**r skip [ofs] instructions forward *)
  | Ibranch_backward(ofs: nat)     (**r skip [ofs] instructions backward *)
  | Ibeq(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1=n2] *)
  | Ibne(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1<>n2] *)
  | Ible(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1<=n2] *)
  | Ibgt(ofs: nat)                 (**r pop [n2], pop [n1], skip [ofs] forward if [n1>n2] *)
  | Iout                         (**r pop an integer, outputs it *)
  | Ihalt.                         (**r terminate execution successfully *)

Definition code := list instruction.

(** [code_at C pc = Some i] if [i] is the instruction at position [pc]
  in the list of instructions [C]. *)

Fixpoint code_at (C: code) (pc: nat) : option instruction :=
  match C, pc with
  | nil, _ => None
  | i :: C', O => Some i
  | i :: C', S pc' => code_at C' pc'
  end.

Definition stack := list nat.

(** The semantics of the virtual machine is given in small-step style,
  as a transition relation between machine configuration: triples
  (program counter, evaluation stack, variable state).
  The transition relation is parameterized by the code [c].
  There is one transition rule for each kind of instruction,
  except [Ihalt], which has no transition. *)

Definition configuration := (nat * stack * state)%type.

Inductive transition (C: code): configuration -> list (nat) -> configuration -> Prop :=
  | trans_const: forall pc stk s n,
      code_at C pc = Some(Iconst n) ->
      transition C (pc, stk, s) [] (pc + 1, n :: stk, s)
  | trans_var: forall pc stk s x,
      code_at C pc = Some(Ivar x) ->
      transition C (pc, stk, s) [] (pc + 1, s x :: stk, s)
  | trans_out: forall pc stk s n,
      code_at C pc = Some Iout ->
      transition C (pc, n :: stk, s) [n] (pc + 1, stk, s)
  | trans_setvar: forall pc stk s x n,
      code_at C pc = Some(Isetvar x) ->
      transition C (pc, n :: stk, s) [] (pc + 1, stk, t_update s x n)
  | trans_add: forall pc stk s n1 n2,
      code_at C pc = Some(Iadd) ->
      transition C (pc, n2 :: n1 :: stk, s) [] (pc + 1, (n1 + n2) :: stk, s)
  | trans_sub: forall pc stk s n1 n2,
      code_at C pc = Some(Isub) ->
      transition C (pc, n2 :: n1 :: stk, s) [] (pc + 1, (n1 - n2) :: stk, s)
  | trans_mul: forall pc stk s n1 n2,
      code_at C pc = Some(Imul) ->
      transition C (pc, n2 :: n1 :: stk, s) [] (pc + 1, (n1 * n2) :: stk, s)
  | trans_branch_forward: forall pc stk s ofs pc',
      code_at C pc = Some(Ibranch_forward ofs) ->
      pc' = pc + 1 + ofs ->
      transition C (pc, stk, s) [] (pc', stk, s)
  | trans_branch_backward: forall pc stk s ofs pc',
      code_at C pc = Some(Ibranch_backward ofs) ->
      pc' = pc + 1 - ofs ->
      transition C (pc, stk, s) [] (pc', stk, s)
  | trans_beq: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ibeq ofs) ->
      pc' = (if beq_nat n1 n2 then pc + 1 + ofs else pc + 1) ->
      transition C (pc, n2 :: n1 :: stk, s) [] (pc', stk, s)
  | trans_bne: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ibne ofs) ->
      pc' = (if beq_nat n1 n2 then pc + 1 else pc + 1 + ofs) ->
      transition C (pc, n2 :: n1 :: stk, s) [] (pc', stk, s)
  | trans_ble: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ible ofs) ->
      pc' = (if leb n1 n2 then pc + 1 + ofs else pc + 1) ->
      transition C (pc, n2 :: n1 :: stk, s) [] (pc', stk, s)
  | trans_bgt: forall pc stk s ofs n1 n2 pc',
      code_at C pc = Some(Ibgt ofs) ->
      pc' = (if leb n1 n2 then pc + 1 else pc + 1 + ofs) ->
      transition C (pc, n2 :: n1 :: stk, s) [] (pc', stk, s).

(** As usual with small-step semantics, we form sequences of machine transitions
  to define the behavior of a code.  We always start with [pc = 0]
  and an empty evaluation stack.  We stop successfully if [pc] points
  to an [Ihalt] instruction and the evaluation stack is empty.

  If [R] is a binary relation, [star R] is its reflexive transitive closure.
  (See file [Sequences] for the definition.)  [star (transition C)]
  therefore represents a sequence of  zero, one or several machine transitions.
*)

Definition mach_terminates (C: code) (s_init s_fin: state) l :=
  exists pc,
  code_at C pc = Some Ihalt /\
  star (transition C) (0, nil, s_init) l (pc, nil, s_fin).

(** Likewise, [infseq R] represents an infinite sequence of [R] transitions.
  (Also defined in file [Sequences].) *)

Definition mach_diverges (C: code) (s_init: state) s :=
  infseq (transition C) s (0, nil, s_init).

Definition mach_reacts (C: code) (s_init: state) s :=
  infseq_prod (transition C) s (0, nil, s_init).

Definition mach_silent (C : code) (s_init s_fin: state) l :=
  exists pc stack,
    star (transition C) (0, nil, s_init) l (pc, stack, s_fin) /\
    infseq_silent (transition C) (pc, stack, s_fin).

(** A third case can occur: after a finite number of transitions,
  the machine hits a configuration where it cannot make any transition,
  and this state is not a final configuration ([Ihalt] instruction and empty stack).
  In this case, we say that the machine "goes wrong", which is
  a politically-correct way of saying that our program just crashed. *)

Definition mach_goes_wrong (C: code) (s_init: state) l :=
  exists pc, exists stk, exists s_fin,
  star (transition C) (0, nil, s_init) l (pc, stk, s_fin)
  /\ irred (transition C) (pc, stk, s_fin)
  /\ (code_at C pc <> Some Ihalt \/ stk <> nil).

(** An important property of the virtual machine is that it is deterministic:
  from a given configuration, it can transition to at most one other configuration. *)

Lemma machine_deterministic:
  forall C config config1 config2 e1 e2,
  transition C config e1 config1 -> transition C config e2 config2 -> config1 = config2 /\ e1 = e2.
Proof.
  intros. inversion H; subst; inversion H0; split; try congruence.
  destruct (beq_nat n1 n2); congruence.
  destruct (beq_nat n1 n2); congruence.
  destruct (leb n1 n2); congruence.
  destruct (leb n1 n2); congruence.
Qed.

Lemma machine_deterministic_config:
  forall C config config1 config2 e1 e2,
    transition C config e1 config1 -> transition C config e2 config2 -> config1 = config2.
Proof.
  intros C config config1 config2 e1 e2 H H0.
  now destruct (machine_deterministic _ _ _ _ _ _ H H0).
Qed.

Lemma machine_deterministic_event:
  forall C config config1 config2 e1 e2,
    transition C config e1 config1 -> transition C config e2 config2 -> e1 = e2.
Proof.
  intros C config config1 config2 e1 e2 H H0.
  now destruct (machine_deterministic _ _ _ _ _ _ H H0).
Qed.

(** As a consequence of this determinism, it follows that
  the final state of a terminating program is unique,
  and that a program cannot both terminate and diverge,
  or terminate and go wrong, or diverge and go wrong.
  These results follow from the generic determinism properties 
  found at the end of module [Sequence]. *)

Remark stop_irred:
  forall C pc stk st,
  code_at C pc = Some Ihalt -> irred (transition C) (pc, stk, st).
Proof.
  unfold irred; intros. unfold not; intros. inversion H0; congruence.
Qed.

Lemma terminates_unique:
  forall C st st1 st2 l1 l2, mach_terminates C st st1 l1 -> mach_terminates C st st2 l2 -> st1 = st2 /\ l1 = l2.
Proof.
  unfold mach_terminates; intros. destruct H as (pc1 & A1 & B1), H0 as (pc2 & A2 & B2).
  assert (((pc1, nil, st1) : configuration) = ((pc2, nil, st2) : configuration)).
  { eapply finseq_unique; eauto using machine_deterministic, stop_irred. }
  assert (l1 = l2).
  { eapply finseq_unique; eauto using machine_deterministic, stop_irred. }
  split; congruence.
Qed.

Lemma goeswrong_unique:
  forall C st l1 l2, mach_goes_wrong C st l1 -> mach_goes_wrong C st l2 -> l1 = l2.
Proof.
  unfold mach_goes_wrong; intros C st l1 l2 H H0.
  destruct H as (pc1 & stk1 & s_fin1 & H1 & H1' & H1'').
  destruct H0 as (pc2 & stk2 & s_fin2 & H2 & H2' & H2'').
  eapply finseq_unique; eauto using machine_deterministic, stop_irred.
Qed.

Lemma silent_unique:
  forall C st st1 st2 l1 l2, mach_silent C st st1 l1 -> mach_silent C st st2 l2 -> l1 = l2.
Proof.
  unfold mach_silent; intros C st st1 st2 l1 l2 H H0.
  destruct H as (pc1 & stk1 & Hstar1 & H1 ).
  destruct H0 as (pc2 & stk2 & Hstar2 & H2 ).
  pose proof (star_star_inv (machine_deterministic C) Hstar1 Hstar2)
    as [[l [Hinv1 Hinv2]] | [l [Hinv1 Hinv2]]]; subst.
  pose proof (infseq_silent_star_inv (machine_deterministic C) Hinv2 H2)
    as [Hinv1' Hinv2'].
  subst; now apply app_nil_r.
  pose proof (infseq_silent_star_inv (machine_deterministic C) Hinv2 H1)
    as [Hinv1' Hinv2'].
  subst; now rewrite app_nil_r.
Qed.

CoInductive stream_eq' {A : Type} : @Stream.stream A -> @Stream.stream A -> Prop :=
  eq'_scons : forall l s1 s2,
    l <> [] -> stream_eq' s1 s2 -> stream_eq' (Stream.app_list_stream l s1) (Stream.app_list_stream l s2).

Lemma reacts_unique:
  forall C st s1 s2, mach_reacts C st s1 -> mach_reacts C st s2 -> Stream.stream_eq s1 s2.
Proof.
  assert (reacts_unique' : forall C a s1 s2, infseq_prod (transition C) s1 a -> infseq_prod (transition C) s2 a -> stream_eq' s1 s2).
  cofix Hfix; intros.
  inversion H; subst; clear H. inversion H0; subst; clear H0.
  pose proof (infseq_prod_inv).
  specialize (H0 _ _ _ (machine_deterministic C) _ _ _ H1 _ _ _ _ H H2 H4 H3 H5).
  destruct H0 as [a' [l1 [s1' [s2' [H11 [H12 [H13 [H14 H15]]]]]]]]; auto.
  rewrite H14; rewrite H15.
  econstructor; eauto.
  assert (forall A s1 s2, @stream_eq' A s1 s2 -> Stream.stream_eq s1 s2).
  {
    cofix Hfix. intros A s1 s2 H.
    inversion H; subst; clear H.
    destruct l. congruence.
    simpl.
    destruct l. simpl. constructor. apply Hfix. auto.
    constructor. apply Hfix. constructor. congruence.
    assumption.
  }
  intros C st s1 s2 H0 H1.
  unfold mach_reacts in *.
  apply H. eapply reacts_unique'; eauto.
Qed.

Lemma terminates_goeswrong_exclusive:
  forall C st st' l l', mach_terminates C st st' l -> mach_goes_wrong C st l' -> False.
Proof.
  unfold mach_terminates, mach_goes_wrong; intros.
  destruct H as (pc1 & A1 & B1), H0 as (pc2 & stk2 & st2 & A2 & B2 & C2).
  assert (((pc1, nil, st') : configuration) = ((pc2, stk2, st2) : configuration)).
  { eapply finseq_unique; eauto using machine_deterministic, stop_irred. }
  inversion H. subst pc2 stk2 st2. destruct C2; congruence.
Qed.

Lemma terminates_diverges_exclusive:
  forall C st st' l s, mach_terminates C st st' l -> mach_diverges C st s -> False.
Proof.
  unfold mach_terminates, mach_diverges; intros.
  destruct H as (pc1 & A1 & B1).
  eapply infseq_finseq_excl with (R := transition C); eauto using machine_deterministic, stop_irred.
Qed.


Lemma terminates_reacts_exclusive:
  forall C st st' l s, mach_terminates C st st' l -> mach_reacts C st s -> False.
Proof.
  unfold mach_terminates, mach_reacts; intros.
  destruct H as (pc1 & A1 & B1).
  eapply infseq_finseq_excl with (R := transition C); eauto using machine_deterministic, stop_irred.
  eapply infseq_prod_infseq; eauto.
Qed.

Lemma goeswrong_diverges_exclusive:
  forall C st l s, mach_goes_wrong C st l -> mach_diverges C st s -> False.
Proof.
  unfold mach_terminates, mach_diverges; intros. 
  destruct H as (pc2 & stk2 & st2 & A2 & B2 & C2).
  eapply infseq_finseq_excl with (R := transition C); eauto using machine_deterministic, stop_irred.
Qed.

Lemma goeswrong_silent_exclusive:
  forall C st st' l l', mach_goes_wrong C st l -> mach_silent C st st' l' -> False.
Proof.
  intros C st st' l l' H H0.
  destruct H as [pc [s_fin [H1 H2]]].
  destruct H0 as [pc' [stk' [H1' H2']]].
  eapply infseq_silent_finseq_excl.
  eauto using machine_deterministic.
  eauto. eapply H2. eauto. eauto using stop_irred.
  destruct H2 as [A1 [A2 A3]].
  eapply A2.
Qed.

Lemma goeswrong_reacts_exclusive:
  forall C st l s, mach_goes_wrong C st l -> mach_reacts C st s -> False.
Proof.
  unfold mach_terminates, mach_reacts; intros.
  destruct H as [pc [s_fin [H1 [H2 [H3 H4]]]]].
  eapply infseq_finseq_excl.
  eauto using machine_deterministic.
  eauto. eapply H3.
  eapply infseq_prod_infseq; eauto.
Qed.

Lemma terminates_silent_exclusive:
  forall C st st' st'' l l', mach_terminates C st st' l -> mach_silent C st st'' l' -> False.
Proof.
  unfold mach_terminates, mach_silent; intros.
  destruct H as [pc [H1 H2]].
  destruct H0 as [pc' [stk' [H1' H2']]].
  eapply infseq_silent_finseq_excl.
  eauto using machine_deterministic.
  eauto. eapply H2. eauto. eauto using stop_irred.
Qed.

(* Lemma silent_diverges_exclusive: *)
(*   forall C st st' l s, mach_diverges C st s -> mach_silent C st st' l -> False. *)
(* Proof. *)
(*   unfold mach_diverges, mach_silent; intros. *)
(*   destruct H0 as [pc [stk [H1 H2]]]. *)
(*   (* eapply infseq_silent_excl. *) *)
(*   eauto using machine_deterministic. *)
(* Admitted. *)


Lemma silent_reacts_exclusive:
  forall C st st' s l,
    mach_reacts C st s -> mach_silent C st st' l -> False.
Proof.
  intros C st st' s l H H0.
  destruct H0 as [pc [stk [H0 H1]]].
  (* inversion H; subst; clear H. *)
  pose proof (star_infseq_prod_inv (machine_deterministic C) H0 H)
    as [s' [H2 H3]].
  inversion H2; subst; clear H2.
  pose proof (infseq_silent_star_inv (machine_deterministic C) H4 H1).
  destruct H2; now congruence.
Qed.
