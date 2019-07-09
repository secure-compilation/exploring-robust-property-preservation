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
  star_tr (transition C) (0, nil, s_init) l (pc, nil, s_fin).

(** Likewise, [infseq R] represents an infinite sequence of [R] transitions.
  (Also defined in file [Sequences].) *)

Definition mach_diverges (C: code) (s_init: state) s :=
  infseq_tr (transition C) s (0, nil, s_init).

Definition mach_silent (C : code) (s_init s_fin: state) l :=
  exists pc stack,
    star_tr (transition C) (0, nil, s_init) l (pc, stack, s_fin) /\
    infseq_silent (transition C) (pc, stack, s_fin).

(** A third case can occur: after a finite number of transitions,
  the machine hits a configuration where it cannot make any transition,
  and this state is not a final configuration ([Ihalt] instruction and empty stack).
  In this case, we say that the machine "goes wrong", which is
  a politically-correct way of saying that our program just crashed. *)

Definition mach_goes_wrong (C: code) (s_init: state) l :=
  exists pc, exists stk, exists s_fin,
  star_tr (transition C) (0, nil, s_init) l (pc, stk, s_fin)
  /\ irred_tr (transition C) (pc, stk, s_fin)
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
  code_at C pc = Some Ihalt -> irred_tr (transition C) (pc, stk, st).
Proof.
  unfold irred_tr; intros. unfold not; intros. inversion H0; congruence.
Qed.

Lemma terminates_unique:
  forall C st st1 st2 l1 l2, mach_terminates C st st1 l1 -> mach_terminates C st st2 l2 -> st1 = st2 /\ l1 = l2.
Proof.
  unfold mach_terminates; intros. destruct H as (pc1 & A1 & B1), H0 as (pc2 & A2 & B2).
  assert (((pc1, nil, st1) : configuration) = ((pc2, nil, st2) : configuration)).
  { eapply finseq_tr_unique; eauto using machine_deterministic, stop_irred. }
  assert (l1 = l2).
  { eapply finseq_tr_unique; eauto using machine_deterministic, stop_irred. }
  split; congruence.
Qed.

Lemma terminates_goeswrong_exclusive:
  forall C st st' l l', mach_terminates C st st' l -> mach_goes_wrong C st l' -> False.
Proof.
  unfold mach_terminates, mach_goes_wrong; intros.
  destruct H as (pc1 & A1 & B1), H0 as (pc2 & stk2 & st2 & A2 & B2 & C2).
  assert (((pc1, nil, st') : configuration) = ((pc2, stk2, st2) : configuration)).
  { eapply finseq_tr_unique; eauto using machine_deterministic, stop_irred. }
  inversion H. subst pc2 stk2 st2. destruct C2; congruence.
Qed.

Lemma terminates_diverges_exclusive:
  forall C st st' l s, mach_terminates C st st' l -> mach_diverges C st s -> False.
Proof.
  unfold mach_terminates, mach_diverges; intros.
  destruct H as (pc1 & A1 & B1).
  eapply infseq_tr_finseq_excl with (R := transition C); eauto using machine_deterministic, stop_irred.
Qed.

Lemma goeswrong_diverges_exclusive:
  forall C st l s, mach_goes_wrong C st l -> mach_diverges C st s -> False.
Proof.
  unfold mach_terminates, mach_diverges; intros. 
  destruct H as (pc2 & stk2 & st2 & A2 & B2 & C2).
  eapply infseq_tr_finseq_excl with (R := transition C); eauto using machine_deterministic, stop_irred.
Qed.
