Require Import Bool Arith Omega List Coq.Program.Equality.
Require Import Maps Imp.
Require Import List.
Import ListNotations.
Require Import Sequences.
Require Import TraceModel.
Require Import Machine.

Set Bullet Behavior "Strict Subproofs".


Definition stack_limit := 50.

Definition configuration_limited := option configuration.
Inductive transition_limited (C : code) : configuration_limited -> list nat -> configuration_limited -> Prop :=
| transition_OOM : forall pc1 stk1 st1 pc2 stk2 st2 l,
    transition C (pc1, stk1, st1) l (pc2, stk2, st2) ->
    stack_limit <= List.length stk2 ->
    transition_limited C (Some (pc1, stk1, st1)) [] None
| transition_some : forall pc1 stk1 st1 pc2 stk2 st2 l,
    transition C (pc1, stk1, st1) l (pc2, stk2, st2) ->
    List.length stk2 < stack_limit ->
    transition_limited C (Some (pc1, stk1, st1)) l (Some (pc2, stk2, st2)).

(** As usual with small-step semantics, we form sequences of machine transitions
  to define the behavior of a code.  We always start with [pc = 0]
  and an empty evaluation stack.  We stop successfully if [pc] points
  to an [Ihalt] instruction and the evaluation stack is empty.

  If [R] is a binary relation, [star R] is its reflexive transitive closure.
  (See file [Sequences] for the definition.)  [star (transition_limited C)]
  therefore represents a sequence of  zero, one or several machine transition_limiteds.
*)

Definition mach_terminates (C: code) (s_init s_fin: state) l :=
  exists pc,
  code_at C pc = Some Ihalt /\
  star_tr (transition_limited C) (Some (0, nil, s_init)) l (Some (pc, nil, s_fin)).

Definition mach_OOM (C : code) (s_init : state) l :=
    star_tr (transition_limited C) (Some (0, nil, s_init)) l None.

(** Likewise, [infseq R] represents an infinite sequence of [R] transition_limiteds.
  (Also defined in file [Sequences].) *)

Definition mach_diverges (C: code) (s_init: state) s :=
  infseq_tr (transition_limited C) s (Some (0, nil, s_init)).

Definition mach_silent (C : code) (s_init s_fin: state) l :=
  exists pc stack,
    star_tr (transition_limited C) (Some (0, nil, s_init)) l (Some (pc, stack, s_fin)) /\
    infseq_silent (transition_limited C) (Some (pc, stack, s_fin)).

(** A third case can occur: after a finite number of transition_limiteds,
  the machine hits a configuration_limited where it cannot make any transition_limited,
  and this state is not a final configuration_limited ([Ihalt] instruction and empty stack).
  In this case, we say that the machine "goes wrong", which is
  a politically-correct way of saying that our program just crashed. *)

Definition mach_goes_wrong (C: code) (s_init: state) l :=
  exists pc, exists stk, exists s_fin,
  star_tr (transition_limited C) (Some (0, nil, s_init)) l (Some (pc, stk, s_fin))
  /\ irred_tr (transition_limited C) (Some (pc, stk, s_fin))
  /\ (code_at C pc <> Some Ihalt \/ stk <> nil).

(** An important property of the virtual machine is that it is deterministic:
  from a given configuration_limited, it can transition_limited to at most one other configuration_limited. *)

Lemma machine_deterministic:
  forall C config config1 config2 e1 e2,
  transition_limited C config e1 config1 -> transition_limited C config e2 config2 -> config1 = config2 /\ e1 = e2.
Proof.
  intros.
  inversion H; inversion H0; subst; split; try congruence;
    match goal with
    | Heq: Some _ = Some _ |- _ => inversion Heq; subst; clear Heq
    end;
  (repeat match goal with
            | Htrans: transition _ _ _ _ |- _ => inversion Htrans; subst; clear Htrans
            end);
    try congruence;
  match goal with
  | Heq1 : code_at _ _ = Some _, Heq2 : code_at _ _ = Some _ |- _ =>
    rewrite Heq1 in Heq2; inversion Heq2; subst; clear Heq2
  end;
     try omega.
  destruct (beq_nat n1 n2); congruence.
  destruct (beq_nat n1 n2); congruence.
  destruct (leb n1 n2); congruence.
  destruct (leb n1 n2); congruence.
Qed.

Lemma machine_deterministic_config:
  forall C config config1 config2 e1 e2,
    transition_limited C config e1 config1 -> transition_limited C config e2 config2 -> config1 = config2.
Proof.
  intros C config config1 config2 e1 e2 H H0.
  now destruct (machine_deterministic _ _ _ _ _ _ H H0).
Qed.

Lemma machine_deterministic_event:
  forall C config config1 config2 e1 e2,
    transition_limited C config e1 config1 -> transition_limited C config e2 config2 -> e1 = e2.
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
  code_at C pc = Some Ihalt -> irred_tr (transition_limited C) (Some (pc, stk, st)).
Proof.
  unfold irred_tr; intros. unfold not; intros.
  inversion H0 as [? ? ? ? ? ? ? Htrans| ? ? ? ? ? ? ? Htrans]; subst;
    inversion Htrans; congruence.
Qed.

Lemma terminates_unique:
  forall C st st1 st2 l1 l2, mach_terminates C st st1 l1 -> mach_terminates C st st2 l2 -> st1 = st2 /\ l1 = l2.
Proof.
  unfold mach_terminates; intros. destruct H as (pc1 & A1 & B1), H0 as (pc2 & A2 & B2).
  assert ((Some (pc1, nil, st1) : configuration_limited) = (Some (pc2, nil, st2) : configuration_limited)).
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
  assert ((Some (pc1, nil, st') : configuration_limited) = (Some (pc2, stk2, st2) : configuration_limited)).
  { eapply finseq_tr_unique; eauto using machine_deterministic, stop_irred. }
  inversion H. subst pc2 stk2 st2. destruct C2; congruence.
Qed.

Lemma terminates_diverges_exclusive:
  forall C st st' l s, mach_terminates C st st' l -> mach_diverges C st s -> False.
Proof.
  unfold mach_terminates, mach_diverges; intros.
  destruct H as (pc1 & A1 & B1).
  eapply infseq_tr_finseq_excl with (R := transition_limited C); eauto using machine_deterministic, stop_irred.
Qed.

Lemma goeswrong_diverges_exclusive:
  forall C st l s, mach_goes_wrong C st l -> mach_diverges C st s -> False.
Proof.
  unfold mach_terminates, mach_diverges; intros. 
  destruct H as (pc2 & stk2 & st2 & A2 & B2 & C2).
  eapply infseq_tr_finseq_excl with (R := transition_limited C); eauto using machine_deterministic, stop_irred.
Qed.
