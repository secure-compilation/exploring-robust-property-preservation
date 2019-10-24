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
  star (transition_limited C) (Some (0, nil, s_init)) l (Some (pc, nil, s_fin)).

Definition mach_OOM (C : code) (s_init : state) l :=
    star (transition_limited C) (Some (0, nil, s_init)) l None.

(** Likewise, [infseq R] represents an infinite sequence of [R] transition_limiteds.
  (Also defined in file [Sequences].) *)

Definition mach_diverges (C: code) (s_init: state) s :=
  infseq (transition_limited C) s (Some (0, nil, s_init)).

Definition mach_reacts (C: code) (s_init: state) s :=
  infseq_prod (transition_limited C) s (Some (0, nil, s_init)).

Definition mach_silent (C : code) (s_init s_fin: state) l :=
  exists pc stack,
    star (transition_limited C) (Some (0, nil, s_init)) l (Some (pc, stack, s_fin)) /\
    infseq_silent (transition_limited C) (Some (pc, stack, s_fin)).

(** A third case can occur: after a finite number of transition_limiteds,
  the machine hits a configuration_limited where it cannot make any transition_limited,
  and this state is not a final configuration_limited ([Ihalt] instruction and empty stack).
  In this case, we say that the machine "goes wrong", which is
  a politically-correct way of saying that our program just crashed. *)

Definition mach_goes_wrong (C: code) (s_init: state) l :=
  exists pc, exists stk, exists s_fin,
  star (transition_limited C) (Some (0, nil, s_init)) l (Some (pc, stk, s_fin))
  /\ irred (transition_limited C) (Some (pc, stk, s_fin))
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
  code_at C pc = Some Ihalt -> irred (transition_limited C) (Some (pc, stk, st)).
Proof.
  unfold irred; intros. unfold not; intros.
  inversion H0 as [? ? ? ? ? ? ? Htrans| ? ? ? ? ? ? ? Htrans]; subst;
    inversion Htrans; congruence.
Qed.

Lemma terminates_unique:
  forall C st st1 st2 l1 l2, mach_terminates C st st1 l1 -> mach_terminates C st st2 l2 -> st1 = st2 /\ l1 = l2.
Proof.
  unfold mach_terminates; intros. destruct H as (pc1 & A1 & B1), H0 as (pc2 & A2 & B2).
  assert ((Some (pc1, nil, st1) : configuration_limited) = (Some (pc2, nil, st2) : configuration_limited)).
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

Lemma OOM_unique:
  forall C st l1 l2, mach_OOM C st l1 -> mach_OOM C st l2 -> l1 = l2.
Proof.
  unfold mach_OOM; intros C st l1 l2 H H0.
  eapply finseq_unique; eauto using machine_deterministic;
    intros c l Hn; inversion Hn.
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
  assert (reacts_unique' : forall C a s1 s2, infseq_prod (transition_limited C) s1 a -> infseq_prod (transition_limited C) s2 a -> stream_eq' s1 s2).
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
  assert ((Some (pc1, nil, st') : configuration_limited) = (Some (pc2, stk2, st2) : configuration_limited)).
  { eapply finseq_unique; eauto using machine_deterministic, stop_irred. }
  inversion H. subst pc2 stk2 st2. destruct C2; congruence.
Qed.

Lemma terminates_OOM_exclusive:
  forall C st st' l l', mach_terminates C st st' l -> mach_OOM C st l' -> False.
Proof.
  unfold mach_terminates, mach_OOM; intros.
  destruct H as (pc1 & A1 & B1). (* H0 as (pc2 & stk2 & st2 & A2 & B2 & C2). *)
  assert ((Some (pc1, nil, st') : configuration_limited) = (None : configuration_limited)).
  { eapply finseq_unique; eauto using machine_deterministic, stop_irred.
    unfold irred.  intros b l'' Hn. inversion Hn. }
  congruence.
Qed.

Lemma terminates_diverges_exclusive:
  forall C st st' l s, mach_terminates C st st' l -> mach_diverges C st s -> False.
Proof.
  unfold mach_terminates, mach_diverges; intros.
  destruct H as (pc1 & A1 & B1).
  eapply infseq_finseq_excl with (R := transition_limited C); eauto using machine_deterministic, stop_irred.
Qed.

Lemma terminates_reacts_exclusive:
  forall C st st' l s, mach_terminates C st st' l -> mach_reacts C st s -> False.
Proof.
  unfold mach_terminates, mach_reacts; intros.
  destruct H as (pc1 & A1 & B1).
  eapply infseq_finseq_excl with (R := transition_limited C); eauto using machine_deterministic, stop_irred.
  eapply infseq_prod_infseq; eauto.
Qed.

Lemma goeswrong_diverges_exclusive:
  forall C st l s, mach_goes_wrong C st l -> mach_diverges C st s -> False.
Proof.
  unfold mach_terminates, mach_diverges; intros. 
  destruct H as (pc2 & stk2 & st2 & A2 & B2 & C2).
  eapply infseq_finseq_excl with (R := transition_limited C); eauto using machine_deterministic, stop_irred.
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

Lemma goeswrong_OOM_exclusive:
  forall C st l l', mach_goes_wrong C st l -> mach_OOM C st l' -> False.
Proof.
  unfold mach_goes_wrong, mach_OOM; intros.
  destruct H as [pc [stk [st' [H2 [H3 H4]]]]].
  assert ((Some (pc, stk, st') : configuration_limited) = (None : configuration_limited)).
  { eapply finseq_unique; eauto using machine_deterministic, stop_irred.
    unfold irred.  intros b l'' Hn. inversion Hn. }
  congruence.
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

Lemma silent_OOM_exclusive:
  forall C st st' l l', mach_OOM C st l -> mach_silent C st st' l' -> False.
Proof.
  unfold mach_terminates, mach_silent; intros.
  (* destruct H as [pc [H1 H2]]. *)
  destruct H0 as [pc' [stk' [H1' H2']]].
  eapply infseq_silent_finseq_excl.
  eauto using machine_deterministic.
  eauto. eapply H. eauto. 
  intros c l'' Hn; inversion Hn.
Qed.

Lemma reacts_OOM_exclusive:
  forall C st s l,
    mach_reacts C st s -> mach_OOM C st l -> False.
Proof.
  unfold mach_reacts, mach_OOM; intros.
  eapply infseq_finseq_excl with (R := transition_limited C); eauto using machine_deterministic, stop_irred.
  intros c l'' Hn; inversion Hn.
  eapply infseq_prod_infseq.
  eauto.
Qed.
