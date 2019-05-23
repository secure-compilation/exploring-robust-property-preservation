Require Import ClassicalExtras.

Require Import TraceModel.
Require Import Properties.
Require Import Galois.

Set Bullet Behavior "Strict Subproofs".

(* This file is intentionaly NOT included in _CoqProject *)


Axiom event : Set.
Axiom is_event : Events event.
Hint Resolve is_event.

Axiom endstate : Set.
Axiom is_endstate : EndState endstate.
Hint Resolve is_endstate.

Definition endstateS : Set := endstate.
Lemma is_endstateS : EndState endstateS.
Proof.
  trivial.
Qed.

Definition out_of_memory := unit.
Definition endstateT : Set := endstate + out_of_memory.
Definition OOM : endstateT := inr tt.
Hint Unfold endstateT OOM.
Lemma is_endstateT : EndState endstateT.
Proof.
  now repeat constructor.
Qed.

Definition traceS := trace event endstateS.
Definition traceT := trace event endstateT.
Definition finprefS := finpref event endstateS.
Definition finprefT := finpref event endstateT.

Definition propS := prop event endstateS.
Definition propT := prop event endstateT.
Definition fpropS := fprop event endstateS.
Definition fpropT := fprop event endstateT.

Inductive syntactic_eq : traceS -> traceT -> Prop :=
| syntactic_eq_tstop : forall l es,
    syntactic_eq (tstop l es) (tstop l (inl es))
| syntactic_eq_tsilent : forall l,
    syntactic_eq (tsilent _ l) (tsilent _ l)
| syntactic_eq_tstream : forall s,
    syntactic_eq (tstream _ s) (tstream _ s)
.
Notation "t__s '≡' t__t" := (syntactic_eq t__s t__t) (no associativity, at level 10).
Hint Constructors syntactic_eq.

Axiom prefixTS : finprefT -> traceS -> Prop.

Definition rel : traceS -> traceT -> Prop :=
  fun t__s t__t => t__s ≡ t__t \/ exists m, (t__t = tstop m OOM /\ prefixTS (ftbd _ m) t__s).
Hint Unfold rel.

Inductive syntactic_eq_finpref : finprefS -> finprefT -> Prop :=
| syntactic_eq_fstop : forall l es,
    syntactic_eq_finpref (fstop l es) (fstop l (inl es))
| syntactic_eq_ftbd : forall l,
    syntactic_eq_finpref (ftbd _ l) (ftbd _ l)
.

Definition rel_finpref : finprefS -> finprefT -> Prop :=
  fun m__s m__t => syntactic_eq_finpref m__s m__t \/ exists l, (m__t = fstop l OOM /\ prefix_finpref (ftbd _ l) m__s).

Definition GC_traceT_traceS : Galois_Connection traceT traceS :=
  induced_connection rel.

Definition τ : propS -> propT := α GC_traceT_traceS.
Definition σ : propT -> propS := γ GC_traceT_traceS.

Lemma τ_preserves_dense : forall (π : propS),
    Dense π -> Dense (τ π).
Proof.
  unfold Dense, τ, GC_traceT_traceS, induced_connection, low_rel; simpl.
  intros π HDense.
  intros t__t Hfin.
  destruct t__t as [l [e | []] | l | s].
  - exists (tstop l e). split.
    apply HDense. econstructor; eexists; eauto.
    left; eauto.
  - exists (tstop l (an_endstate is_endstateS)). split.
    apply HDense. econstructor; eexists; eauto.
    right; eexists; split; eauto.
    admit. (* property of prefixTS *)
  - destruct Hfin as [l' [e' Hn]].
    inversion Hn.
  - destruct Hfin as [l' [e' Hn]].
    inversion Hn.
Admitted.

Lemma σ_preserves_dense : forall (π : propT),
    Dense π -> Dense (σ π).
Proof.
  unfold Dense, σ, GC_traceT_traceS, induced_connection, up_rel; simpl.
  intros π HDense.
  intros t__s Hfin t__t Hrel.
  destruct Hrel as [Hrel | Hrel].
  - apply HDense; inversion Hrel; subst.
    + now repeat eexists.
    + destruct Hfin as [l' [e' Hn]].
      inversion Hn.
    + destruct Hfin as [l' [e' Hn]].
      inversion Hn.
  - destruct Hrel as [m [Heq Hpref]].
    apply HDense.
    rewrite Heq.
    now repeat eexists.
Qed.


(* The goal is now to prove that τ and/or σ preserve Safety. 
   I need to define σ and τ for fprop, in order to use them
   to transform the set of bad prefixes *)

Definition traceT_to_traceS_safety (t__t : traceT) : traceS :=
  match t__t with
  | tstop l (inl e) => tstop l e
  | tstop l (inr _) => tstop l (an_endstate is_endstateS)
  | tsilent l => tsilent _ l
  | tstream s => tstream _ s
  end.
Hint Unfold traceT_to_traceS_safety.

Lemma traceT_to_traceS_safety_rel : forall (t__t : traceT),
    rel (traceT_to_traceS_safety t__t) t__t.
Proof.
  intros t__t.
  destruct t__t as [l [e | []] | l | s]; try now repeat constructor.
  - right.
    exists l. split. reflexivity.
    admit. (* trivial property of prefixTS *)
Admitted.

Definition finprefT_to_finprefS (m__t : finprefT) : finprefS :=
  match m__t with
  | fstop l (inl e) => fstop l e
  | fstop l (inr _) => ftbd _ l
  | ftbd l => ftbd _ l
  end.

(* Lemma prefix_T_to_S_safety : forall (m__t : finprefT) (t__t : traceT), *)
(*    prefix (finprefT_to_finprefT_safety m__t) (traceT_to_traceS_safety t__t) -> *)
(*    prefix m__t t__t. *)
(* Proof. *)
(*   intros m__t t__t Hpref. *)
(*   destruct m__t as [l [e | []] | l]; *)
(*     destruct t__t as [l' [e' | []] | l' | s']; *)
(*     try now auto. *)
(*   - destruct Hpref; split; now subst. *)
(*   - simpl in Hpref. *)

Definition traceS_to_traceT (t__s : traceS) : traceT :=
  match t__s with
  | tstop l e => tstop l (inl e)
  | tsilent l => tsilent _ l
  | tstream s => tstream _ s
  end.
Hint Unfold traceS_to_traceT.

Lemma traceS_to_traceT_rel : forall (t__s : traceS),
    rel t__s (traceS_to_traceT t__s).
Proof.
  intros t__s.
  destruct t__s; now repeat constructor.
Qed.

Definition finprefS_to_finprefT (m__s : finprefS) : finprefT :=
  match m__s with
  | fstop l e => fstop l (inl e)
  | ftbd l => ftbd _ l
  end.
