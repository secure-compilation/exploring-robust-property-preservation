From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Require Import ClassicalExtras.
Require Import MyNotation.
Require Import Setoid.
Require Import FunctionalExtensionality.

Require Import Galois.
Require Import LanguageModel.
Require Import TraceModel.
Require Import Properties.
Require Import ChainModel.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Notation "W ↓" := (compile_whole _ _ _ W) (at level 50).


Section Preservation.


  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  (*CA: we don't need a particular structure of traces to define preservation
        e.g. traces = values or our defn of traces both make sense
   *)
  Variable trace__S trace__T : Type.

  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.

  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition prg__S := prg Source.
  Local Definition prg__T := prg Target.
  Local Definition sat__S := sat Source_Semantics.
  Local Definition sat__T := sat Target_Semantics.

  Local Definition cmp := compile_whole Source Target compilation_chain.

  Local Notation "W ↓" := (cmp W) (at level 50).

  Variable σ : prop__T -> prop__S.
  Variable τ : prop__S -> prop__T.

  Definition σP (W : prg__S) (π__T : (trace__T -> Prop)) :=
    sat__S W (σ π__T) -> sat__T (W ↓) π__T.

  Definition σTP := forall W π__T, σP W π__T.

  Lemma contra_σP (W : prg__S) (π__T : prop__T) :
    (σP W π__T) <->  ((exists t, sem__T (W ↓) t /\ ~ (π__T t)) ->
                  (exists s, sem__S W s /\ ~ (σ π__T) s)).
  Proof.
    rewrite /σP. by rewrite [_ -> _] contra !neg_sat.
  Qed.

  Lemma contra_σTP :
    σTP <-> (forall W π__T, (exists t, sem__T (W ↓) t /\ ~ (π__T t)) ->
                   (exists s, sem__S W s /\ ~ (σ π__T) s)).
  Proof.
    rewrite /σTP.
    split => H W π__T; by move/contra_σP: (H W π__T).
  Qed.

  Definition τP (W : prg__S) (π__S : prop__S) :=
    sat__S W π__S -> sat__T (W ↓) (τ π__S).

  Definition τTP := forall W π__S, τP W π__S.


  Lemma contra_τP (W : prg__S) (π__S : prop__S) :
    (τP W π__S) <-> ((exists t, sem__T (W ↓) t /\ ~ (τ π__S) t) ->
                 (exists s, sem__S W s /\ ~ π__S s)).
  Proof.
    rewrite /τP. by rewrite [_ -> _] contra !neg_sat.
  Qed.

  Lemma contra_τTP :
    τTP <-> (forall W π__S, (exists t, sem__T (W ↓) t /\ ~ (τ π__S) t) ->
                   (exists s, sem__S W s /\ ~ π__S s)).
  Proof.
    rewrite /τTP.
    split => H W π__S; by move/contra_τP: (H W π__S).
  Qed.

  Theorem G_σTP_iff_τTP :
    (Galois_fst τ σ) -> (Galois_snd τ σ) -> (σTP <-> τTP).
  Proof.
    move => G1 G2. split.
    - move => Hσ P πs Hsat_src. apply: (Hσ P (τ πs)).
      apply: sat_upper_closed. exact Hsat_src. by apply: G1.
    - move => Hτ P πt Hrsat_tgt.
      have H : sat__T (P ↓) (τ (σ πt)) by apply: Hτ.
      apply: sat_upper_closed. exact H. by apply: G2.
  Qed.

  Corollary Adj_σTP_iff_τTP :
    Adjunction_law τ σ -> (σTP <-> τTP).
  Proof.
    rewrite Galois_equiv. move => [ms [mt [G1 G2]]].
      by apply: G_σTP_iff_τTP.
  Qed.

End Preservation.
