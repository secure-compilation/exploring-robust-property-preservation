(*" given a compiler ↓: Source → Target, (and a semantics for the two languages)

    is there a relation ~ ⊆ Trace_S × Trace_T

    such that ↓ is TC̃ and ~ is minimal with this property? "

 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Require Import ClassicalExtras.
Require Import MyNotation.
Require Import Setoid.
Require Import FunctionalExtensionality.
Require Import Setoid.

Require Import Galois.
Require Import LanguageModel.
Require Import TraceModel.
Require Import Properties.
Require Import ChainModel.
Require Import NonRobustDef.
Require Import NonRobustTraceCriterion.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section Relation.

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  Variable trace__S trace__T : Set.

  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.

  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition beh__S := beh Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition beh__T := beh Target_Semantics.
  Local Definition prg__S := prg Source.
  Local Definition prg__T := prg Target.
  Local Definition sat__S := sat Source_Semantics.
  Local Definition sat__T := sat Target_Semantics.

  Local Definition cmp := compile_whole Source Target compilation_chain.

  Local Notation "W ↓" := (cmp W) (at level 50).

  (* CA's intuition:
          frist approximate a trace property π_s with a family
          of program behaviours "W_i s.t. beh W_i ⊆ π_s"
          then take (in the target) the union of the behaviours of W_i ↓

     + φ is not necessarely continous, so that it may not have an upper adjoint!!
       it also follows that τ' below is different from φ

   *)
  Definition φ : prop__S -> prop__T :=
    fun π__S =>
      (fun t__T : trace__T => exists W : prg__S, sem__T (W ↓) t__T /\
                                         (forall t__S, sem__S W t__S -> π__S t__S)).

  Definition rel : trace__S -> trace__T -> Prop :=
    fun t__S t__T => exists W, sem__S W t__S /\ (φ (beh__S W)) t__T.

  Local Definition adjunction := induced_connection rel.

  Local Definition τ' : prop__S -> prop__T := α adjunction.
  Local Definition σ' : prop__T -> prop__S := γ adjunction.

  Local Definition τTP := τTP compilation_chain
                              Source_Semantics Target_Semantics
                              τ'.


  Local Definition σTP := σTP compilation_chain
                              Source_Semantics Target_Semantics
                              σ'.


  Lemma φ_leq_τ' : forall π__S, (φ π__S) ⊆ (τ' π__S).
  Proof.
    rewrite /τ' /α //= /low_rel => π__S t__T [W [Wcmp_t W_sub_π]].
    destruct (non_empty_sem Source_Semantics W) as [t__S W_t__S].
    exists t__S. split.
    + by apply W_sub_π.
    + rewrite /rel /φ. exists W. split; auto.
      now exists W.
  Qed.


  Local Definition rel_TC := rel_TC compilation_chain
                                    Source_Semantics Target_Semantics
                                    rel.

  Lemma rel_TC' : rel_TC <-> (forall W, beh__T (W ↓) ⊆ (τ' (beh__S W))).
  Proof.
    rewrite /τ' /α //= /low_rel;
    split => H W t__T Wcmp_t; specialize (H W t__T Wcmp_t); firstorder.
  Qed.

  Lemma Wcmp_φW (W : prg__S) : beh__T (W ↓) ⊆ (φ (beh__S W)).
  Proof.
    rewrite /φ => t__T Wcmp_t. now exists W.
  Qed.

  Theorem cmp_is_rel_TC : rel_TC.
  Proof.
    rewrite rel_TC' => W.
    apply: subset_trans.
    exact (Wcmp_φW W). apply: φ_leq_τ'.
  Qed.

  Corollary cmp_is_τTP: τTP.
  Proof. setoid_rewrite <- rel_TC_τTP. exact cmp_is_rel_TC. Qed.

  Corollary cmp_is_σTP : σTP.
  Proof. setoid_rewrite <- rel_TC_σTP. exact cmp_is_rel_TC. Qed.

  (*CA's TODO: is rel minimal with this property? *)

End Relation.