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
  Variable trace__S trace__T : Set.

  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.
  Local Definition hprop__S := hprop trace__S.
  Local Definition hprop__T := hprop trace__T.

  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition beh__S := beh Source_Semantics.
  Local Definition beh__T := beh Target_Semantics.
  Local Definition prg__S := prg Source.
  Local Definition prg__T := prg Target.
  Local Definition sat__S := sat Source_Semantics.
  Local Definition sat__T := sat Target_Semantics.
  Local Definition hsat__S := hsat Source_Semantics.
  Local Definition hsat__T := hsat Target_Semantics.

  Local Definition cmp := compile_whole Source Target compilation_chain.

  Local Notation "W ↓" := (cmp W) (at level 50).

  Variable σ : prop__T -> prop__S.
  Variable τ : prop__S -> prop__T.

  Local Definition σ__h : hprop__T -> hprop__S := lift σ.
  Local Definition τ__h : hprop__S -> hprop__T := lift τ.

  Definition σhP (W : prg__S) (h__T : hprop__T) :=
    hsat__S W (σ__h h__T) -> hsat__T (W ↓) h__T.


  Definition σHP := forall W h__T, σhP W h__T.

  Lemma contra_σhP (W : prg__S) (h__T : hprop__T) :
    (σhP W h__T) <->  (~  h__T (beh__T (W ↓))  ->
                  (~  (σ__h h__T) (beh__S W))).
  Proof.
    rewrite /σhP. by rewrite contra.
  Qed.

  Lemma contra_σHP :
    σHP <-> (forall W h__T,  (~  h__T (beh__T (W ↓))  ->
                  (~  (σ__h h__T) (beh__S W)))) .
  Proof.
    rewrite /σHP.
    split => H W h__T; by move/contra_σhP: (H W h__T).
  Qed.

  Definition τhP (W : prg__S) (h__S : hprop__S) :=
    hsat__S W h__S -> hsat__T (W ↓) (τ__h h__S).

  Definition τHP := forall W h__S, τhP W h__S.


  Lemma contra_τhP (W : prg__S) (h__S : hprop__S) :
    (τhP W h__S) <->  ((~  (τ__h h__S) (beh__T (W ↓)))  ->
                  (~   h__S (beh__S W))).
  Proof.
    rewrite /τhP. by rewrite contra.
  Qed.

  Lemma contra_τHP :
    τHP <-> (forall W h__S,  ((~  (τ__h h__S) (beh__T (W ↓)))  ->
                     (~   h__S (beh__S W)))).
  Proof.
    rewrite /τHP.
    split => H W h__S; by move/contra_τhP: (H W h__S).
  Qed.

  Theorem Insertion_τHP_σHP :
    (Insertion_snd τ σ) -> (τHP -> σHP).
  Proof.
    move => H_in Hτ W h__t H_src.
    move: (Hτ W (σ__h h__t) H_src) => [b__s [[bt [H_bt Heq]] H_trg]].
    subst.
    have Hfoo : τ (σ bt) = bt by apply: H_in.
    by rewrite /hsat__T /hsat H_trg Hfoo.
  Qed.

End Preservation.