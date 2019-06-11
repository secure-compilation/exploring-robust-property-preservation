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

Section RobustPreservation.


  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  (*CA: we don't need a particular structure of traces to define preservation
        e.g. traces = values or our defn of traces both make sense
   *)
  Variable trace__S trace__T : Set.

  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.

  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition par__S := par Source.
  Local Definition par__T := par Target.
  Local Definition ctx__S := ctx Source.
  Local Definition ctx__T := ctx Target. 
  Local Definition rsat__S := rsat Source_Semantics.
  Local Definition rsat__T := rsat Target_Semantics.
  
  Local Definition cmp := compile_par Source Target compilation_chain.

  Local Notation "P ↓" := (cmp P) (at level 50).
 (* CA: don't understand why this does not work 

   Local Notation " C [ P ] " := (plug _  P C) (at level 50).
  *)
  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.
  
  Variable σ : prop__T -> prop__S.
  Variable τ : prop__S -> prop__T.

  Definition σRP (P : par__S) (π__T : (trace__T -> Prop)) :=
    rsat__S P (σ π__T) -> rsat__T (P ↓) π__T.

  Definition σRTP := forall P π__T, σRP P π__T.

  Lemma contra_σRP (P : par__S) (π__T : prop__T) :
    (σRP P π__T) <->  ((exists C__T t, sem__T ( plug__T (P↓) C__T) t /\ ~ (π__T t)) ->
                   (exists C__S s, sem__S ( plug__S  P C__S) s /\ ~ (σ π__T) s)).
  Proof.
    rewrite /σRP. by rewrite [_ -> _] contra !neg_rsat.
  Qed.

  Lemma contra_σRTP :
    σRTP <-> (forall P π__T, (exists C__T t, sem__T (plug__T (P ↓) C__T) t /\ ~ (π__T t)) ->
                     (exists C__S s, sem__S (plug__S P C__S) s /\ ~ (σ π__T) s)).
  Proof.
    rewrite /σRTP.
    split => H P π__T; by move/contra_σRP: (H P π__T).
  Qed.

  Definition τRP (P : par__S) (π__S : prop__S) :=
    rsat__S P π__S -> rsat__T (P ↓) (τ π__S).

  Definition τRTP := forall P π__S, τRP P π__S.


  Lemma contra_τRP (P : par__S) (π__S : prop__S) :
    (τRP P π__S) <-> ((exists C__T t, sem__T ( plug__T (P↓) C__T) t /\ ~ (τ π__S) t) ->
                 (exists C__S s, sem__S (plug__S P C__S) s /\ ~ π__S s)).
  Proof.
    rewrite /τRP. by rewrite [_ -> _] contra !neg_rsat.
  Qed.

  Lemma contra_τRTP :
    τRTP <-> (forall P π__S, ((exists C__T t, sem__T ( plug__T (P↓) C__T) t /\ ~ (τ π__S) t) ->
                     (exists C__S s, sem__S (plug__S P C__S) s /\ ~ π__S s))).
  Proof.
    rewrite /τRTP.
    split => H P π__S; by move/contra_τRP: (H P π__S).
  Qed.

  Theorem G_σRTP_iff_τRTP :
    (Galois_fst τ σ) -> (Galois_snd τ σ) -> (σRTP <-> τRTP).
  Proof.
    move => G1 G2. split.
    - move => Hσ P πs Hrsat_src. apply: (Hσ P (τ πs)).
      apply: rsat_upper_closed. exact Hrsat_src. by apply: G1.
    - move => Hτ P πt Hrrsat_tgt.
      have H : rsat__T (P ↓) (τ (σ πt)) by apply: Hτ.
      apply: rsat_upper_closed. exact H. by apply: G2.
  Qed.

  Corollary Adj_σRTP_iff_τRTP :
    Adjunction_law τ σ -> (σRTP <-> τRTP).
  Proof.
    rewrite Galois_equiv. move => [ms [mt [G1 G2]]].
      by apply: G_σRTP_iff_τRTP.
  Qed.

End RobustPreservation.
