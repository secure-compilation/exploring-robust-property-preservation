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

Section Robust2relPreservation.

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
  Local Definition rsat__S := rsat2 Source_Semantics.
  Local Definition rsat__T := rsat2 Target_Semantics.
  
  Local Definition cmp := compile_par Source Target compilation_chain.

  Local Notation "P ↓" := (cmp P) (at level 50).
 (* CA: don't understand why this does not work 

   Local Notation " C [ P ] " := (plug _  P C) (at level 50).
  *)
  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.
  
  Variable σ : (trace__T * trace__T -> Prop) -> (trace__S * trace__S -> Prop).
  Variable τ : (trace__S * trace__S -> Prop) -> (trace__T * trace__T -> Prop).

  Definition σR2rP (P1 P2 : par__S) (T : trace__T * trace__T -> Prop) :=
    rsat__S P1 P2 (σ T) -> rsat__T (P1 ↓) (P2 ↓) T.   

  Definition σR2rTP := forall P1 P2 T, σR2rP P1 P2 T.

  Lemma contra_σR2rP (P1 P2 : par__S) (T : trace__T * trace__T -> Prop) :
    (σR2rP P1 P2 T) <->  ((exists C__T t1 t2, sem__T ( plug__T (P1 ↓) C__T) t1 /\
                                      sem__T ( plug__T (P2 ↓) C__T) t2 /\  ~ (T (t1,t2))) ->
                        (exists C__S s1 s2, sem__S (plug__S P1 C__S) s1 /\
                                      sem__S (plug__S P2 C__S) s2 /\  
                                    ~ (σ T) (s1, s2))).
  Proof.
    rewrite /σR2rP. by rewrite [_ -> _] contra !neg_rsat2.
  Qed.

  Lemma contra_σR2rTP :
    σR2rTP <-> (forall P1 P2 T, (exists C__T t1 t2, sem__T (plug__T (P1 ↓) C__T) t1 /\
                                       sem__T (plug__T (P2 ↓) C__T) t2 /\
                                     ~ (T (t1, t2))) ->
                        (exists C__S s1 s2, sem__S (plug__S P1 C__S) s1 /\
                                      sem__S (plug__S P2 C__S) s2 /\
                                     ~ (σ T) (s1, s2))).
  Proof.
    rewrite /σR2rTP.
    split => H P1 P2 T; by move/contra_σR2rP: (H P1 P2 T).
  Qed.

  Definition τR2rP (P1 P2 : par__S) (S : trace__S * trace__S -> Prop) :=
    rsat__S P1 P2 S -> rsat__T (P1 ↓) (P2 ↓) (τ S).

  Definition τR2rTP := forall P1 P2 S, τR2rP P1 P2 S.

  Lemma contra_τR2rP (P1 P2 : par__S) (S : trace__S * trace__S -> Prop) :
    (τR2rP P1 P2 S) <-> ((exists C__T t1 t2, sem__T (plug__T (P1 ↓) C__T) t1 /\
                                    sem__T (plug__T (P2 ↓) C__T) t2 /\
                                   ~ (τ S) (t1, t2)) ->
                      (exists C__S s1 s2, sem__S (plug__S P1 C__S) s1 /\
                                    sem__S (plug__S P2 C__S) s2 /\
                                   ~ S (s1, s2))).
  Proof.
    rewrite /τR2rP. by rewrite [_ -> _] contra !neg_rsat2.
  Qed.

  Lemma contra_τR2rTP :
    τR2rTP <-> (forall P1 P2 S, ((exists C__T t1 t2, sem__T ( plug__T (P1 ↓) C__T) t1 /\
                                         sem__T ( plug__T (P2 ↓) C__T) t2 /\
                                       ~ (τ S) (t1, t2)) ->
                          (exists C__S s1 s2, sem__S (plug__S P1 C__S) s1 /\
                                        sem__S (plug__S P2 C__S) s2 /\
                                       ~ S (s1, s2)))).
  Proof.
    rewrite /τR2rTP.
    split => H P1 P2 S; by move/contra_τR2rP: (H P1 P2 S).
  Qed.

  Theorem G_σR2rTP_iff_τR2rTP :
    (Galois_fst τ σ) -> (Galois_snd τ σ) -> (σR2rTP <-> τR2rTP).
  Proof.
    move => G1 G2. split.
    - move => Hσ P1 P2 S Hrsat_src. apply: (Hσ P1 P2 (τ S)).
      apply: rsat2_upper_closed. exact Hrsat_src. by apply: G1.
    - move => Hτ P1 P2 T Hrrsat_tgt.
      have H : rsat__T (P1 ↓) (P2 ↓) (τ (σ T)) by apply: Hτ.
      apply: rsat2_upper_closed. exact H. by apply: G2.
  Qed.

  Corollary Adj_σR2rTP_iff_τR2rTP :
    Adjunction_law τ σ -> (σR2rTP <-> τR2rTP).
  Proof.
    rewrite Galois_equiv. move => [ms [mt [G1 G2]]].
      by apply: G_σR2rTP_iff_τR2rTP.
  Qed.

End Robust2relPreservation.
