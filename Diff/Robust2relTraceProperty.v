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

  Definition σR2P (P1 P2 : par__S) (T : trace__T * trace__T -> Prop) :=
    rsat__S P1 P2 (σ T) -> rsat__T (P1 ↓) (P2 ↓) T.   

  Definition σR2TP := forall P1 P2 T, σR2P P1 P2 T.

  (* Lemma contra_σRP (P : par__S) (π__T : prop__T) : *)
  (*   (σRP P π__T) <->  ((exists C__T t, sem__T ( plug__T (P↓) C__T) t /\ ~ (π__T t)) -> *)
  (*                  (exists C__S s, sem__S ( plug__S  P C__S) s /\ ~ (σ π__T) s)). *)
  (* Proof. *)
  (*   rewrite /σRP. by rewrite [_ -> _] contra !neg_rsat. *)
  (* Qed. *)

  (* Lemma contra_σRTP : *)
  (*   σRTP <-> (forall P π__T, (exists C__T t, sem__T (plug__T (P ↓) C__T) t /\ ~ (π__T t)) -> *)
  (*                    (exists C__S s, sem__S (plug__S P C__S) s /\ ~ (σ π__T) s)). *)
  (* Proof. *)
  (*   rewrite /σRTP. *)
  (*   split => H P π__T; by move/contra_σRP: (H P π__T). *)
  (* Qed. *)

  Definition τR2P (P1 P2 : par__S) (S : trace__S * trace__S -> Prop) :=
    rsat__S P1 P2 S -> rsat__T (P1 ↓) (P2 ↓) (τ S).

  Definition τR2TP := forall P1 P2 S, τR2P P1 P2 S.

  (* Lemma contra_τRP (P : par__S) (π__S : prop__S) : *)
  (*   (τRP P π__S) <-> ((exists C__T t, sem__T ( plug__T (P↓) C__T) t /\ ~ (τ π__S) t) -> *)
  (*                (exists C__S s, sem__S (plug__S P C__S) s /\ ~ π__S s)). *)
  (* Proof. *)
  (*   rewrite /τRP. by rewrite [_ -> _] contra !neg_rsat. *)
  (* Qed. *)

  (* Lemma contra_τRTP : *)
  (*   τRTP <-> (forall P π__S, ((exists C__T t, sem__T ( plug__T (P↓) C__T) t /\ ~ (τ π__S) t) -> *)
  (*                    (exists C__S s, sem__S (plug__S P C__S) s /\ ~ π__S s))). *)
  (* Proof. *)
  (*   rewrite /τRTP. *)
  (*   split => H P π__S; by move/contra_τRP: (H P π__S). *)
  (* Qed. *)

  Theorem G_σRTP_iff_τRTP :
    (Galois_fst τ σ) -> (Galois_snd τ σ) -> (σR2TP <-> τR2TP).
  Proof.
    move => G1 G2. split.
    - move => Hσ P1 P2 S Hrsat_src. apply: (Hσ P1 P2 (τ S)).
      apply: rsat2_upper_closed. exact Hrsat_src. by apply: G1.
    - move => Hτ P1 P2 T Hrrsat_tgt.
      have H : rsat__T (P1 ↓) (P2 ↓) (τ (σ T)) by apply: Hτ.
      apply: rsat2_upper_closed. exact H. by apply: G2.
  Qed.

  Corollary Adj_σRTP_iff_τRTP :
    Adjunction_law τ σ -> (σR2TP <-> τR2TP).
  Proof.
    rewrite Galois_equiv. move => [ms [mt [G1 G2]]].
      by apply: G_σRTP_iff_τRTP.
  Qed.

End Robust2relPreservation.
