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
Require Import RobustTraceProperty.

(* Every time we can express a Class Ξ via an upper closed operator ξ
   we have that γRΞP is equivalent to (ξ ∘ τ)RTP.

   for instance we can express the class of Safety and Dense properties using
   the uco Cl.

*)

Section Closure_Operators_RobustPreservation.

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

  Definition σRP := σRP compilation_chain
                        Source_Semantics Target_Semantics
                        σ.

  Variable ϕ_op : (@Uco trace__T).

  Local Definition ϕ := uco ϕ_op.

  (* ϕ ∘ τ *)
  Local Definition ϕ_τRP := τRP compilation_chain
                                Source_Semantics Target_Semantics
                                (ϕ ∘ τ).

  Local Definition ϕ_τRTP := forall P π__S, ϕ_τRP P π__S.

  Lemma uco_adjuncts' :
    Adjunction_law τ σ ->
    ( (forall P (π__T : prop__T),  σRP P (ϕ π__T)) <->
      ϕ_τRTP ).
  Proof.
    rewrite Galois_equiv. move => [mono_σ [mono_τ [G1 G2]]].
    split => H_p P π sat_src.
    + have H: rsat__S P (σ (ϕ (τ π))).
      { apply: rsat_upper_closed. exact: sat_src.
        apply: subset_trans. by apply: G1.
        apply: mono_τ. exact: (ext ϕ_op). }
      move: (H_p P (ϕ (τ π))). firstorder.
    + have H: rsat__T (P ↓) (ϕ π).
      { move: (H_p P _ sat_src) => H.
        apply: rsat_upper_closed. exact: H.
        have Hfoo : ϕ π = ϕ (ϕ π) by rewrite /ϕ (idmp ϕ_op).
        move => t Hfoo_t. rewrite Hfoo.
        move: t Hfoo_t.
        apply: mono. by apply: G2. }
      exact: H.
  Qed.

  Lemma uco_aux  :
    (forall P (π__T : prop__T),  σRP P (ϕ π__T)) <->
    (forall P (π__T : prop__T),  ((lift ϕ) (@h_true trace__T)) π__T -> σRP P π__T).
  Proof.
    split => H_p P π.
    + move => [b [hb Cb]] sat_src. subst.
        by move: (H_p P b sat_src).
    + move => sat_src.
      have H: (lift ϕ (@h_true trace__T)) (ϕ π) by now exists π.
       by move: (H_p P (ϕ π) H sat_src).
  Qed.

 Theorem uco_adjuncts :
  Adjunction_law τ σ ->
  ( (forall P (π__T : prop__T),  ((lift ϕ) (@h_true trace__T) π__T) -> σRP P π__T) <->
     ϕ_τRTP ).
 Proof.
  move => H_adj. rewrite -uco_adjuncts'.
    by rewrite -uco_aux. assumption.
Qed.

End Closure_Operators_RobustPreservation.
