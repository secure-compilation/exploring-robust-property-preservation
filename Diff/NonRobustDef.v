From mathcomp Require Import all_ssreflect. 

Set Implicit Arguments.
Unset Strict Implicit.
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

Module Preservation (TSource TTarget : Trace)
                         (Source Target : Language)
                         (Compiler : CompilationChain Source Target).
  
  Definition trace__S := TSource.trace.
  Definition trace__T := TTarget.trace.

  Module SProp := Properties TSource.
  Module TProp := Properties TTarget. 
  
  Definition prop__S := SProp.prop.
  Definition prop__T := TProp.prop.

  Definition prg__S := Source.prg.
  Definition prg__T := Target.prg.

  Module Sat__S := Sat TSource Source.  
  Module Sat__T := Sat TTarget Target.

  Definition sat__S := Sat__S.sat.
  Definition sat__T := Sat__T.sat.

  Definition cmp := Compiler.compile_whole.

  Notation "W ↓" := (cmp W) (at level 50). 
  
  (* parameters *)
  
  Parameter σ : prop__T -> prop__S.
  Parameter τ : prop__S -> prop__T.

  (* definitions *)

  Definition σP (W : prg__S) (π__T : prop__T) :=
    sat__S W (σ π__T) -> sat__T (W ↓) π__T.

  Definition σTP := forall W π__T, σP W π__T. 
  
  Definition τP (W : prg__S) (π__S : prop__S) :=
    sat__S W π__S -> sat__T (W ↓) (τ π__S).

  Definition τTP := forall W π__S, τP W π__S.

  Theorem G_σTP_iff_τTP :
    (Galois_fst τ σ) -> (Galois_snd τ σ) -> (σTP <-> τTP).
  Proof.
     move => G1 G2. split. 
     - move => Hσ P πs Hsat_src. apply: (Hσ P (τ πs)).
       apply: Sat__S.sat_upper_closed. exact Hsat_src. by apply: G1. 
     - move => Hτ P πt Hrsat_tgt.
       have H : sat__T (P ↓) (τ (σ πt)) by apply: Hτ. 
       apply: Sat__T.sat_upper_closed. exact H. by apply: G2.
  Qed.     

  Corollary Adj_σTP_iff_τTP :
    Adjunction_law τ σ -> (σTP <-> τTP).
  Proof.
    rewrite Galois_equiv. move => [ms [mt [G1 G2]]].
      by apply: G_σTP_iff_τTP. 
  Qed. 
      
End Preservation.                                      



