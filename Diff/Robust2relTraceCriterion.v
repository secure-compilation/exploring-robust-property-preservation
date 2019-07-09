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
Require Import Robust2relTraceProperty.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section Robust2relCrit.

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

  Variable rel : trace__S -> trace__T -> Prop.

  Local Definition σ : (trace__T * trace__T -> Prop) -> (trace__S * trace__S -> Prop) :=
                       γ (@induced_connection_prod (trace__T) (trace__S) rel).

  Local Definition τ : (trace__S * trace__S -> Prop) -> (trace__T * trace__T -> Prop) :=
                       α (@induced_connection_prod (trace__T) (trace__S) rel).


  Local Definition σR2rTP := σR2rTP compilation_chain
                                    Source_Semantics Target_Semantics
                                    σ.

  Local Definition τR2rTP := τR2rTP compilation_chain
                                    Source_Semantics Target_Semantics
                                    τ.


  Local Definition induced_adj : Adjunction_law τ σ :=
    adjunction_law (induced_connection_prod rel).

  Definition rel_R2rTC : Prop :=
    forall C__T P1 P2 t1 t2, sem__T (plug__T (P1 ↓) C__T) t1 ->
                       sem__T (plug__T (P2 ↓) C__T) t2 ->
                       exists C__S s1 s2, rel s1 t1 /\
                                    rel s2 t2 /\
                                    sem__S (plug__S P1 C__S) s1 /\
                                    sem__S (plug__S P2 C__S) s2.

  Theorem rel_R2rTC_τR2rTP : rel_R2rTC <-> τR2rTP.
  Proof.
    setoid_rewrite contra_τR2rTP. split.
    + move => Hrel P1 P2 S [C__T [t1 [t2 [Hsem1 [Hsem2 τS_t1_t2]]]]].
      destruct (Hrel C__T P1 P2 t1 t2 Hsem1 Hsem2) as
          [C__S [s1 [s2 [rel1 [rel2 [Hsem1' Hsem2' ]]]]]].
      exists C__S, s1, s2. repeat (split; auto).
      move => HS_s1_s2.
      apply: τS_t1_t2. exists (s1, s2). repeat (split; auto).
    + move => Hτ C__T P1 P2 t1 t2 Hsem1 Hsem2.
      specialize (Hτ P1 P2 (fun s => ~ rel (fst s) t1 \/ ~ rel (snd s) t2)).
      destruct Hτ as [C__S [s1 [s2 [Hsem1' [Hsem2' notS_s1_s2]]]]].
      ++ exists C__T, t1, t2. repeat (split; auto).
         move => [[s1 s2] [Hs1_s2 [H1 H2]]].
         destruct Hs1_s2; contradiction.
      move/de_morgan1: notS_s1_s2. rewrite -dne. move => [rel1 rel2].
      exists C__S, s1, s2. repeat (split; auto).
  Qed.

  Theorem rel_R2rTC_σR2rTP : rel_R2rTC <-> σR2rTP.
  Proof.
    setoid_rewrite (Adj_σR2rTP_iff_τR2rTP _ _ _ induced_adj).
    by rewrite rel_R2rTC_τR2rTP.
  Qed.

End Robust2relCrit.