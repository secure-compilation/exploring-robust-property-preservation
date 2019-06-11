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
Require Import RobustTraceProperty.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section RobustTPCriterion.

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

  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.
  
  Variable rel : trace__S -> trace__T -> Prop.

  Local Definition adjunction :=  induced_connection rel.

  Local Definition τ' : prop__S -> prop__T := α adjunction.
  Local Definition σ' : prop__T -> prop__S := γ adjunction.

  Local Definition rel_adjunction_law : Adjunction_law τ' σ' := adjunction_law adjunction.

  Definition rel_RTC := forall P C__T t, sem__T (plug__T (P ↓) C__T) t -> exists C__S s, rel s t /\ sem__S (plug__S P C__S) s.

  
  Local Definition τRTP := τRTP compilation_chain
                                Source_Semantics Target_Semantics
                                τ'.


  Local Definition σRTP := σRTP compilation_chain
                                Source_Semantics Target_Semantics
                                σ'.


  Lemma σRTP_τRTP : σRTP <-> τRTP.
  Proof. apply: Adj_σRTP_iff_τRTP. by apply: rel_adjunction_law. Qed.


  Theorem rel_RTC_τRTP : rel_RTC <-> τRTP.
  Proof.
    setoid_rewrite contra_τRTP. split.
    - move => Htilde P π [C__T [t [Hsemt Hτ]]].
      destruct (Htilde P C__T t Hsemt) as [C__S [s [Hrel_s_t Hsems]]].
      exists C__S, s. split; auto. move => s_in_π. apply: Hτ. by exists s.
    - move => Hτ P C__T t Hsemt. specialize (Hτ P (fun s => ~ rel s t)).
      case: Hτ.
      { exists C__T, t. split; auto. unfold τ'. move => [s [Hc Hcc]] //=. }
      move => C__S [s [Hsems H]]. exists C__S, s. split; auto; by apply: NNPP.
  Qed.

  Theorem rel_RTC_σRTP : rel_RTC <-> σRTP.
  Proof. by rewrite σRTP_τRTP rel_RTC_τRTP. Qed.


End RobustTPCriterion.

