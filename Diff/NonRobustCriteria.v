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
Require Import NonRobustDef.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Module Type Criteria  (TSource TTarget : Trace)
                      (R : RelTrace TSource TTarget)
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

  Definition sem__S := Sat__S.sem.
  Definition sem__T := Sat__T.sem.                       
  
  Definition cmp := Compiler.compile_whole.

  Notation "W ↓" := (cmp W) (at level 50).

  Definition rel := R.rel. 
  
  Definition σ' : prop__T -> prop__S := R.σ'.
  Definition τ' : prop__S -> prop__T := R.τ'.

  
  
  Module PropertyFull := (Preservation  TSource TTarget
                                        Source Target
                                        Compiler).

   
  Definition rel_TC := forall W t, sem__T (W ↓) t -> exists s, sem__S W s.  

  (* CA's TODO: + force parameters σ and τ in Propertyfull to be 
                   σ' and τ' above.
                + Show rel_TC <-> σTP <-> τTP.  
  *)

  
End Criteria. 