From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Require Import ClassicalExtras.
Require Import MyNotation.
Require Import Setoid.
Require Import FunctionalExtensionality.
Require Import Setoid.
Require Import List.
Require Import Stream.

Require Import Galois.
Require Import LanguageModel.
Require Import TraceModel.
Require Import Properties.
Require Import ChainModel.
Require Import NonRobustTraceCriterion. 

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section FC_TC.

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  Variable T_evs S_evs : Events.
  Variable T_end S_end : Endstates.

  Local Definition ev__S := ev S_evs.
  Local Definition ev__T := ev T_evs. 

  Local Definition trace__S := @trace S_evs S_end.
  Local Definition finpref__S := @finpref S_evs S_end.
  Local Definition trace__T := @trace T_evs T_end.
  Local Definition finpref__T := @finpref T_evs T_end.

  (* maybe worth moving this to TraceModel.v *)
  Variable is_input__S : ev__S -> bool. 
  Variable is_input__T : ev__T -> bool.
  
  Variable Source_Semantics : EventTraceSemantics Source S_evs S_end.
  Variable Target_Semantics : EventTraceSemantics Target T_evs T_end.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition psem__S := psem Source_Semantics.   
  Local Definition sem__T := sem Target_Semantics.
  Local Definition psem__T := psem Target_Semantics.
  Local Definition prg__S := prg Source.
  Local Definition prg__T := prg Target.

  Local Definition cmp := compile_whole Source Target compilation_chain.

  Local Notation "P ↓" := (cmp P) (at level 50).

  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.

  Variable rel : ev__S -> ev__T -> Prop.

  Variable inputs_related_only_with_inputs :
    forall e__S e__T, rel e__S e__T -> is_input__S e__S = is_input__T e__T.

  Variable rel_right_total_on_inputs : forall e__T, is_input__T e__T = true -> exists e__S, rel e__S e__T.  

  Lemma rel_right_total_is_input :
    forall e__T, is_input__T e__T = true -> exists e__S, rel e__S e__T /\ is_input__S e__S = true.
  Proof.
    move => et et_input.
    destruct (rel_right_total_on_inputs et_input) as [es rel_es_et].
    exists es. split; auto. rewrite -et_input. by apply: inputs_related_only_with_inputs. 
  Qed.                                          

  (* lists pointwise related, 
     they must have the same length!
   *) 
  Inductive list_lock_rel : list ev__S -> list ev__T -> Prop :=
   | nil_rel  : list_lock_rel nil nil
   | rel_cons : forall e__S e__T l m, list_lock_rel l m -> rel e__S e__T -> list_lock_rel (cons e__S l) (cons e__T m). 
   
  CoInductive stream_rel : @stream ev__S -> @stream ev__T -> Prop :=
    | rel_scons : forall e__S e__T l m, stream_rel l m -> rel e__S e__T -> stream_rel (scons e__S l) (scons e__T m). 

  Definition list_rel (l : list ev__S) (m : list ev__T) : Prop :=
    (exists ll, list_list_prefix ll l /\ list_lock_rel ll m) \/
    (exists mm, list_list_prefix mm m /\ list_lock_rel l mm). 

  (*CA: not sure this is good! 
        we only look at the list/strema of events and require they are related 

        We can relate a source terminating trace with a target silenlty diverging one! 

        Is it the case that we need a relation also on endstates? 
        
  *)
  Definition trace_rel (s : trace__S) (t : trace__T) : Prop :=
    match s, t with
    | tstop l _ , tstop m _ => list_rel l m
    | tstop l _, tsilent m => list_rel l m
    | tstop l _, tstream m => exists mm, list_stream_prefix mm m /\ list_lock_rel l mm
    | tsilent l , tstop m _ => list_rel l m
    | tsilent l , tsilent m => list_rel l m
    | tsilent l, tstream m  => exists mm, list_stream_prefix mm m /\ list_lock_rel l mm
    | tstream l , tstop m _ => exists ll, list_stream_prefix ll l /\ list_lock_rel ll m
    | tstream l, tsilent m => exists ll, list_stream_prefix ll l /\ list_lock_rel ll m
    | tstream l, tstream m => stream_rel l m
    end.  
  
  Local Notation "s ≅ t" := (trace_rel s t) (at level 50).  
  
  Variable src_input_totality : input_totality is_input__S Source_Semantics.
  
  Variable rel_trg_determinacy : forall W t1 t2,
      sem__T (W↓) t1 /\ sem__T (W↓) t2 ->
      (forall s, sem__S W s -> s ≅ t1 -> s ≅ t2) (* relaxing t1 = t2 *) \/
      (exists m1 m2 i1 i2, i1 <> i2 /\
                      (forall l, list_rel l m1 -> list_rel l m2) /\
                      prefix (ftbd (snoc m1 i1)) t1 /\
                      prefix (ftbd (snoc m2 i2)) t2). 

  (* TODO: 
     
     


   *)
  

End FC_TC.