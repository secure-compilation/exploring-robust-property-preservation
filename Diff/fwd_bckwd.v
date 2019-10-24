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
  Variable is_input__S :  ev__S -> bool. 
  Variable is_input__T :  ev__T -> bool.
  
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

  (* CA:

     we could assume a relation over lists of events to realte
     a single source events to a sequence of target events
  
     example: 

      Input__S := Nat 
      Input__T := List ({0,1}) 

      with the relation defined to be the binary representation of a natural number

      3 ~ [1,1] 

     However this way we lose the following porperty 

         [e1] ++ [e2]  ~ [e1'] ++ [e2'] => e1 ~ e1' ∧ e2 ~ e2' 

     that was foundamental in the sketch proof (see board/FCtilde_TCtilde_logical.jpg)  

  *)
 
  
  Variable rel : ev__S -> ev__T -> Prop.

  Inductive list_rel : list ev__S -> list ev__T -> Prop := 
  | nil_rel : list_rel nil nil
  | snoc_rel : forall l1 m1 e__S e__T, rel e__S e__T -> list_rel l1 m1 -> list_rel (snoc l1 e__S) (snoc m1 e__T).

    
  Variable inputs_related_only_with_inputs :
    forall l m, rel l m -> is_input__S l = is_input__T m.

  Variable rel_right_total_on_inputs : forall m, is_input__T m = true -> exists l, rel l m.  

  Lemma rel_right_total_is_input :
    forall e__T, is_input__T e__T = true -> exists e__S, rel e__S e__T /\ is_input__S e__S = true.
  Proof.
    move => et et_input.
    destruct (rel_right_total_on_inputs et_input) as [es rel_es_et].
    exists es. split; auto. rewrite -et_input. by apply: inputs_related_only_with_inputs. 
  Qed.                                          

  CoInductive stream_rel : @stream ev__S -> @stream ev__T -> Prop :=
    | scon_rel : forall s1 t1 e__S e__T, rel e__S e__T -> stream_rel s1 t1 -> stream_rel (scons e__S s1) (scons e__T t1).

  (*CA: How to define this? *)
  Definition trace_rel (s : trace__S) (t : trace__T) : Prop :=
    match s, t with
    | tstop l _ , tstop m _ => list_rel l m (* /\ endstates related? *)
    | tstop l _, tsilent m => list_rel l m (* sure? or shall we add a condition on the endstate? *)
    | tstop l _, tstream m => exists mm, list_stream_prefix mm m /\ list_rel l mm (* sure? or shall we add a condition on the endstate? *)
    | tsilent l , tstop m _ => list_rel l m (* sure? or shall we add a condition on the endstate? *)
    | tsilent l , tsilent m => list_rel l m
    | tsilent l, tstream m  => exists mm, list_stream_prefix mm m /\ list_rel l mm (* sure??? *)
    | tstream l , tstop m _ => exists ll, list_stream_prefix ll l /\ list_rel ll m (* sure? or shall we add a condition on the endstate? *)
    | tstream l, tsilent m => exists ll, list_stream_prefix ll l /\ list_rel ll m (* sure??? *)
    | tstream l, tstream m => stream_rel l m
    end.  

  Local Notation "s ≅ t" := (trace_rel s t) (at level 50).
  
  Variable src_input_totality : input_totality is_input__S Source_Semantics.
  
  Variable rel_trg_determinacy : forall W t1 t2,
      sem__T (W↓) t1 -> sem__T (W↓) t2 ->
      ((forall s, sem__S W s -> s ≅ t1 -> s ≅ t2) (* relaxing t1 = t2 *) \/
      (exists m1 m2 i1 i2, i1 <> i2 /\
                      (forall l, list_rel l m1 -> list_rel l m2) /\
                      prefix (ftbd (snoc m1 i1)) t1 /\
                      prefix (ftbd (snoc m2 i2)) t2)).

  (*CA: it is similar to the determinacy condition
        (see non relational version) but for traces 
        belonging to different sets 
  *)
  Definition vertical_match (s : trace__S) (t : trace__T) : Prop :=
    s ≅ t \/
    (exists l m y i, prefix (ftbd (snoc l y)) s /\
                 prefix (ftbd (snoc m i)) t /\
                 ~ rel y i ).

  (* CA: this seems needed to me, however it also seems to conflict
         with the defintion of ≅ (between traces) starting from ~ (between events). 

         e.g. W = in x; ⊥ 

              W↓ = in x; if (good x) then out 0 
                         else ⊥. 

              meaning that a silently diverging trace should be related to 
              arbitrary "longer" traces. 

          This way one might lose the property that if s ~ t then prefixes of s 
          are related with prefixes of t (of the same length).           

   *)
  Variable rel_box_logical : forall W l m y i,
      psem__S W (ftbd (snoc l y)) ->
      psem__T (W↓) (ftbd (snoc m i)) -> 
      list_rel l m -> 
      is_input__S y -> is_input__T i ->
      rel y i ->
      (* W and W↓ can produce only continuations that are related at
         least up to the next input *)
      (forall s t, prefix (ftbd (snoc l y)) s ->
               prefix (ftbd (snoc m i)) t ->
               vertical_match s t). 

  
  Local Definition rel_FC1 := rel_FC1 compilation_chain 
                                      Source_Semantics Target_Semantics
                                      trace_rel. 

  Local Definition rel_TC := rel_TC compilation_chain 
                                    Source_Semantics Target_Semantics
                                    trace_rel.

 

  (*CA: some previous attempts... 
  
  (* CA: probably wrong *)
  Lemma forward_implies_finpref_backward :
    rel_FC1 ->
    (forall W m, psem__T (W↓) (ftbd m) -> exists l, list_rel l m /\ psem__S W (ftbd l)).
  Proof.
    move => Hfwd W.
    apply: rev_ind. 
     - exists nil. split.
       constructor. 
       move: (non_empty_sem Source_Semantics W) => [s semWs].
       exists s. split; auto. by destruct s. 
     - move => e__T m0 IH psemWcmpm.  
       have psemWcmpm0 : psem__T (W↓) (ftbd m0) by admit. (* deduce it from psemwcmpm *)
       move: (IH psemWcmpm0) => [l0 [rel_l0_m0 psemWl0]]. 
       have [src_case1 | src_case2]  : (exists e__S, rel e__S e__T /\ psem__S W (ftbd (snoc l0 e__S))) \/
                              ~ (exists e__S, rel e__S e__T /\ psem__S W (ftbd (snoc l0 e__S))) by apply: classic. 
       + move: src_case1 => [e__S [rel_es_et psemW_long]]. 
         exists (snoc l0 e__S). split; auto. 
         have Hfoo: m0 ++ [:: e__T] = snoc m0 e__T by admit. 
         rewrite Hfoo. by constructor.   
       + (* now by src_case2 we deduce:
            1.1 s = tstop l0 _ \/
            1.2 s = tsilent l0 \/ 
            1.3 s >= l0 out0

            1.1  

          *) 

         
       Print rel_trg_determinacy. Abort. 


  Lemma forward_implies_finite_trace_backward :
    rel_FC1 ->
    (forall W l es, sem__T (W↓) (tstop l es) -> exists s, s ≅ (tstop l es) /\ sem__S W s). 
  Proof. Admitted.
         
         
  Lemma forward_implies_silent_backward :
    rel_FC1 ->
    (forall W l, sem__T (W↓) (tsilent l) -> exists s, s ≅ (tsilent l) /\ sem__S W s). 
  Admitted. 

  Lemma forwad_implies_div_backward :
   rel_FC1 ->
   (forall W l, sem__T (W↓) (tstream l) -> exists s, s ≅ (tstream l) /\ sem__S W s). 
  Proof.  
  move => Hfwd W l semWcmpt.
  Admitted. 
    
  Theorem forward_implies_backward : rel_FC1 -> rel_TC.
  Proof.
    move => Hfwd W t semWcmpt.
    destruct t.
    - by apply: forward_implies_finite_trace_backward.
    - by apply: forward_implies_silent_backward.   
    - by apply: forwad_implies_div_backward. 
   Qed.

  *)    
    
End FC_TC.