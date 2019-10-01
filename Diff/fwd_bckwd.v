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
  Variable is_input__S : list ev__S -> bool. 
  Variable is_input__T : list ev__T -> bool.
  
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

  (* we assume a relation over lists of events because we might want to realte
     a single source events to a sequence of target events
  *)
  Variable rel : (list ev__S) -> (list ev__T) -> Prop.

  Variable inputs_related_only_with_inputs :
    forall l m, rel l m -> is_input__S l = is_input__T m.

  Variable rel_right_total_on_inputs : forall m, is_input__T m = true -> exists l, rel l m.  

  Lemma rel_right_total_is_input :
    forall m, is_input__T m = true -> exists l, rel l m /\ is_input__S l = true.
  Proof.
    move => et et_input.
    destruct (rel_right_total_on_inputs et_input) as [es rel_es_et].
    exists es. split; auto. rewrite -et_input. by apply: inputs_related_only_with_inputs. 
  Qed.                                          

  Definition stream_rel (s : @stream ev__S) (t : @stream ev__T) : Prop :=
    (forall l, list_stream_prefix l s -> exists m, list_stream_prefix m t /\ rel l m) /\
    (forall m, list_stream_prefix m t -> exists l, list_stream_prefix l s /\ rel l m). 

  (*CA: not sure this is good! 
        we only look at the list/strema of events and require they are related 

        We can relate a source terminating trace with a target silenlty diverging one! 

        not sure this is necessary in the proof! (pending more for "yes it is necessary")
  *)
  Definition trace_rel (s : trace__S) (t : trace__T) : Prop :=
    match s, t with
    | tstop l _ , tstop m _ => rel l m
    | tstop l _, tsilent m => rel l m
    | tstop l _, tstream m => exists mm, list_stream_prefix mm m /\ rel l mm
    | tsilent l , tstop m _ => rel l m
    | tsilent l , tsilent m => rel l m
    | tsilent l, tstream m  => exists mm, list_stream_prefix mm m /\ rel l mm
    | tstream l , tstop m _ => exists ll, list_stream_prefix ll l /\ rel ll m
    | tstream l, tsilent m => exists ll, list_stream_prefix ll l  /\ rel ll m
    | tstream l, tstream m => stream_rel l m
    end.  

  Definition pref_rel (l : finpref__S) (m : finpref__T) : Prop :=
    match l, m with
    | fstop h _ , fstop k _ => rel h k
    | fstop h _ , ftbd k    => rel h k
    | ftbd  h   , fstop k _ => rel h k
    | ftbd  h   , ftbd k    => rel h k
    end.                   
    
  Local Notation "s ≅ t" := (trace_rel s t) (at level 50).

  Locate input_totality.
  
  Variable src_input_totality : input_totality is_input__S Source_Semantics.
  
  Variable rel_trg_determinacy : forall W t1 t2,
      sem__T (W↓) t1 -> sem__T (W↓) t2 ->
      ((forall s, sem__S W s -> s ≅ t1 -> s ≅ t2) (* relaxing t1 = t2 *) \/
      (exists m1 m2 i1 i2, i1 <> i2 /\
                      (forall l, rel l m1 -> rel l m2) /\
                      prefix (ftbd (m1 ++ i1)) t1 /\
                      prefix (ftbd (m2 ++ i2)) t2)).

  Variable rel_box_logical : forall W l l1 m m1 y i,
      psem__S W (ftbd (l ++ y ++ l1)) ->
      psem__T (W↓) (ftbd (m ++ i ++ m1)) -> 
      rel l m -> rel y i ->
      is_input__S y -> is_input__T i ->
      rel l1 m1.

  
  Local Definition rel_FC1 := rel_FC1 compilation_chain 
                                      Source_Semantics Target_Semantics
                                      trace_rel. 

  Local Definition rel_TC := rel_TC compilation_chain 
                                    Source_Semantics Target_Semantics
                                    trace_rel.

  Lemma not_rel_first_time_on_inputs (W : prg__S) (s : trace__S) (t : trace__T) :
    rel_FC1 -> sem__T (W↓) t -> sem__S W s ->
    ~s ≅ t -> (exists l m y i,
                  is_input__S y = true /\ is_input__T i = true /\
                  ~ rel y i /\ 
                  prefix (ftbd (l ++ y)) s /\
                  prefix (ftbd (m ++ i)) t).
  Proof.
   (* 1. use FC~ to get t0 s.t. s ~ t0 
       2. use target determinacy to get s ~ t \/ t0,t "differ" the first time 
          on inputs i, i0 with i0 ~ y0
       3. if y0 ~ i then look at the next input in t (using box_logical) --
           if all inputs i' in t are related to the corresponding s inputs then by box_logical 
           the traces are related 
       3bis. if ¬ y0 ~ i then we are done 
     *) Admitted.  

  
  Lemma forward_implies_finpref_backward :
    rel_FC1 ->
    (forall W t m, sem__T (W↓) t -> prefix m t -> exists l, pref_rel l m /\ psem__S W l).
  Admitted.

  Lemma forward_implies_finite_trace_backward :
    rel_FC1 ->
    (forall W l es, sem__T (W↓) (tstop l es) -> exists s, s ≅ (tstop l es) /\ sem__S W s). 
  Admitted. (* immediate from forward_implies_finpref_backward *)

  Lemma forward_implies_silent_backward :
    rel_FC1 ->
    (forall W l, sem__T (W↓) (tsilent l) -> exists s, s ≅ (tsilent l) /\ sem__S W s). 
  Admitted. (* immediate from forward_implies_finpref_backward *)

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
    
    
End FC_TC.