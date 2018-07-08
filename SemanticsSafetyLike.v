Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.

Section Main.

Variable partial : Set.
Variable program : Set.
Variable context : Set.
Variable plug : partial -> context -> program.
  
Variable cfg : Set.
Variable init : program -> cfg. 
Variable step : cfg -> event -> cfg -> Prop.

Definition stuck (c:cfg) : Prop :=  forall e c', ~step c e c'.

CoInductive sem' : cfg -> trace -> Prop :=
| SStop : forall c, stuck c -> sem' c tstop
| SCons : forall c e c' t, step c e c' -> sem' c' t -> sem' c (tcons e t).

Definition sem (p:program) : trace -> Prop := sem' (init p).

Lemma non_empty_sem : forall P, exists t, sem P t.
Admitted.

Definition lang : level := @Build_level partial
                                        program
                                        context
                                        plug
                                        sem
                                        non_empty_sem.

Lemma tgt_sem : semantics_safety_like lang.
Admitted.

End Main.
