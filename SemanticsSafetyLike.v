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
Proof.
  unfold semantics_safety_like. simpl.
  intros t P Hsem Hinf.
  (*unfold psem. simpl.*)
  (* Basic idea: if t is not in sem P, there is a prefix of t, m (here
     signified with a dependent type for the sake of simplicity), that
     does not belong to psem P. The argument can be that if every prefix
     of t is in the semantics, then t itself must be, too.

     Consider now the initial bad prefix m. If m is empty, choose it as
     the minimal bad prefix and any event as the bad event: these two
     instantiate the existentials in the goal. If m = snoc m' e, there
     are two possible cases: if m' is in sem P, it is the minimal bad
     prefix and e the bad event, and we are done; if m' is still not in
     sem P, we continue reducing it. (Thus, an easy induction.) *)
Admitted.

End Main.
