Require Import TraceModel. 
Require Import Properties.
Require Import ClassicalExtras.

Set Implicit Arguments. 

Record level :=
  {
    prg  : Set;
    ctx  : Set;   
    plug : prg -> ctx -> prg;
    sem  : prg -> prop;
    non_empty_sem : forall P, exists t, sem P t
  }.

  
Axiom src : level.
Axiom tgt : level.
Axiom compile : (prg src) -> (prg tgt).

Notation "C [ P ]" := (plug _ P C) (at level 50).
Notation "P ↓" := (compile P) (at level 50). 


Definition psem {K : level}
                (P : prg K)
                (m : finpref) : Prop := 
  exists t, prefix m t /\ (sem K) P t.

Definition sat {K : level}
               (P : prg K)
               (π : prop) : Prop :=
  forall t, sem K P t -> π t.

Definition rsat {K : level}
                (P : prg K)
                (π : prop) : Prop :=
  forall C, sat (C [ P ] ) π. 


Lemma neg_rsat {K : level} :
    forall P π, (~ rsat P π <->
           (exists C t, sem K (C [ P ]) t /\ ~ π t)).
Proof.
   unfold rsat. unfold sat. split.
  - intros r. rewrite not_forall_ex_not in r.
    destruct r as [C r]. rewrite not_forall_ex_not in r.
    destruct r as [t r]. exists C,t. rewrite not_imp in r.
    assumption.
  - intros [C [t r]]. rewrite not_forall_ex_not.
    exists C. rewrite not_forall_ex_not. exists t.
    rewrite not_imp. assumption.
Qed.


Definition beh {K : level} (P : prg K) : prop :=
  fun b => sem K P b.

Definition hsat {K : level}
                (P : prg K)
                (H : hprop) : Prop :=
  H (beh P).

Definition rhsat {K : level}
                 (P : prg K)
                 (H : hprop) : Prop :=
  forall C, hsat ( C [ P ] ) H.

Lemma neg_rhsat {K : level} :
  forall P H,  (~ rhsat P H <-> ( exists (C : ctx K), ~ H (beh ( C [ P ] )))).
Proof.
  intros P H. split; unfold rhsat; intro H0;
  [now rewrite <- not_forall_ex_not | now rewrite not_forall_ex_not].
Qed.   

    