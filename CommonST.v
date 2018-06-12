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

Definition sat2 {K : level} (P1 P2 : @prg K) (r : rel_prop) : Prop :=
  forall t1 t2, sem K P1 t1 -> sem K P2 t2 -> r t1 t2.

Lemma neg_sat2 {K : level} : forall P1 P2 r,
    ~ sat2 P1 P2 r <-> (exists t1 t2, sem K P1 t1 /\ sem K P2 t2 /\ ~ r t1 t2).
Proof.
  unfold sat2. intros P1 P2 r. split.
  +  intros H. rewrite not_forall_ex_not in H.
    destruct H as [t1 H]. rewrite not_forall_ex_not in H.
    destruct H as [t2 H]. rewrite not_imp in H. destruct H as [H1 H2].
    rewrite not_imp in H2. destruct H2 as [H2 H3].
    now exists t1, t2.
  + intros [t1 [t2  [H1 [H2 H3]]]]. rewrite not_forall_ex_not.
    exists t1. rewrite not_forall_ex_not. exists t2.
    rewrite not_imp. split.
    ++ assumption.
    ++ rewrite not_imp. now auto.
Qed. 


Definition rsat2 {K : level} (P1 P2 : @prg K) (r : rel_prop) : Prop :=
  forall C, sat2 (C [ P1 ]) (C [ P2 ]) r.


Definition hsat2 {K : level} (P1 P2 : @prg K) (r : rel_hprop) : Prop :=
   r (sem K P1) (sem K P2).

Definition hrsat2 {K : level} (P1 P2 : @prg K) (r : rel_hprop) : Prop :=
  forall C, r (sem K (C [P1])) (sem K (C [P2])).

