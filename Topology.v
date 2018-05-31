Require Import Events.
Require Import ClassicalExtras.
Require Import TraceModel.
Require Import Properties.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts.

Hypothesis prop_ext : prop_extensionality.

Record Topology {X : Set} :=
  {
    open : (X -> Prop) -> Prop;
    empty : open (fun x : X => False);
    full  : open (fun x : X => True);

    arbitrary_union :
      forall (F : (X -> Prop) -> Prop),
        (forall f, F f -> open f) ->
         open (fun x : X => exists f, F f /\ f x);

    finite_intersection :
      forall A1 A2, open A1 -> open A2 ->
       open (fun x : X => A1 x /\ A2 x)                        
  }.

Definition closed {X : Set} (τ : @Topology X) :
                  (X -> Prop) -> Prop :=
  (fun C => (open τ) (fun x => (~ C x))).

Lemma arbitrary_intersection {X : Set} (τ : @Topology X) :
   forall (F : (X -> Prop) -> Prop),
        (forall f, F f -> (closed τ) f) ->
        (closed τ) (fun x : X => (forall f, F f -> f x)).
Proof.
  unfold closed. intros F H. 
  specialize (arbitrary_union τ (fun f =>  F (fun x => ~ f x))).
  assert ((forall f : X -> Prop,
              (fun f0 : X -> Prop =>
                 F (fun x : X => ~ f0 x)) f -> open τ f)).   
  { intros f H0. specialize (H (fun x => ~ f x) H0).
    simpl in H. assert (f = (fun x => ~ ~ f x)).
    apply functional_extensionality. intros x.    
    apply (prop_ext). now rewrite <- dne.
    now rewrite H1. } 
  intros H1. specialize (H1 H0).
  assert ( (fun x : X =>
          exists f : X -> Prop,
            (fun f0 : X -> Prop =>
             F (fun x0 : X => ~ f0 x0)) f /\ 
            f x)  =
         (fun x : X => ~ (forall f : X -> Prop, F f -> f x)
         )).
  { apply functional_extensionality. intros x. apply prop_ext.
    rewrite not_forall_ex_not. split.
    + intros [f [K1 K2]]. exists (fun x => ~ f x). rewrite not_imp.
      split; now auto.
    + intros [f K]. exists (fun x => ~ f x). split; try now auto.
      rewrite not_imp in K. destruct K as [k1 k2].
      assert (f = fun x0 => ~ ~ f x0).
      { apply functional_extensionality. intros x0.
        apply prop_ext. now rewrite <- dne. } 
      now rewrite <- H2. }
  now rewrite <- H2.
Qed.

Lemma finite_union {X : Set} (τ : @Topology X) :
  forall C1 C2, (closed τ) C1 -> (closed τ) C2 ->
           (closed τ) (fun x => C1 x \/ C2 x).
Proof.
  unfold closed. intros C1 C2 H1 H2.
  assert ( (fun x : X => ~ (C1 x \/ C2 x)) = (fun x => ~ C1 x /\ ~ C2 x)).
  { apply functional_extensionality. intros x.
    apply prop_ext. now rewrite de_morgan2. }
  rewrite H. now apply (finite_intersection τ). 
Qed.

Definition closure {X : Set} (S : X -> Prop) (τ : @Topology X) :=
  fun x => (forall C, (closed τ) C -> (forall y, S y -> C y) -> C x).

Lemma closure_is_closed {X : Set} (τ : @Topology X) :
  forall S, (closed τ) (closure S τ).
Proof.
  intros S. unfold closure.
  specialize (arbitrary_intersection τ
              (fun C => (closed τ) C /\ (forall y, S y -> C y))).
  intros Hint.
  assert (forall K, ((fun C => (closed τ) C /\ (forall y, S y -> C y)) K)
               -> closed τ K) by easy. 
  specialize (Hint H); clear H.
  simpl in Hint.
  assert ((fun x : X =>
            forall f : X -> Prop,
            closed τ f /\ (forall y : X, S y -> f y) -> f x)
           =
          (fun x : X =>
            forall C : X -> Prop,
              closed τ C -> (forall y : X, S y -> C y) -> C x)).
  { apply functional_extensionality. intros x.
    apply prop_ext. now firstorder. } 
  now rewrite <- H.           
Qed.

Lemma closure_smallest {X : Set} (S : X -> Prop) (τ : @Topology X) :
  forall C, (closed τ) C ->
       (forall x, S x -> C x) ->
       (forall x, (closure S τ) x -> C x).
Proof. 
  intros C Hcl Hsub x Hc. now apply Hc.  
Qed. 

Definition dense {X : Set} (τ : @Topology X) :
                 (X -> Prop) -> Prop :=
  (fun D => forall A, (open τ) A ->
               (exists a, A a) ->
               (exists d, A d /\ D d)).  

Lemma a_special_dense {X : Set} (S : X -> Prop) (τ : @Topology X) :
  (dense τ) (fun x => ~ (closure S τ) x /\ ~ S x).
Admitted. 
  


(*************************************************************************)
Lemma empty_observable : Observable (fun t => False).
Proof. easy. Qed.

Lemma full_observable : Observable  (fun t => True). 
Proof.
  unfold Observable. intros t ff.
  now exists ftbd.
Qed.

Lemma union_observable : forall H : hprop,
    (forall A, H A -> Observable A) ->
    Observable (fun t => exists A, H A /\ A t).
Proof.
  unfold Observable. intros H h t [A [ha At]].
  destruct (h A ha t At) as [m [h1 h2]].
  exists m. split; try now auto. 
  intros t' pmt'. specialize (h2 t' pmt'). now exists A.
Qed.

Lemma intersection_observable : forall A1 A2,
    Observable A1 -> Observable A2 ->
    Observable (fun t => A1 t /\ A2 t).
Proof.
  unfold Observable. intros A1 A2 h1 h2 t [at1 at2].
  destruct (h1 t at1) as [m1 [h11 h12]].
  destruct (h2 t at2) as [m2 [h21 h22]].
  assert (sh : fpr m1 m2 \/ fpr m2 m1)
    by now apply (same_ext m1 m2 t).
  destruct sh; [exists m2| exists m1 ]; split; auto; intros t' K;  
  [ specialize (h12 t' (fpr_pref_pref m1 m2 t' H K)) 
  | specialize (h22 t' (fpr_pref_pref m2 m1 t' H K))]; now auto.
Qed.

Definition trace_topology := Build_Topology trace
                                      Observable
                                      empty_observable
                                      full_observable
                                      union_observable
                                      intersection_observable.


Check trace_topology.

Lemma safety_closed : forall π, Safety π <-> (closed trace_topology) π.
Proof. easy. Qed.

