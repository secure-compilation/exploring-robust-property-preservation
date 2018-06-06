Require Import Events.
Require Import ClassicalExtras.
Require Import TraceModel.
Require Import Properties.
Require Import FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts.

Axiom prop_ext : prop_extensionality.

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

Lemma closure_includes {X : Set} (S: X -> Prop) (τ : @Topology X) :
  forall x, (S x -> (closure S τ) x).
Proof. unfold closure. now auto. Qed. 

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

Lemma not_dense {X : Set} (τ : @Topology X) :
  forall B, ~ (dense τ) B <-> exists A a, A a /\ (open τ) A /\ (forall t, A t -> ~ B t).
Proof.
  unfold dense. intros B. split.
  + rewrite not_forall_ex_not. intros [H h].
    rewrite not_imp in h. destruct h as [h1 h2].
    rewrite not_imp in h2. destruct h2 as [[a Ha] h2].
    rewrite not_ex_forall_not in h2.
    exists H, a. repeat (split; try now auto). 
    intros t ht. now firstorder.
  + rewrite not_forall_ex_not. intros [A [a [H1 [H2 H3]]]].
    exists A. intros ff. destruct (ff H2); try now auto.
    now exists a. apply (H3 x); try now auto.
Qed. 

Lemma full_closed_and_dense {X : Set} (τ : @Topology X) :
  closed τ (fun x => True) /\
  dense τ (fun x => True). 
Proof.
  split.
  - unfold closed.
    assert ((fun x : X => ~ True) = (fun x : X => False)). 
    { apply functional_extensionality. intros x.
      apply prop_ext. tauto. } rewrite H.  
    apply (empty τ).
  - unfold dense. intros A Hop [a Ha].
    now exists a.
Qed. 
  
Theorem only_full_closed_and_dense {X : Set} (τ : @Topology X) :
  forall S, (closed τ S /\ dense τ S) <-> (forall x, S x).
Proof.
  intros S. split.
  - intros [Hc Hd]. apply NNPP. rewrite not_forall_ex_not.
    intros [a H].
    assert (open τ (fun x => ~ S x)). now apply Hc.
    destruct (Hd (fun x => ~ S x)); try now auto. now exists a.
  - intros Hfull. assert (S = fun x => True). { apply functional_extensionality.
    intros x. now apply prop_ext. } rewrite H.                                                    
    now apply full_closed_and_dense.
Qed. 

Lemma s_dense {X : Set} (S : X -> Prop) (τ : @Topology X) :
  (dense τ) (fun x => ~ ((closure S τ) x /\ ~ S x)).
Proof.
  apply NNPP. rewrite not_dense. intros [A [a [Ha [Hop H]]]].
  assert (Hincl1 : forall t, A t -> closure S τ t /\ ~ S t).
  { intros t H0. apply NNPP. now auto. }
  assert (Hincl2 : forall t, S t -> (closure S τ t /\ ~ A t)).
  { intros t H0. split.
    + now apply closure_includes.
    + intros ff. specialize (Hincl1 t ff). specialize (H t ff).
      now auto. } 
  assert (contr : ~ (forall C, (closed τ C) -> (forall b, S b -> C b) ->
                          (forall t, (closure S τ) t -> C t))).
  { intros ff.
    assert (A = fun x => ~ ~ A x).
    { apply functional_extensionality. intros x.
      apply prop_ext. now rewrite <- dne. }
    assert (closed τ (fun x => ~ A x)). 
    { unfold closed. now rewrite <- H0. } 
    assert (forall b, S b -> (fun x => ~ A x) b) by now firstorder.
    specialize (ff (fun x => ~ A x) H1 H2).
    simpl in *. destruct (Hincl1 a Ha) as [k1 k2]. 
    now apply (ff a k1). } 
    apply contr. now apply closure_smallest.
Qed.

Theorem decomposition_theorem {X : Set} (τ : @Topology X) :
  forall S, (exists C D, closed τ C /\ dense τ D /\
               (forall x, S x <-> (C x  /\ D x))).
Proof.
  intros S. exists (closure S τ), (fun x => ~ ((closure S τ) x /\ ~ S x)). 
  split.
  - now apply closure_is_closed.
  - split.
    + now apply  s_dense.
    + intros x. split.
      ++ intros Hs. split.
         * now apply closure_includes. 
         * now firstorder.
      ++ intros [Hc Hconj]. rewrite de_morgan1 in Hconj. 
         destruct Hconj; try now auto. now rewrite dne.
Qed. 

