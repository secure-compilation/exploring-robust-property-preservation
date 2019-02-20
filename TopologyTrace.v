Require Import ClassicalExtras. 
Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import Topology.
Require Import Coq.Logic.FunctionalExtensionality.


(*************************************************************************)
Lemma empty_observable : Observable (fun t => False).
Proof. easy. Qed.

Lemma full_observable : Observable  (fun t => True).
Proof.
  unfold Observable. intros t ff.
  exists (ftbd nil); firstorder.
  now case t.  
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

Lemma safety_closed : forall π, Safety π <-> (closed trace_topology) π.
Proof. easy. Qed.

Lemma liveness_dense : forall π, Liveness π <-> (dense trace_topology) π.
Proof.
  intros π. unfold dense. split.
  - intros HL A Hopen [a Ha]. destruct (Hopen a Ha) as [m [Hm Ht]].
    destruct (HL m) as [t [Hpref Hd]]. specialize (Ht t Hpref).
    now exists t.
  - intros Hd m. specialize (Hd (fun t => prefix m t)).
    destruct Hd. now exists m. exists (embedding an_endstate m). now apply embed_pref.
    now exists x.
Qed.

Lemma Dense_dense : forall π, Dense π <-> (dense trace_topology) π.
Proof. intros π. now rewrite <- all_fin_in_all_liv, liveness_dense. Qed. 

Theorem safety_dense_only_true :
  forall π, (Safety π /\ Dense π) <-> (forall t, π t).
Proof.
  intros π. rewrite safety_closed, Dense_dense.
  now apply only_full_closed_and_dense.
Qed.


Theorem decomposition_safety_dense :
  forall π, exists S L, (Safety S /\ Dense L /\
               (forall t, π t <-> S t /\ L t)).
Proof.
  intros π.
  destruct  (decomposition_theorem trace_topology π) as [S [L H]].
  rewrite <- safety_closed, <- Dense_dense in H.
  now exists S, L.
Qed.


Theorem X_dense_class
        (X : hprop)
        (dec : forall π, exists S x, Safety S /\ X x /\
                           (forall t, π t <-> (S t /\ x t)))
        (dec_triv: forall x S x', X x -> Safety S -> X x' ->
                             (forall t, x t <-> (S t /\ x t)) ->
                             (forall t, S t))
        (trivial_meet : forall π, X π -> Safety π ->
                             (forall t, π t)) :
        forall π, (dense trace_topology π) <-> X π.
Proof.
  intros π. split.
  + intros HL. destruct (dec π) as [S [x [Hs [Hx Hmeet]]]].
    assert (K : (forall t, S t) \/ (exists t, ~ S t)).
    { rewrite <- not_forall_ex_not. now apply classic. }
    destruct K as [K | [t Ht]].
    ++ assert (kk : π = x).
       { apply functional_extensionality. 
         intros t. specialize K with t.
         specialize Hmeet with t.
         apply prop_ext. now firstorder. } 
       now rewrite kk.
    ++ destruct (HL (fun t => ~ S t)) as [t' [St' pit']]. 
       { now apply safety_closed. }
       { now exists t. }
       destruct (Hmeet t') as [contra foo].
       destruct (contra pit') as [contra' foo']. contradiction.
  + intros HX. 
    apply (dense_closure_true).
    intros t C HC H. apply (dec_triv π C π); auto. 
    firstorder.
Qed.


Theorem X_Dense_class
        (X : hprop)
        (dec : forall π, exists S x, Safety S /\ X x /\
                           (forall t, π t <-> (S t /\ x t)))
        (dec_triv: forall x S x', X x -> Safety S -> X x' ->
                             (forall t, x t <-> (S t /\ x t)) ->
                             (forall t, S t))
        (trivial_meet : forall π, X π -> Safety π ->
                             (forall t, π t)) :
  forall π, Dense π <-> X π.
Proof. intros π. rewrite <- (X_dense_class X); try now auto; try now rewrite Dense_dense;
                   auto.
Qed.        
