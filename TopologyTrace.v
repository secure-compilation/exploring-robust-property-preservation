Require Import ClassicalExtras.
Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import Topology.


(*************************************************************************)
Lemma empty_observable : Observable (fun t => False).
Proof. easy. Qed.

Lemma full_observable : Observable  (fun t => True).
Proof.
  unfold Observable. intros t ff.
  now exists (ftbd nil).
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
    destruct Hd. now exists m. exists (embedding m). now apply embed_pref.
    now exists x.
Qed.


Theorem safety_livenes_only_true :
  forall π, (Safety π /\ Liveness π) <-> (forall t, π t).
Proof.
  intros π. rewrite safety_closed, liveness_dense.
  now apply only_full_closed_and_dense.
Qed.

Theorem decomposition_safety_liveness :
  forall π, exists S L, (Safety S /\ Liveness L /\
               (forall t, π t <-> S t /\ L t)).
Proof.
  intros π.
  destruct  (decomposition_theorem trace_topology π) as [S [L H]].
  rewrite <- safety_closed, <- liveness_dense in H.
  now exists S, L.
Qed.
