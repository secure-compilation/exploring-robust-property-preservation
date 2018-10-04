Require Import TraceModel.
Require Import Properties. 
Require Import Topology.
Require Import TopologyTrace.
Require Import ClassicalExtras.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts.

Hypothesis prop_ext : prop_extensionality.

(* TODO: prove and move to Topology *)
Lemma dense_closure_true (X : Set)
                         (τ : @Topology X)
                         (D : X -> Prop) :
  (forall x : X, (closure D τ) x) -> dense τ D.
Admitted.      
                         

Theorem X_dense_classe
        (X : hprop)
        (dec : forall π, exists S x, Safety S /\ X x /\
                           (forall t, π t <-> (S t /\ x t)))
        (trivial_meet : forall π, X π -> Safety π ->
                             (forall t, π t)) :
        forall π, Liveness π <-> X π.
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
    ++ assert (HD : dense trace_topology π) by now rewrite (liveness_dense π) in HL.
       destruct (HD (fun t => ~ S t)) as [t' [St' pit']]. 
       { now apply safety_closed. }
       { now exists t. }
       destruct (Hmeet t') as [contra foo].
       destruct (contra pit') as [contra' foo']. contradiction.
  + intros HX. rewrite liveness_dense.
    apply (dense_closure_true).
    intros t C HC Hin.
    destruct (dec π) as [S [x [HS [Hx H]]]].
    