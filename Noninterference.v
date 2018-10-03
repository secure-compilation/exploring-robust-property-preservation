Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import ClassicalExtras.
Require Import Coq.Logic.FunctionalExtensionality.

Inductive filter (P : event -> Prop) : trace -> trace -> Prop :=
| filter_tstop : filter P tstop tstop
| filter_tsilent : filter P tsilent tsilent
| filter_tcons_true : forall (e : event) (t t' : trace),
    filter P t t' ->
    P e ->
    filter P (tcons e t) (tcons e t')
| filter_tcons_false : forall (e : event) (t t' : trace),
    filter P t t' ->
    ~ P e ->
    filter P (tcons e t) t'
.
Hint Constructors filter.

Axiom pub : event -> Prop.
Axiom input : event -> Prop.

Definition pub_input : event -> Prop :=
  fun i => pub i /\ input i.

Definition stopped := fin.

(* Definition ni : hprop := *)
(*   fun b => forall (p1 p2 : list event), b (fstop p1) -> b (ftop p2) -> *)
(*                                 (filter pi p1) = (filter pi p2) -> *)
(*                                 (filter pub p1) = (filter pub p2). *)


(* First definition of noninterference, with filter *)
Definition NI : hprop :=
  fun b => forall (t1 t2 : trace), b t1 -> b t2 ->
                           (fin t1 /\ fin t2 /\
                            exists t', filter pub_input t1 t' /\ filter pub_input t2 t') ->
                           exists t', filter pub t1 t' /\ filter pub t2 t'.


Inductive eq_prop (P : event -> Prop) : trace -> trace -> Prop :=
| eq_prop_tstop : eq_prop P tstop tstop
| eq_prop_tsilent : eq_prop P tsilent tsilent
| eq_prop_tcons_true : forall (e : event) (t t' : trace),
    eq_prop P t t' ->
    eq_prop P (tcons e t) (tcons e t')
| eq_prop_tcons_false_left : forall (e : event) (t t' : trace),
    eq_prop P t t' ->
    ~ (P e) ->
    eq_prop P (tcons e t) t'
| eq_prop_tcons_false_right : forall (e : event) (t t' : trace),
    eq_prop P t t' ->
    ~ (P e) ->
    eq_prop P t (tcons e t')
.


(* Second definition of noninterference, with eq_prop *)
Definition NI' : hprop :=
  fun b => forall (t1 t2 : trace), b t1 -> b t2 ->
                           (fin t1 /\ fin t2 /\ @eq_prop pub_input t1 t2) ->
                           @eq_prop pub t1 t2.

Theorem NI_hypersafety : HSafe NI.
Proof.
  unfold HSafe.
  intros b HnNI.
  unfold NI in HnNI.
  rewrite not_forall_ex_not in HnNI.
  destruct HnNI as [t1 HnNI].
  rewrite not_forall_ex_not in HnNI.
  destruct HnNI as [t2 HnNI].
  rewrite not_imp in HnNI; destruct HnNI as [Hbt1 HnNI].
  rewrite not_imp in HnNI; destruct HnNI as [Hbt2 HnNI].
  rewrite not_imp in HnNI; destruct HnNI as [[H1 [H2 H3]] HnNI].
  destruct H3 as [t' [Ht'1 Ht'2]].
  rewrite not_ex_forall_not in HnNI.
  assert (H: forall (t1 t2 : trace), fin t1 -> fin t2 -> 
             (forall (t : trace), ~(filter pub t1 t /\ filter pub t2 t)) ->
             exists (m1 m2 : finpref), prefix m1 t1 /\ prefix m2 t2 /\
                                  (forall t1' t2', prefix m1 t1' -> prefix m2 t2' ->
                                              forall (t' : trace), ~(filter pub t1' t' /\ filter pub t2' t'))
         ).
  { clear.
    intros t1 t2 Hfin1 Hfin2.
    induction Hfin1; induction Hfin2; intros H; try now auto.
    - exfalso. apply (H tstop). now split.
    - admit.
    - admit.
    - admit.
  }
  specialize (H t1 t2 H1 H2 HnNI).
  destruct H as [m1 [m2 [Hpref1 [Hpref2 H]]]].
  exists (fun x => x = m1 \/ x = m2).
  repeat split.
  - admit.
  - unfold spref. intros m Hm. destruct Hm as [Hm | Hm]; subst; now eauto.
  - admit.
Admitted.

Theorem NI'_hypersafety : HSafe NI'.
Proof.
  unfold HSafe, NI'.
  intros b HnNI.
  rewrite not_forall_ex_not in HnNI.
  destruct HnNI as [t1 HnNI].
  rewrite not_forall_ex_not in HnNI.
  destruct HnNI as [t2 HnNI].
  rewrite not_imp in HnNI; destruct HnNI as [Hbt1 HnNI].
  rewrite not_imp in HnNI; destruct HnNI as [Hbt2 HnNI].
  rewrite not_imp in HnNI; destruct HnNI as [[Hfin1 [Hfin2 Heq]] HnNI].
  (* I should probably use a custom induction theorem *)
  induction Heq. 
  - exfalso; apply HnNI. now constructor.
  - exfalso; apply HnNI. now constructor.
  - (* how to proceed? we need `b t` to apply the induction hypothesis, but have only
       `b (tcons e t)` *)
    assert (H1: b t) by admit.
    assert (H2: b t') by admit.
    assert (H3: fin t) by now inversion Hfin1.
    assert (H4: fin t') by now inversion Hfin2.
    assert (H5: ~ eq_prop pub t t').
    { intros Hn. apply HnNI. now constructor. }
    specialize (IHHeq H1 H2 H3 H4 H5).
    destruct IHHeq as [M [HM [HMb H]]].
    (* This becomes too easy now... probably because the induction hypothesis is too strong *)
    exists M. repeat split; try now auto.
  - admit.
  - admit.
Admitted.