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

Definition NI : hprop :=
  fun b => forall (t1 t2 : trace), b t1 -> b t2 ->
                           (fin t1 /\ fin t2 /\
                            exists t', filter pub_input t1 t' /\ filter pub_input t2 t') ->
                           exists t', filter pub t1 t' /\ filter pub t2 t'.

    

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
    - 

        
    destruct t1, t2; try now auto.
    - exfalso. apply (H tstop). now split.
    - admit.
    - exfalso
     



Definition fcons e m :=
  match m with
  | fstop p => fstop (cons e p)
  | ftbd p  => ftbd  (cons e p)
  end.
  
Theorem NI_hypersafety : HSafe NI.
Admitted.
