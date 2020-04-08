Require Import Setoid.
Set Implicit Arguments.

(* (* Boolean expressions with infinite loops and  IO *)
(*   e ::= val b | not e | e1 `and` e2 | input | output e | oforever e  *) *)

(* Inductive event := *)
(* | EInput : bool -> event *)
(* | EOutput : bool -> event. *)

(* (* Vanilla lazy lists with a terminal result *) *)
(* CoInductive trace (a:Type) := *)
(* | Done : bool -> trace a *)
(* | More : a -> trace a -> trace a. *)
(* Arguments Done {a}. *)

(* Definition out (a:Type) (b:bool) := More (EOutput b) (Done b). *)
(* CoFixpoint map_trace {a:Type} (f:bool->bool) (xs:trace a) := *)
(* match xs with *)
(* | Done b => Done (f b) *)
(* | More x xs' => More x (map_trace f xs') *)
(* end. *)

(* CoFixpoint snoc_trace {a:Type} (xs:trace a) (f : bool -> trace a) := *)
(* match xs with *)
(* | Done b => f b *)
(* | More x' xs' => More x' (snoc_trace xs' f) *)
(* end. *)

(* CoFixpoint append_traces {a:Type} (f:bool->bool->bool) (xs ys:trace a) := *)
(* match xs with *)
(* | Done b => map_trace (f b) ys *)
(* | More x xs' => More x (append_traces f xs' ys) *)
(* end. *)

(* CoFixpoint forever (b:bool) : trace event := More (EOutput b) (forever b). *)

(* CoInductive stream (a:Type) := *)
(* | SCons : a -> stream a -> stream a. *)

(* Inductive output := *)
(* | OInput : output (* inputs are replaced by opaque markers *) *)
(* | OOutput : bool -> output. *)

(* Fixpoint drop (n:nat) (s:stream bool) : stream bool := *)
(* match n, s with *)
(* | 0, _ => s *)
(* | S n', SCons _ s' => drop n' s' *)
(* end. *)
(* Definition oout (a:Type) (b:bool) := More (OOutput b) (Done b). *)

(* CoFixpoint oforever (b:bool) : trace output := More (OOutput b) (oforever b). *)

(* CoInductive equal_traces {a:Type} : trace a -> trace a -> Prop := *)
(* | EqDone : forall b, equal_traces (Done b) (Done b) *)
(* | EqMore : forall x t1 t2, equal_traces t1 t2 -> equal_traces (More x t1) (More x t2). *)

(* Lemma equal_traces_refl {a : Type} : forall (t : trace a), equal_traces t t. *)
(* Proof. *)
(*   cofix Hfix. *)
(*   destruct t. *)
(*   constructor. *)
(*   constructor. apply Hfix. *)
(* Qed. *)

(* Lemma equal_traces_map {a : Type} : forall f (t1 t2 : trace a), equal_traces t1 t2 -> equal_traces (map_trace f t1) (map_trace f t2). *)
(* Proof. *)
(*   cofix Hfix. *)
(*   intros f t1 t2 H. *)
(*   inversion H. *)
(*   - apply equal_traces_refl. *)
(*   - subst. admit. *)
(* Admitted. *)

(* Lemma equal_traces_append {a : Type} : forall f (t1 t2 t3 t4 : trace a), *)
(*     equal_traces t1 t2 -> *)
(*     equal_traces t3 t4 -> *)
(*     equal_traces (append_traces f t1 t3) (append_traces f t2 t4). *)
(* Proof. *)
(*   admit. *)
(* Admitted. *)

(* CoInductive equal_stream : stream bool -> stream bool -> Prop := *)
(* | eq_scons : forall x s1 s2, *)
(*     equal_stream s1 s2 -> *)
(*     equal_stream (SCons x s1) (SCons x s2) *)
(* . *)

(* Lemma equal_stream_refl : forall s, equal_stream s s. *)
(* Proof. *)
(*   cofix Hfix. destruct s; constructor; auto. *)
(* Qed. *)


(* CoFixpoint proj_output (t : trace event) : trace output := *)
(*   match t with *)
(*   | Done b => Done b *)
(*   | More (EInput _) t' => More OInput (proj_output t') *)
(*   | More (EOutput x) t' => More (OOutput x) (proj_output t') *)
(*   end. *)

(* CoFixpoint stutter (b : bool) : stream bool := *)
(*   SCons b (stutter b). *)

(* Definition proj_input (t : trace event) : stream bool. *)
(*   revert t. *)
(*   cofix proj_input. *)
(*   intros t. *)
(*   exact match t with *)
(*   | Done b => stutter true *)
(*   | More (EInput b) t' => SCons b (proj_input t') *)
(*   | More (EOutput _) t' => proj_input t' *)
(*   end. *)
(* Admitted. *)

(* Fixpoint sapp {a : Type} (l : list a) (s : stream a) : stream a := *)
(*   match l with *)
(*   | nil => s *)
(*   | cons x l' => SCons x (sapp l' s) *)
(*   end. *)

(* CoFixpoint merge ti to := *)
(*   match to with *)
(*   | Done b => Done b *)
(*   | More OInput to' => *)
(*     match ti with *)
(*     | SCons i ti' => More (EInput i) (merge ti' to') *)
(*     end *)
(*   | More (OOutput o) to' => More (EOutput o) (merge ti to') *)
(*   end. *)


(** Trace Model **)
Axiom trace : Type. (* Traces for the fully nondeterministic case *)
Axiom input_stream : Type. (* Input streams for the state-based nondeterminism *)
Axiom output_trace : Type. (* Output traces for the state-based nondeterminism *)

Axiom proj_input : trace -> input_stream. (* Generally easy to define, just need
                                            to be careful with the stuttering at the end *)
Axiom proj_output : trace -> output_trace.
Axiom merge : input_stream -> output_trace -> trace.

(* These properties are not trivial. While proj_output_merge seems fairly easy to
   prove, I believe proj_input_merge do not hold in most cases. Indeed, if not all
   inputs are consumed, then one need to ignore the junk inputs at the end *)
Conjecture proj_output_merge : forall ti to, proj_output (merge ti to) = to.
(* Conjecture proj_input_merge : forall ti to, proj_input (merge ti to) = ti. (* <-- TODO: this is false as stated *) *)

(****** START OF THE INTERESTING STUFF ******)

(* Source language *)
Axiom bexp : Type.
Axiom ndeval : bexp -> trace -> Prop.
Axiom steval : input_stream -> bexp -> output_trace -> Prop.
Definition EE := forall be t,
    ndeval be t <-> steval (proj_input t) be (proj_output t).

(* Target language *)
Axiom bexp' : Type.
Axiom ndeval' : bexp' -> (trace) -> Prop.
Axiom steval' : input_stream -> bexp' -> output_trace -> Prop.
Axiom compile : bexp -> bexp'.

Definition EE' := forall be t,
    ndeval' be t <-> steval' (proj_input t) be (proj_output t).


Conjecture proj_input_merge : forall be ti ti' to,
    proj_input (merge ti to) = ti' ->
    (steval ti be to <-> steval ti' be to).
Conjecture proj_input_merge' : forall be' ti ti' to,
    proj_input (merge ti to) = ti' ->
    (steval' ti be' to <-> steval' ti' be' to).

Definition BEP_IO :=
  forall be1 be2,
    (forall t, ndeval be1 t <-> ndeval be2 t) ->
    (forall t, ndeval' (compile be1) t <-> ndeval' (compile be2) t).

Definition BEP_State :=
  forall be1 be2 is1 is2,
    (* Input stream quantified at highest level, as if it were part of the program *)
    (forall os, steval is1 be1 os <-> steval is2 be2 os) ->
    (forall os, steval' is1 (compile be1) os <-> steval' is2 (compile be2) os).

Lemma ndeval_merge : forall be is1 os1,
    EE ->
    ndeval be (merge is1 os1) <-> steval is1 be os1.
Proof.
  intros be is1 os1 HEE. rewrite (HEE _ _).
  rewrite proj_output_merge.
  symmetry.
  now apply proj_input_merge.
Qed.

Lemma BEP_State_to_IO {lang_is_EE : EE} {lang_is_EE' : EE'} : BEP_State -> BEP_IO.
Proof.
  unfold BEP_State, BEP_IO.
  intros H be1 be2 H0.
  assert (H' : forall (be1 be2 : bexp) (is1 : input_stream),
             (forall os : output_trace,
                 steval is1 be1 os <-> steval is1 be2 os) ->
             forall os : output_trace,
               steval' is1 (compile be1) os <->
               steval' is1 (compile be2) os)
    by now auto.
  (* Key step: (∀s. (A(s) => B(s)))
                =>  (∀s. A(s)) => (∀s. B(s)) *)
  assert (H'' : forall (be1 be2 : bexp),
             (forall os is1,
                 steval is1 be1 os <-> steval is1 be2 os) ->
             forall os is1,
               steval' is1 (compile be1) os <->
               steval' is1 (compile be2) os)
    by now auto.
  clear H H'.
  intros t.
  do 2 rewrite (lang_is_EE' _ _).
  apply H''. intros os1 is1.
  specialize (H0 (merge is1 os1)).
  now do 2 rewrite ndeval_merge in H0.
Qed.

(* CH: inp_no_stutter relies on an invariant of our semantics (that we consume only
   finite input) that's not true in general and it's anyway not exposed in the
   type of traces. This doesn't seem so hard to fix though, could return a lazy
   list and appending to lazy lists is just fine ... if it's already infinite it
   does nothing. *)
Axiom inp_no_stutter : trace -> list nat.
Axiom sapp : list nat -> input_stream -> input_stream.
Axiom stutter : input_stream.
Axiom input_no_stutter_proj_input : forall t,
    sapp (inp_no_stutter t) (stutter) = proj_input t.
Axiom steval_input_no_stutter : forall be t junk_in junk_in',
    steval (sapp (inp_no_stutter t) junk_in) be (proj_output t) <->
    steval (sapp (inp_no_stutter t) junk_in') be (proj_output t).

Definition EE1 := forall be t,
    ndeval be t ->
    forall junk_in,
      steval (sapp (inp_no_stutter t) junk_in) be (proj_output t).

Definition EE2 := forall be t junk_in,
    steval (sapp (inp_no_stutter t) junk_in) be (proj_output t) ->
    ndeval be t.

Lemma EE_EE1_EE2 : EE <-> (EE1 /\ EE2).
Proof.
  unfold EE, EE1, EE2.
  split.
  - intros H.
    split.
    + intros be t H0 junk_in.
      eapply steval_input_no_stutter.
      rewrite input_no_stutter_proj_input.
      now apply H.
    + intros be t junk_in H0.
      eapply H.
      erewrite <- input_no_stutter_proj_input.
      eapply steval_input_no_stutter.
      eassumption.
  - intros [H1 H2] be t.
    split.
    + intros H.
      rewrite <- input_no_stutter_proj_input.
      now eapply H1.
    + intros H.
      eapply H2.
      now rewrite input_no_stutter_proj_input.
Qed.

(* CH: Not sure about how useful conjecture1 and conjecture2 are,
       what's more useful is ndeval_merge at the end *)

Conjecture merge_proj : forall t, merge (proj_input t) (proj_output t) = t.
Lemma conjecture2 (lang_is_EE : EE): forall be t,
    ndeval be t <-> (exists ti to, t = merge ti to /\ steval ti be to).
Proof.
  intros.
  split.
  - intros H.
    exists (proj_input t).
    exists (proj_output t).
    split.
    + rewrite merge_proj. reflexivity.
    + now apply lang_is_EE.
  - intros [ti [to [H1 H2]]]. subst t.
    unfold EE in lang_is_EE; setoid_rewrite -> lang_is_EE.
    rewrite proj_output_merge.
    pose proof (@proj_input_merge be ti (proj_input (merge ti to)) to eq_refl) as [H _].
    now apply H.
Qed.

Lemma conjecture1 (lang_is_EE:EE) : forall be1 be2,
    (forall t, ndeval be1 t <-> ndeval be2 t) <->
    (forall t,
        (exists ti1 to1, t = merge ti1 to1 /\ steval ti1 be1 to1) <->
        (exists ti2 to2, t = merge ti2 to2 /\ steval ti2 be2 to2)).
Proof.
  intros be1 be2.
  split.
  - intros H t.
    rewrite <- 2!conjecture2; auto.
  - intros H t.
    rewrite -> 2!conjecture2; auto.
Qed.
