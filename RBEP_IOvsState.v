Require Import Setoid.
Set Implicit Arguments.

(* Boolean expressions with infinite loops and  IO
  e ::= val b | not e | e1 `and` e2 | input | output e | oforever e  *)

Inductive bexp : Type :=
| Val : bool -> bexp
| Not : bexp -> bexp
| And : bexp -> bexp -> bexp
| Input : bexp
| Output : bexp -> bexp
| OForever : bexp -> bexp.

Inductive event :=
| EInput : bool -> event
| EOutput : bool -> event.

Inductive ndstep : bexp -> option event -> bexp -> Prop :=
| NdNot : forall b, ndstep (Not (Val b)) None (Val (negb b))
| NdAnd : forall b1 b2, ndstep (And (Val b1) (Val b2)) None (Val (andb b1 b2))
| NdInput : forall b, ndstep Input (Some (EInput b)) (Val b)
| NdOutput : forall b, ndstep (Output (Val b)) (Some (EOutput b)) (Val b)
| NdOForever :  forall b, ndstep (OForever (Val b)) (Some (EOutput b)) (OForever (Val b))
| NdNot1 : forall be e be', ndstep be e be' -> ndstep (Not be) e (Not be')
(* TODO: also all the context rules *)
.

(* Vanilla lazy lists with a terminal result *)
CoInductive trace (a:Type) :=
| Done : bool -> trace a
| More : a -> trace a -> trace a.
Arguments Done {a}.

Definition out (a:Type) (b:bool) := More (EOutput b) (Done b).

CoFixpoint map_trace {a:Type} (f:bool->bool) (xs:trace a) :=
match xs with
| Done b => Done (f b)
| More x xs' => More x (map_trace f xs')
end.

CoFixpoint snoc_trace {a:Type} (xs:trace a) (f : bool -> trace a) :=
match xs with
| Done b => f b
| More x' xs' => More x' (snoc_trace xs' f)
end.

CoFixpoint append_traces {a:Type} (f:bool->bool->bool) (xs ys:trace a) :=
match xs with
| Done b => map_trace (f b) ys
| More x xs' => More x (append_traces f xs' ys)
end.

CoFixpoint forever (b:bool) : trace event := More (EOutput b) (forever b).

CoInductive ndeval : bexp -> (trace event) -> Prop :=
| NdEvalVal : forall b, ndeval (Val b) (Done b)
| NdEvalNot : forall be t, ndeval be t -> ndeval (Not be) (map_trace negb t)
| NdEvalAnd : forall be1 t1 be2 t2,
         ndeval be1 t1 -> ndeval be2 t2 -> ndeval (And be1 be2) (append_traces andb t1 t2)
| NdEvalInput : forall b, ndeval Input (More (EInput b) (Done b))
| NdEvalOutput : forall be t, ndeval be t -> ndeval (Output be) (snoc_trace t (out event))
| NdEvalOForever : forall be t, ndeval be t -> ndeval (OForever be) (snoc_trace t forever).

CoInductive stream (a:Type) :=
| SCons : a -> stream a -> stream a.

Inductive output :=
| OInput : output (* inputs are replaced by opaque markers *)
| OOutput : bool -> output.

(* CoFixpoint rest (s:stream bool) (os:trace output) : stream bool := *)
(* match os with *)
(* | Done b => s *)
(* | More (OOutput _) xs => rest s xs *)
(* | More OInput xs => *)
(*   match s with *)
(*   | SCons b bs => rest bs xs *)
(*   end *)
(* end. *)

(* CoFixpoint append_traces' (s:stream bool) (f:bool->bool->bool) (xs ys:trace output) : *)
(*   stream bool * trace output := *)
(* match xs with *)
(* | Done b => (s, map_trace (f b) ys) *)
(* | More (OOutput x) xs' => let (s',t) := append_traces' s f xs' ys in (s', More (OOutput x) t) *)
(* | More OInput xs' => *)
(*    match s with *)
(*    | SCons b bs => append_traces' bs f xs' ys *)
(*    end *)
(* end. *)

Inductive input_number : trace output -> nat -> Prop :=
| LoDone : forall b, input_number (Done b) 0
| LoMoreOutput : forall b xs n , input_number xs n -> input_number (More (OOutput b) xs) n
| LoMoreInput : forall xs n , input_number xs n -> input_number (More OInput xs) (S n).

Fixpoint drop (n:nat) (s:stream bool) : stream bool :=
match n, s with
| 0, _ => s
| S n', SCons _ s' => drop n' s'
end.

Definition oout (a:Type) (b:bool) := More (OOutput b) (Done b).

CoFixpoint oforever (b:bool) : trace output := More (OOutput b) (oforever b).

CoInductive steval : (stream bool) -> bexp -> (trace output) -> Prop :=
| StEvalVal : forall s b, steval s (Val b) (Done b)
| StEvalNot : forall s be t, steval s be t -> steval s (Not be) (map_trace negb t)
| StEvalAnd : forall s be1 t1 be2 t2 n,
         steval s be1 t1 -> input_number t1 n ->
         steval (drop n s) be2 t2 ->
         steval s (And be1 be2) (append_traces andb t1 t2)
| StEvalAndLoop : forall s be1 t1 be2,
         steval s be1 t1 -> (forall n, ~input_number t1 n) ->
         steval s (And be1 be2) t1
| StEvalInput : forall b s, steval (SCons b s) Input (More OInput (Done b))
| StEvalOutput : forall s be t, steval s be t -> steval s (Output be) (snoc_trace t (oout event))
| StEvalOForever : forall s be t, steval s be t -> steval s (OForever be) (snoc_trace t oforever).

CoInductive seval : (stream bool) -> bexp -> (trace output) -> (stream bool) -> Prop :=
| SEvalVal : forall s b, seval s (Val b) (Done b) s
| SEvalNot : forall s be t s', seval s be t s' -> seval s (Not be) (map_trace negb t) s'
| SEvalAnd : forall s be1 t1 s1 be2 t2 s2,
         seval s be1 t1 s1 -> seval s1 be2 t2 s2 ->
         seval s (And be1 be2) (append_traces andb t1 t2) s2
| SEvalInput : forall b s, seval (SCons b s) Input (More OInput (Done b)) s
| SEvalOutput : forall s be t s', seval s be t s' -> seval s (Output be) (snoc_trace t (oout event)) s'
| SEvalOForever : forall s be t s', seval s be t s' -> seval s (OForever be) (snoc_trace t oforever) s'.

Definition steval' (s:stream bool) (b:bexp) (t:trace output) := exists s', seval s b t s'.

(* TODO: can we prove that seval/seval' is a function / deterministic?
         can paco solve this? not syntactically guarded *)

CoInductive equal_traces {a:Type} : trace a -> trace a -> Prop :=
| EqDone : forall b, equal_traces (Done b) (Done b)
| EqMore : forall x t1 t2, equal_traces t1 t2 -> equal_traces (More x t1) (More x t2).

Lemma equal_traces_refl {a : Type} : forall (t : trace a), equal_traces t t.
Proof.
  cofix Hfix.
  destruct t.
  constructor.
  constructor. apply Hfix.
Qed.

Lemma equal_traces_map {a : Type} : forall f (t1 t2 : trace a), equal_traces t1 t2 -> equal_traces (map_trace f t1) (map_trace f t2).
Proof.
  cofix Hfix.
  intros f t1 t2 H.
  inversion H.
  - apply equal_traces_refl.
  - subst. admit.
Admitted.

Lemma equal_traces_append {a : Type} : forall f (t1 t2 t3 t4 : trace a),
    equal_traces t1 t2 ->
    equal_traces t3 t4 ->
    equal_traces (append_traces f t1 t3) (append_traces f t2 t4).
Proof.
  admit.
Admitted.

Lemma steval_deterministic : forall s be t1 t2, steval' s be t1 -> steval' s be t2 -> equal_traces t1 t2.
  cofix H. intros s be t1 t2 [s1 H1] [s2 H2]. inversion H1; inversion H2; subst.
  - inversion H7; subst. apply EqDone.
(* will get stuck for Not case *)
Abort. (* TODO: try, maybe also try induction on bexp *)

CoInductive equal_stream : stream bool -> stream bool -> Prop :=
| eq_scons : forall x s1 s2,
    equal_stream s1 s2 ->
    equal_stream (SCons x s1) (SCons x s2)
.

Lemma equal_stream_refl : forall s, equal_stream s s.
Proof.
  cofix Hfix. destruct s; constructor; auto.
Qed.

Lemma seval_deterministic : forall be s t1 t2 s1 s2,
    seval s be t1 s1 ->
    seval s be t2 s2 ->
    equal_traces t1 t2 /\ equal_stream s1 s2.
Proof.
Admitted.
(* Proof. *)
(*   induction be; intros s t1 t2 s1 s2 H1 H2; inversion H1; inversion H2; subst. *)
(*   - split. now constructor. apply equal_stream_refl. *)
(*   - split. apply equal_traces_map. *)
(*     edestruct IHbe with (t1 := t) (t2 := t0); eauto. *)
(*     edestruct IHbe with (t1 := t) (t2 := t0); eauto. *)
(*   - edestruct (IHbe1 _ _ _ _ _ H4 H11) as [Heqt1 Heqs1]. *)

Lemma steval_deterministic : forall be s t1 t2, steval' s be t1 -> steval' s be t2 -> equal_traces t1 t2.
Proof.
  intros be s t1 t2 [s1 H1] [s2 H2].
  destruct (seval_deterministic H1 H2).
  assumption.
Qed.

Lemma steval_defined : forall be s, exists t, steval' s be t.
Admitted.

(* TODO: should we able to get this from some unique choice
   - functional choice can do it only from steval_defined
     https://coq.github.io/doc/master/stdlib/Coq.Logic.IndefiniteDescription.html
*)

CoFixpoint proj_output (t : trace event) : trace output :=
  match t with
  | Done b => Done b
  | More (EInput _) t' => More OInput (proj_output t')
  | More (EOutput x) t' => More (OOutput x) (proj_output t')
  end.

CoFixpoint stutter (b : bool) : stream bool :=
  SCons b (stutter b).

Definition proj_input (t : trace event) : stream bool.
  revert t.
  cofix proj_input.
  intros t.
  exact match t with
  | Done b => stutter true
  | More (EInput b) t' => SCons b (proj_input t')
  | More (EOutput _) t' => proj_input t'
  end.
Admitted.

Definition EE := forall be t,
    ndeval be t <-> steval (proj_input t) be (proj_output t).

Conjecture lang_is_EE : EE.

Axiom inp_no_stutter : trace event -> list bool.
Fixpoint sapp {a : Type} (l : list a) (s : stream a) : stream a :=
  match l with
  | nil => s
  | cons x l' => SCons x (sapp l' s)
  end.

Axiom input_no_stutter_proj_input : forall t,
    sapp (inp_no_stutter t) (stutter true) = proj_input t.

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

CoFixpoint merge ti to :=
  match to with
  | Done b => Done b
  | More OInput to' =>
    match ti with
    | SCons i ti' => More (EInput i) (merge ti' to')
    end
  | More (OOutput o) to' => More (EOutput o) (merge ti to')
  end.

Lemma conjecture2 : forall be t,
    ndeval be t <-> (exists ti to, t = merge ti to /\ steval ti be to).
Proof.
  intros.
  split.
  - intros H.
    exists (sapp (inp_no_stutter t) (stutter true)).
    exists (proj_output t).
    split.
    + admit. (* This should be a property of the definition *)
    + rewrite input_no_stutter_proj_input.
      (* use EE now *)
      now apply lang_is_EE.
Admitted.

Lemma conjecture1 : forall be1 be2,
    (forall t, ndeval be1 t <-> ndeval be2 t) <->
    (forall t,
        (exists ti1 to1, t = merge ti1 to1 /\ steval ti1 be1 to1) <->
        (exists ti2 to2, t = merge ti2 to2 /\ steval ti2 be2 to2)).
Proof.
  intros be1 be2.
  split.
  - intros H t.
    rewrite <- 2!conjecture2.
    now apply H.
  - intros H t.
    rewrite -> 2!conjecture2.
    now apply H.
Qed.
