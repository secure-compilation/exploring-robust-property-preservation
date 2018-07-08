
(*CA: In this file all and only definitions and lemmas about traces *)

Require Import Events.
Require Import ClassicalExtras.
Require Import Setoid.

(** *traces  *)
CoInductive trace : Set :=
  | tstop : trace
  | tcons : event -> trace -> trace.

(** *finite prefixes *)
Inductive finpref : Set :=
  | fstop : finpref
  | ftbd : finpref 
  | fcons : event -> finpref -> finpref.

(** *prefix relation *)
Fixpoint prefix m t : Prop :=
  match m, t with
  | fstop, tstop | ftbd, _ => True
  | fcons e1 m1, tcons e2 t2 => e1 = e2 /\ prefix m1 t2
  | _, _ => False
  end. 

(** *finite trace*)
Inductive fin : trace -> Prop :=
  | fin_stop : fin tstop
  | fin_cons : forall e t, fin t -> fin (tcons e t).

Definition inf (t : trace) : Prop := ~(fin t).

Lemma fin_or_inf : forall t, fin t \/ inf t.
Proof.
  intros t. unfold inf. now apply classic.
Qed.

Lemma inf_tcons : forall e t, inf (tcons e t) -> inf t.
Proof. intros e t H Hc. apply H. now constructor. Qed.

(* a finite prefix has at least two possible continuations
   as we have at least two distinct events
   CH: this doesn't seem to use different_events though!
*)
Lemma many_continuations :
  forall m ta, inf ta -> exists t', prefix m t' /\ t' <> ta.
Proof.
   induction m as [| | e m' IH]; intros ta Hita.
  - exists tstop. split; try now auto.
    intro Hc. subst. apply Hita. now constructor. 
  - exists tstop. split; try now auto. 
    intro Hc. subst. apply Hita. now constructor. 
  - destruct ta as [| e' ta'].
    + exfalso. apply Hita. now constructor.
    + apply inf_tcons in Hita. specialize (IH ta' Hita). 
      destruct IH as [t' [Hpref Hdiff]]. eexists (tcons e t').
      split; try now auto.
      ++ intro Hc. inversion Hc. now subst. 
Qed.

(* we try to identify a finite trace and the fpref made of the same events *)
Fixpoint equal (m : finpref) (t : trace) : Prop :=
  match m, t with
  | fstop, tstop  => True
  | fcons e2 ms, tcons e1 ts => e1 = e2 /\ equal ms ts
  | _ , _ => False
  end.

Lemma equal_prefix : forall m t, equal m t -> prefix m t.
Proof.
  induction m; destruct t; intro H; simpl in *;
  try now tauto. now firstorder.
Qed.

Lemma fin_equal : forall t, fin t <-> exists m : finpref, equal m t.
Proof.
  intro t. split.
  - intro H. induction H as [| e t H [m IH]];
    [ now exists fstop
    | now exists (fcons e m)]. 
  - intros [m Heq]. generalize dependent t.
    induction m as [| |e m' IH]; intros t Heq; try now auto.
    + destruct t; try now auto. now constructor. 
    + destruct t as [| e' t']; inversion Heq. 
      constructor. now apply IH.
Qed.

Lemma single_cont : forall m t t', equal m t -> prefix m t' -> t = t'.
Proof.
  induction m; destruct t, t'; firstorder.
  subst. now rewrite (IHm t t').
Qed.

Lemma single_cont_consequence : forall t,
    fin t -> exists m, forall t', prefix m t' -> t = t'.
Proof.
  intros t H. destruct (proj1(fin_equal _) H) as [m H'].
  exists m. intros t'. now apply single_cont. 
Qed.

(******************************************************************)

Fixpoint fstopped (m : finpref) : bool:=
  match m with
  | fstop => true
  | ftbd  => false
  | fcons x xs => fstopped xs
  end. 

Lemma stop_sngle_continuation : forall m t1 t2,
    fstopped m = true ->
    prefix m t1 -> prefix m t2 ->
    t1 = t2.
Proof.
  induction m; intros [] [] H H0 H1; try now auto.
  + inversion H0. inversion H1. clear H0 H1.
    subst. simpl in H. specialize (IHm t t0 H H3 H5).
    now subst.
Qed.

Lemma equal_stopped : forall m t,
    equal m t ->
    fstopped m = true.
Proof.
  intros m. induction m; intros t H;
  try now auto.
  destruct t; try now auto. simpl in H.
  destruct H as [H1 H2]. subst.
  simpl. now apply (IHm t).
Qed.

(************************************************************************)

CoFixpoint constant_trace (e : event) : trace := tcons e (constant_trace e).

Theorem trace_eta : forall t, t = match t with
                                  | tstop => tstop
                                  | tcons e t' => tcons e t'
                                  end.
Proof. destruct t; reflexivity. Qed.

Lemma constant_trace_eta : forall e, constant_trace e = tcons e (constant_trace e).
Proof. intro e. now rewrite trace_eta at 1. Qed.

Lemma inf_constant_trace :  forall e, inf (constant_trace e).
Proof.
  intros e Hc. remember (constant_trace e).
  induction Hc; rewrite constant_trace_eta in Heqt; 
  now inversion Heqt. 
Qed.

Lemma const_not_fin : forall e, ~ (exists t, fin t /\ constant_trace e = t).
Proof.
  intros e [t [Ht Heq]].
  rewrite <- Heq in Ht. now apply (inf_constant_trace e Ht).
Qed.

CoInductive all (e:event) : trace -> Prop :=
| acons : forall t, all e t -> all e (tcons e t).

Inductive ends_with (e:event) : trace -> Prop :=
| eall : forall t, all e t -> ends_with e t
| egrow : forall t e', ends_with e t -> ends_with e (tcons e' t).

Lemma ends_with_different : forall t,
  ends_with an_event t -> ends_with another_event t -> False.
Proof.
   intros t Ha Hb. induction Ha.
  - induction Hb.
    + inversion H; inversion H0; subst.
      pose proof different_events. congruence.
    + now inversion H; subst.
  - inversion Hb; subst.
    + inversion H; subst. apply IHHa. now constructor.
    + easy.
Qed.

(************************************************************************)

(** *embed *)
(* a way to get a trace t from a finite prefix m is
   to consider the trace made of the same events of m
   and then add a tstop.
*)
Fixpoint embedding (m : finpref) : trace :=
  match m with
  | fstop | ftbd => tstop
  | fcons e xs => tcons e (embedding xs)
  end.

Lemma embed_pref : forall m, prefix m (embedding m).
Proof. now induction m. Qed.

Lemma embed_fin : forall m, fin (embedding m).
Proof. induction m; now constructor. Qed. 

Lemma embed_eq : forall m, fstopped m = true -> equal m (embedding m).
Proof. induction m; intros H; try now auto. simpl in *. now auto. Qed.

Lemma equal_embedding : forall m t,
    equal m t ->
    embedding m = t. 
Proof.
  induction m; intros t Heq; destruct t; try now auto.
  inversion Heq. simpl. subst. now rewrite (IHm t H0).
Qed.

Lemma embed_cons:  forall m t e,
    embedding m = t ->
    (tcons e (embedding m)) = tcons e t.
Proof.
  intros [] t a He; try now destruct t.
  simpl in *. now rewrite He.
Qed. 

(************************************************************************)

(** *fpr  *)


(* CA: we can define a prefix relation among finite prefixes *)
Fixpoint fpr (m1 m2 : finpref) : Prop :=
  match m1, m2 with
  | ftbd, _ | fstop, fstop => True
  | (fcons x xs), (fcons y ys) => x = y /\ fpr xs ys
  | _, _ => False
  end.

Lemma fpr_reflexivity : forall m, fpr m m.
Proof.  now induction m. Qed.

Lemma fpr_transitivity : forall m1 m2 m3,
    fpr m1 m2 -> fpr m2 m3 -> fpr m1 m3.
Proof.
  induction m1; intros m2 m3 H2 H3; auto;
  destruct m2; inversion H2; auto.
  + destruct m3; inversion H3. subst. simpl.
    split; auto. now apply (IHm1 m2 m3).
Qed.

Lemma fpr_pref_pref : forall m1 m2 t,
    fpr m1 m2 -> prefix m2 t -> prefix m1 t.
Proof.
  induction m1; intros [] [] H1 H2;
  try (now auto); inversion H1; inversion H2; subst; auto.
  simpl. split; auto. now apply (IHm1 f t).
Qed.

Lemma a_foo_lemma : forall m,
    fpr m ftbd -> m = ftbd.
Proof. now induction m. Qed.

Lemma another_foo_lemma : forall m1 m2 e,
    fpr m1 m2 -> fpr (fcons e m1) (fcons e m2).
Proof. now induction m1. Qed.

Lemma same_ext : forall m1 m2 t,
    prefix m1 t -> prefix m2 t ->
    fpr m1 m2 \/ fpr m2 m1.
Proof.
  induction m1; intros [] [] H1 H2;
  try (now auto); inversion H1; inversion H2; subst.
  destruct (IHm1 f t H0 H4) as [K | K];
  [now left | now right].
Qed.

Lemma same_fpr : forall m1 m2 m,
    fpr m1 m -> fpr m2 m ->
    (fpr m1 m2 \/ fpr m2 m1).
Proof.
  induction m1; intros [] [] H1 H2;
  try (now auto); inversion H1; inversion H2; subst.
  destruct (IHm1 f f0 H0 H4) as [K | K];
  [now left | now right].
Qed.

Lemma non_comp_pref_diff_traces : forall t1 t2 m1 m2,
    prefix m1 t1 -> prefix m2 t2 ->
    ~ (fpr m1 m2 \/ fpr m2 m1) -> t1 <> t2.
Proof.
  intros t1 t2 m1 m2 H H0 H1 Hf.
  subst. apply H1. now apply (same_ext m1 m2 t2).
Qed.

Lemma no_prper_fpr_ftbd : forall m, m <> ftbd -> fpr m ftbd -> False.
Proof. now induction m. Qed.

Lemma stop_sngle_continuation_fpr : forall m1 m2,
    fstopped m1 = true ->
    fpr m1 m2 ->
    m1 = m2.
Proof.
  induction m1, m2; try now auto.
  intros H H0. inversion H0. subst. now rewrite (IHm1 m2).
Qed.

(**************************************************)

(** *snoc *)

(* CA: fsnoc is the identity on fstop *)
Fixpoint fsnoc (m:finpref) (e:event) : finpref :=
  match m with
  | fstop => fstop 
  | ftbd => fcons e ftbd
  | fcons m ms => fcons m (fsnoc ms e)
  end.

Lemma stop_snoc_id : forall m e,
    fstopped m = true ->
    fsnoc m e = m.
Proof.
  induction m; try now auto.
  intros e0 H. simpl in *. now rewrite (IHm e0 H).
Qed.

Lemma fpr_snoc_fpr : forall m1 m2 e,
    fpr m1 m2 ->
    fpr m1 (fsnoc m2 e).
Proof.
  induction m1; intros [] a H; try now auto;
  inversion H; subst.
  + simpl in *. destruct H as [H1 H2].
    specialize (IHm1 f a H2). now auto.
Qed.

Lemma snoc_stop' : forall m e b, fstopped (fsnoc m e) = b ->
                            fstopped m = b.
Proof.
  intros m e b H. induction m; inversion H; auto.
    simpl in *. specialize (IHm H0). now rewrite H.
Qed.

Lemma snoc_stop : forall m e b, fstopped (fsnoc m e) = b <->
                                fstopped m = b.
Proof.
  intros m e b. split.
  - now apply snoc_stop'.
  - intros H. apply NNPP. intros ff.
    destruct (fstopped (fsnoc m e)) eqn : Heq;
    destruct b;  try (now apply ff);
    apply snoc_stop' in Heq; now rewrite H in Heq.
Qed.


Lemma compare_with_snoc : forall m1 m e,
    fpr m1 (fsnoc m e) ->
    (fpr m1 m \/ m1 = fsnoc m e).
Proof.
  induction m1, m; intros a H; try now auto.
  + inversion H. apply a_foo_lemma in H1.
    subst. now right.
  + inversion H. subst. specialize (IHm1 m a H1).
    simpl. destruct IHm1.
    ++ now left.
    ++ right. now subst.
Qed.

Lemma snoc_diff : forall m a b,
    fstopped m = false  ->
    fpr (fsnoc m a) (fsnoc m b) ->
    a = b.
Proof.
  intros m a b H H0. eapply (compare_with_snoc (fsnoc m a) m b) in H0.
  destruct H0 as [H0 | H0]; auto; induction m; inversion H;
  inversion H0; auto; try now apply IHm; try now auto. 
Qed.

Lemma no_snoc_fpr_ftb : forall m e, ~ fpr (fsnoc m e) ftbd.
Proof. now induction m. Qed.

Lemma fpr_snoc_ftbd : forall m e f,
    fstopped m = false ->
    fpr (fsnoc m e) (fsnoc ftbd f) ->
    m = ftbd.
Proof.
  intros m e f H H0. induction m; try now auto.
  + simpl in H, H0. inversion H0; clear H0.
    apply no_prper_fpr_ftbd in H2. now exfalso.
    exfalso. now apply (no_snoc_fpr_ftb m e H2).
Qed.

Lemma same_snoc_same_finpref : forall m m0 e1 e2 i1 i2,
    i1 <> i2  -> e1 <> e2 ->
    fstopped m0 = false ->
    fstopped m = false ->
    fpr (fsnoc m0 i1) (fsnoc m e1) ->
    fpr (fsnoc m0 i2) (fsnoc m e2) ->
    m0 = m.
Proof.
  induction m; intros m0 e1 e2 i1 i2 H H0 H1 H2 H3 H4;
  try now auto; simpl in H3, H4.
  + now apply (fpr_snoc_ftbd m0 i1 e1).
  + destruct m0; try now auto; simpl in H4, H4.
    ++ inversion H3. inversion H4. now subst.
    ++ simpl in H1, H2, H3, H4. inversion H3. inversion H4. subst.
       destruct (IHm m0 e1 e2 i1 i2); now auto.
 Qed.

Lemma snoc_lemma : forall m,
    m = ftbd \/
    (exists m' e', m = fsnoc m' e').
Proof.
  intros m. induction m; try now auto.
  + right. now exists fstop, an_event.
  + destruct IHm as [Hftbd | [m' [e' H]]]; right; subst.  
    ++ now exists ftbd, e. 
    ++ now exists (fcons e m'), e'. 
Qed.

Lemma not_stop_not_snoc_pref : forall m e,
    fstopped m = false ->
    fpr (fsnoc m e) m -> False.
Proof.
  intros m e H H0. induction m; try now auto.
  simpl in *. destruct H0 as [Heq H0].
  now apply IHm.
Qed.

Lemma snoc_m_event_equal : forall m e1 e2,
    fstopped m = false ->
    fpr (fsnoc m e1) (fsnoc m e2) ->
    e1 = e2.
Proof.
  intros m e1 e2 Hstop Hfpr.
  induction m; inversion Hfpr; try now auto.
Qed.     

Lemma same_snoc_same_pointwise : forall m1 m2 e1 e2,
    fstopped m1 = false ->
    fstopped m2 = false -> 
    fsnoc m1 e1 = fsnoc m2 e2 ->
    m1 = m2 /\ e1 = e2.
Proof.
  induction m1; intros m2 e1 e2 Hstop1 Hstop2 Heq; try now auto.
  + destruct m2; inversion Heq; try now auto.
    ++ now destruct m2. 
  + destruct m2; inversion Heq; try now auto.
    ++ exfalso. apply (no_snoc_fpr_ftb m1 e1). now rewrite H1. 
    ++ destruct (IHm1 m2 e1 e2); try now auto.
       now subst.
Qed.

Lemma proper_prefix : forall m t,
    prefix m t -> 
    embedding m <> t ->
    fstopped m = false ->
    (exists e, prefix (fsnoc m e) t).
Proof.
  induction m; intros t Hpref Hembed Hstop; try now auto.
  + destruct t. try now auto. now exists e.
  + destruct t; try now auto.
    inversion Hpref. subst. destruct (IHm t) as [e H]; try now auto. 
    intros ff. apply Hembed. simpl. now apply embed_cons.
    now exists e.
Qed.

Lemma fpr_stop_equal : forall m1 m2,
    fpr m1 m2 ->
    fstopped m1 = true ->
    m1 = m2.
Proof.
  intros m1. induction m1; intros m2 Hpref Hstop.
  + now destruct m2. 
  + inversion Hstop.
  + destruct m2; try now auto.
    inversion Hpref. subst. simpl in Hstop.
    now rewrite (IHm1 m2 H0 Hstop).
Qed.


(**********************************************************************)

(** *m[fstop/ftbd] *)

Fixpoint same_events_with_stop (m : finpref) : finpref :=
  match m with
  | ftbd | fstop => fstop
  | fcons x xs => fcons x (same_events_with_stop xs)
  end.

Notation "m [fstop/ftbd]" := (same_events_with_stop m)
                             (at level 50).

Lemma with_stop_fstopped : forall m,
    fstopped (m[fstop/ftbd]) = true.
Proof. now induction m. Qed.

Lemma if_fstopped_equal : forall m,
    fstopped m = true ->
    m = m[fstop/ftbd].
Proof.
  intros m Hstop. induction m; try now auto.
  simpl in Hstop. simpl. now rewrite <- (IHm Hstop).
Qed. 

Lemma embedding_is_the_same : forall m,
    embedding m =
    embedding (m[fstop/ftbd]).
Proof.
  induction m; try now auto. 
  simpl. now rewrite IHm.
Qed. 

Lemma m_fpr_with_stop : forall m,
    fpr m (m[fstop/ftbd]).
Proof. now induction m. Qed.

Lemma with_stop_prefix_embedding :forall m,
    prefix (m [fstop/ftbd]) (embedding m).
Proof. now induction m. Qed.

Lemma equal_with_stop_same_embedding : forall m mm,
    fstopped m = true ->
    fpr mm m ->
    fpr m (mm[fstop/ftbd]) ->
    embedding m = embedding mm.
Proof.
  induction m; intros mm Hstop Hfpr HfprStop; try now destruct mm. 
  simpl in Hstop. simpl.
  destruct mm; try now auto. inversion Hfpr. inversion HfprStop. subst. 
  now rewrite (IHm mm Hstop H0 H2).
Qed.

Lemma proper_fpr: forall m0 mm,
    fpr m0 (mm[fstop/ftbd]) ->
    fstopped m0 = false ->
    fpr m0 mm.
Proof. 
  induction m0; intros mm Hfpr Hstop; try now auto.
  simpl in Hstop. destruct mm; try now auto.
  inversion Hfpr. subst. simpl. split; now auto. 
Qed.

(*******************************************************************************)

CoInductive t_eq : trace -> trace -> Prop :=
| etrace : forall (e : event) t1 t2, t_eq t1 t2 -> t_eq (tcons e t1) (tcons e t2).

Lemma t_eq_symm : forall t1 t2, t_eq t1 t2 -> t_eq t2 t1.
Admitted.

Lemma prefix_preserved : forall m t1 t2, prefix m t1 -> t_eq t1 t2 -> prefix m t2.
Proof.
  intros m. induction m; intros t1 t2 hpref heq; try now auto.
  + now destruct t1, t2. 
  + destruct t1, t2; try now auto. inversion hpref. subst.   
    inversion heq. subst. simpl. split; try now auto.
    now apply (IHm t1 t2). 
Qed.

Lemma same_finite_prefixes : forall t1 t2, t_eq t1 t2 ->
                             forall m, (prefix m t1) <-> prefix m t2.
Proof.
  intros t1 t2 heq m. split; intros H;
  [now apply (prefix_preserved m t1 t2)
  |apply (prefix_preserved m t2 t1); try now auto].
  now apply t_eq_symm. 
Qed. 

Lemma neq_finitely_refutable : forall t1 t2,
    ~ (t_eq t1 t2) <-> (exists m1 m2, prefix m1 t1 /\ prefix m2 t2 /\ ~ (prefix m1 t2 /\ prefix m2 t1)).
Proof.
  intros t1 t2. split.
  - admit.
  - intros [m1 [m2 [h1 [h2 hn]]]] hf. apply hn. split.
    + now apply (same_finite_prefixes t1 t2).
    + apply t_eq_symm in hf. now apply (same_finite_prefixes t2 t1).
Admitted.

(*******************************************************************************)

Axiom is_input : event -> Prop.

Definition traces_match (t1 t2 : trace) : Prop := 
 t1 = t2 \/
 (exists (m : finpref) (e1 e2 : event),
   is_input e1 /\ is_input e2 /\  e1 <> e2 /\
   fstopped m = false /\ prefix (fsnoc m e1) t1 /\ prefix (fsnoc m e2) t2).
