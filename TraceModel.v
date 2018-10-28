
(*CA: In this file all and only definitions and lemmas about traces *)

Require Import Events.
Require Import ClassicalExtras.
Require Import Setoid.
Require Import List.

(** *traces  *)
CoInductive trace : Set :=
  | tstop : trace
  | tstuck : trace
  | tsilent : trace
  | tcons : event -> trace -> trace.

(** *finite prefixes *)
Definition pref := list event.

Inductive finpref : Set :=
| fstop : pref -> finpref
| fstuck : pref -> finpref
| ftbd  : pref -> finpref
.

Tactic Notation "destruct" "finpref" ident(m) "as" ident(e) ident(p) :=
  destruct m as [[| |e p] | [| |e p]].

Tactic Notation "induction" "finpref" ident(m) "as" ident(e) ident(p) ident(Hp) :=
  destruct m as [m | m | m]; induction m as [|e p Hp].

(** *prefix relation *)
Fixpoint fstop_prefix (m : pref) (t : trace) : Prop :=
  match m, t with
    | nil, tstop => True
    | nil, _     => False
    | cons e1 m', tcons e2 t' => e1 = e2 /\ fstop_prefix m' t'
    | _, _       => False
  end.

Fixpoint fstuck_prefix (m : pref) (t : trace) : Prop :=
  match m, t with
    | nil, tstuck => True
    | nil, _     => False
    | cons e1 m', tcons e2 t' => e1 = e2 /\ fstuck_prefix m' t'
    | _, _       => False
  end.

Fixpoint ftbd_prefix (m : pref) (t : trace) : Prop :=
  match m, t with
  | nil, _ => True
  | cons e1 m', tcons e2 t' => e1 = e2 /\ ftbd_prefix m' t'
  | _, _ => False
  end.

Definition prefix (m : finpref) (t : trace) : Prop :=
  match m with
  | fstop m => fstop_prefix m t    
  | fstuck m => fstuck_prefix m t
  | ftbd m  => ftbd_prefix m t
  end.

(** *finite trace*)

(* fin and inf now refer to *executions*, not traces!
   Eventually they may be given more memorable names than term/nonterm. *)
Inductive fin : trace -> Prop :=
  | fin_stop : fin tstop
  | fin_stuck : fin tstuck
  | fin_cons : forall e t, fin t -> fin (tcons e t).

Definition inf (t : trace) : Prop := ~(fin t).
Hint Unfold inf.

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
  induction finpref m as e m IHm; intros ta Hinf.
  + exists tstop. split; try now auto.
    intros Hc; subst. apply Hinf. now constructor.
  + destruct ta as [| | | e' ta].
    ++ exfalso. apply Hinf. now constructor.
    ++ exfalso. apply Hinf. now constructor.
    ++ specialize (IHm tsilent Hinf).
       destruct IHm as [t' [Hpref Hnsilent]].
       exists (tcons e t'). now split.
    ++ apply inf_tcons in Hinf. specialize (IHm ta Hinf).
       destruct IHm as [t' [Hpref Hneq]]. exists (tcons e t').
       split; try now auto.
       intros Hc. inversion Hc; now subst.
  + exists tstuck. split; try now auto.
    intros Hc; subst. apply Hinf. now constructor.
  + destruct ta as [| | | e' ta].
    ++ exfalso. apply Hinf. now constructor.
    ++ exfalso. apply Hinf. now constructor.
    ++ specialize (IHm tsilent Hinf).
       destruct IHm as [t' [Hpref Hnsilent]].
       exists (tcons e t'). now split.
    ++ apply inf_tcons in Hinf. specialize (IHm ta Hinf).
       destruct IHm as [t' [Hpref Hneq]]. exists (tcons e t').
       split; try now auto.
       intros Hc. inversion Hc; now subst.
  + exists tstop. split; try now auto.
    intros Hc; subst. apply Hinf. now constructor.
  + destruct ta as [| | | e' ta].
    ++ exfalso. apply Hinf. now constructor.
    ++ exfalso. apply Hinf. now constructor.
    ++ specialize (IHm tsilent Hinf).
       destruct IHm as [t' [Hpref Hnsilent]].
       exists (tcons e t'). now split.
    ++ apply inf_tcons in Hinf. specialize (IHm ta Hinf).
       destruct IHm as [t' [Hpref Hneq]]. exists (tcons e t').
       split; try now auto.
       intros Hc. inversion Hc; now subst.
Qed.

(* we try to identify a finite trace and the fpref made of the same events *)

Fixpoint fstop_equal (m : pref) (t : trace) : Prop :=
  match m, t with
  | nil, tstop => True
  | cons e1 m', tcons e2 t' => e1 = e2 /\ fstop_equal m' t'
  | _, _ => False
  end.

Fixpoint fstuck_equal (m : pref) (t : trace) : Prop :=
  match m, t with
  | nil, tstuck => True
  | cons e1 m', tcons e2 t' => e1 = e2 /\ fstuck_equal m' t'
  | _, _ => False
  end.

Definition ftbd_equal (m : pref) (t : trace) : Prop := False.

Definition equal (m : finpref) (t : trace) : Prop :=
  match m with
  | fstop m => fstop_equal m t
  | fstuck m => fstuck_equal m t
  | ftbd m  => ftbd_equal m t
  end.

Lemma equal_prefix : forall m t, equal m t -> prefix m t.
Proof.
  induction finpref m as e p Hp; destruct t; intros H; now tauto.
Qed.

Lemma fin_equal : forall t, fin t <-> exists m : finpref, equal m t.
Proof.
  intro t. split.
  - intro H. induction H as [| | e t H [m IH]].
    + now (exists (fstop nil)).
    + now (exists (fstuck nil)).
    + destruct m as [m | m | m].
      * now (exists (fstop (cons e m))).
      * now (exists (fstuck (cons e m))).
      * now simpl in IH.
  - intros [m Heq]. generalize dependent t.
    induction finpref m as e m' IH; intros t Heq; try now auto.
    + destruct t; try now auto. now constructor.
    + destruct t as [| | | e' t']; inversion Heq.
      constructor. now apply IH.
    + destruct t as [| | | e' t']; inversion Heq.
      now constructor.
    + destruct t as [| | | e' t']; inversion Heq.
      constructor. now apply IH.
Qed.

Lemma single_cont : forall m t t', equal m t -> prefix m t' -> t = t'.
Proof.
  induction finpref m as e p IHp; destruct t, t'; firstorder;
  subst; now rewrite (IHp t t').
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
  | fstop _ => true
  | ftbd  _ => false
  end. 

Lemma stop_sngle_continuation : forall m t1 t2,
    fstopped m = true ->
    prefix m t1 -> prefix m t2 ->
    t1 = t2.
Proof.
  intros [m | m | m]; induction m; intros [] [] H H0 H1; try now auto.
  + inversion H0. inversion H1. clear H0 H1.
    subst. simpl in H. specialize (IHm t t0 H H3 H5).
    now subst.
Qed.

Lemma equal_stopped : forall m t,
    equal m t ->
    fstopped m = true.
Proof.
  intros [m | m]; induction m; intros t H;
  try now auto.
Qed.

(************************************************************************)

CoFixpoint constant_trace (e : event) : trace := tcons e (constant_trace e).

Theorem trace_eta : forall t, t = match t with
                                  | tstop => tstop
                                  | tsilent => tsilent
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

Fixpoint embedding_pref (m : pref) : trace :=
  match m with
  | nil => tstop
  | cons e m' => tcons e (embedding_pref m')
  end.

Definition embedding (m : finpref) : trace :=
  match m with
  | fstop m | ftbd m => embedding_pref m
  end.

Lemma embed_pref : forall m, prefix m (embedding m).
Proof. destruct m as [m | m]; now induction m. Qed.

Lemma embed_fin : forall m, fin (embedding m).
Proof. destruct m as [m | m]; induction m; now constructor. Qed. 

Lemma embed_eq : forall m, fstopped m = true -> equal m (embedding m).
Proof. destruct m as [m | m]; induction m; intros H; try now auto.
       simpl in *. now auto.
Qed.

Lemma equal_embedding : forall m t,
    equal m t ->
    embedding m = t.
Proof.
  destruct m as [m | m]; induction m; intros t Heq; destruct t; try now auto.
  inversion Heq. simpl. subst.
  assert (H: equal (fstop m) t) by auto.
  assert (H': (embedding (fstop m)) = embedding_pref m) by auto.
  specialize (IHm t H). now subst.
Qed.

Lemma embed_cons:  forall m t e,
    embedding m = t ->
    (tcons e (embedding m)) = tcons e t.
Proof.
  intros [] t a He; try now destruct t.
  simpl in *. now rewrite He.
  simpl in *. now rewrite He.
Qed.

(************************************************************************)

(** *fpr  *)


(* CA: we can define a prefix relation among finite prefixes *)

Fixpoint fpr_ftbd (m1 m2 : pref) : Prop :=
  match m1, m2 with
  | nil, _ => True
  | cons e1 m1', cons e2 m2' => e1 = e2 /\ fpr_ftbd m1' m2'
  | _, _ => False
  end.

(* Not used!! *)
Fixpoint fpr_fstop (m1 m2 : pref) : Prop :=
  match m1, m2 with
  | nil, nil => True
  | cons e1 m1', cons e2 m2' => e1 = e2 /\ fpr_fstop m1' m2'
  | _, _ => False
  end.

Fixpoint fpr (m1 m2 : finpref) : Prop :=
  match m1, m2 with
  | ftbd m1, ftbd m2 | ftbd m1, fstop m2 => fpr_ftbd m1 m2
  (* | ftbd m1, fstop m2 => fpr_ftbd m1 m2 *)                                 
  | fstop m1, fstop m2 => m1 = m2(* or fpr_fstop m1 m2 *)
  | fstop m1, ftbd m2 => False
  end.

Lemma fpr_reflexivity : forall m, fpr m m.
Proof.  destruct m as [m | m]; now induction m. Qed.

Lemma fpr_transitivity : forall m1 m2 m3,
    fpr m1 m2 -> fpr m2 m3 -> fpr m1 m3.
Proof.
  destruct m1 as [m1 | m1];
  induction m1; intros [m2 | m2] [m3 | m3] H2 H3; auto;
  destruct m2; inversion H2; auto;
    destruct m3; inversion H3; subst; simpl; split; auto.
  now apply (IHm1 (ftbd m2) (ftbd m3)).
  now apply (IHm1 (ftbd m2) (ftbd m3)).
Qed.

Lemma fpr_antisymmetry : forall (m m' : finpref),
    fpr m m' /\ fpr m' m -> m = m'.
Proof.
  intros m.
  induction finpref m as e p IHp;
    intros m' [H1 H2];
    destruct finpref m' as e' p';
    try now auto.
  - now inversion H1.
  - specialize (IHp (ftbd p')).
    inversion H1 as [Heq Hpp']; inversion H2 as [_ Hp'p].
    subst.
    simpl in IHp. assert (H: fpr_ftbd p p' /\ fpr_ftbd p' p) by auto.
    specialize (IHp H). now inversion IHp.
Qed.


Lemma fpr_pref_pref : forall m1 m2 t,
    fpr m1 m2 -> prefix m2 t -> prefix m1 t.
Proof.
  destruct m1 as [m1 | m1].
  - induction m1; intros [] [] H1 H2; simpl in *; subst; try (now auto).
  - induction m1 as [| e m1'].
    + intros [] [] H1 H2; simpl in *; subst; try (now auto).
    + intros m2 t. intros H1 H2.
      destruct m2 as [[| e2 m2'] | [| e2 m2']]; simpl in *; subst; try (now auto);
        destruct H1; subst; destruct t; try contradiction;
        destruct H2; subst; split; auto.
      specialize (IHm1' (fstop m2') t); simpl in *; auto.
      specialize (IHm1' (ftbd m2') t); simpl in *; auto.
Qed.

Lemma a_foo_lemma : forall m,
    fpr m (ftbd nil) -> m = ftbd nil.
Proof. destruct m as [m | m]; now induction m. Qed.

(* Lemma another_foo_lemma : forall m1 m2 e, *)
(*     fpr m1 m2 -> fpr (fcons e m1) (fcons e m2). *)
(* Proof. destruct m as [m1 | m1]; now induction m1. Qed. *)

Lemma same_ext : forall m1 m2 t,
    prefix m1 t -> prefix m2 t ->
    fpr m1 m2 \/ fpr m2 m1.
Proof.
  destruct m1 as [m1 | m1]; induction m1; intros [] [] H1 H2;
    try (now auto); destruct H1; destruct p; simpl in *;
      destruct H2; simpl in *; subst; try (now auto);
  try (specialize (IHm1 (fstop p) t H0 H2); simpl in IHm1;
  destruct IHm1; subst; 
    [now left | now right]);
  try (specialize (IHm1 (ftbd p) t H0 H2); simpl in IHm1;
  destruct IHm1; subst; 
  [now left | now right]).
Qed.

Lemma same_fpr : forall m1 m2 m,
    fpr m1 m -> fpr m2 m ->
    (fpr m1 m2 \/ fpr m2 m1).
Proof.
  destruct m1 as [p1 | p1]; destruct m2 as [p2 | p2]; destruct m as [p | p];
    try now auto.
  - generalize dependent p2. generalize dependent p.
    induction p1.
    + intros p p2 H1 H2. simpl in *; subst; now left.
    + intros p p2 H1 H2. simpl in *; subst; now left.
  - generalize dependent p2. generalize dependent p.
    induction p1.
    + intros p p2 H1 H2. simpl in *; subst; now right.
    + intros p p2 H1 H2. simpl in *; subst; now right.
  - generalize dependent p2. generalize dependent p.
    induction p1.
    + intros p p2 H1 H2. simpl in *; subst; now left.
    + intros p p2 H1 H2. simpl in *; subst; now left.
  - generalize dependent p2. generalize dependent p.
    induction p1.
    + intros p p2 H1 H2. simpl in *; subst; now left.
    + intros p p2 H1 H2. simpl in *; subst.
      destruct p as [| a' p'].
      ++ contradiction.
      ++ destruct H1; subst. destruct p2; auto.
         simpl in H2; destruct H2; subst. specialize (IHp1 p' p2 H0 H1).
         destruct IHp1; [now left | now right].
  - generalize dependent p2. generalize dependent p.
    induction p1.
    + intros p p2 H1 H2. simpl in *; subst; now left.
    + intros p p2 H1 H2. simpl in *; subst.
      destruct p as [| a' p'].
      ++ contradiction.
      ++ destruct H1; subst. destruct p2; auto.
         simpl in H2; destruct H2; subst. specialize (IHp1 p' p2 H0 H1).
         destruct IHp1; [now left | now right].
Qed.

Lemma non_comp_pref_diff_traces : forall t1 t2 m1 m2,
    prefix m1 t1 -> prefix m2 t2 ->
    ~ (fpr m1 m2 \/ fpr m2 m1) -> t1 <> t2.
Proof.
  intros t1 t2 m1 m2 H H0 H1 Hf.
  subst. apply H1. now apply (same_ext m1 m2 t2).
Qed.

Lemma no_prper_fpr_ftbd : forall m, m <> ftbd nil -> fpr m (ftbd nil) -> False.
Proof. destruct m as [m | m]; now induction m. Qed.

Lemma stop_sngle_continuation_fpr : forall m1 m2,
    fstopped m1 = true ->
    fpr m1 m2 ->
    m1 = m2.
Proof.
  destruct m1 as [m1 | m1]; destruct m2 as [m2 | m2];
    induction m1, m2; try now auto.
  intros H H0; simpl in *; subst. now rewrite H0.
Qed.

(**************************************************)

(** *snoc *)

(* CA: fsnoc is the identity on fstop *)

Fixpoint snoc {A : Type} (l : list A) (x : A) : list A :=
  match l with
  | nil => cons x nil
  | cons x' l' => cons x' (snoc l' x)
  end.

Definition fsnoc (m : finpref) (e : event) :=
  match m with
  | fstop m' => m
  | ftbd  m' => ftbd (snoc m' e)
  end.

Lemma stop_snoc_id : forall m e,
    fstopped m = true ->
    fsnoc m e = m.
Proof.
  induction m; try now auto.
Qed.

Lemma fpr_snoc_fpr : forall m1 m2 e,
    fpr m1 m2 ->
    fpr m1 (fsnoc m2 e).
Proof.
  destruct m1 as [m1 | m1]; induction m1; intros [] e H; try now auto;
  inversion H; subst.
  + simpl in *. destruct p. contradiction.
    destruct H as [H1 H2].
    specialize (IHm1 (ftbd p) e H2). now split.
Qed.

Lemma snoc_stop' : forall m e b, fstopped (fsnoc m e) = b ->
                            fstopped m = b.
Proof.
  intros m e b H. now destruct m.
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
  destruct m1 as [m1 | m1]; induction m1; destruct m as [m | m];
    induction m; intros e' H; try now auto.
  + inversion H. assert (fpr (ftbd m1) (ftbd nil)).
    { auto. }
    apply a_foo_lemma in H2.
    subst; simpl. inversion H2; now right.
  + simpl in *.
    destruct H. subst; simpl in *.
    specialize (IHm1 (ftbd m) e' H0). simpl in *. destruct IHm1.
    ++ now left.
    ++ right. inversion H. now subst.
Qed.

Lemma snoc_diff : forall m a b,
    fstopped m = false  ->
    fpr (fsnoc m a) (fsnoc m b) ->
    a = b.
Proof.
  intros [m|m] a b H H0. inversion H.
  clear H. simpl in *.
  eapply (compare_with_snoc (fsnoc (ftbd m) a) (ftbd m) b) in H0.
  destruct H0 as [H0 | H0]; auto.
  - induction m; inversion H0; auto; try now apply IHm.
  - induction m; inversion H0; auto.
    assert (H: fsnoc (ftbd m) a = fsnoc (ftbd m) b).
    { simpl. now rewrite H1. }
    now specialize (IHm H).
Qed.

Lemma no_snoc_fpr_ftb : forall m e, ~ fpr (fsnoc m e) (ftbd nil).
Proof. destruct m as [m | m]; now induction m. Qed.

Lemma fpr_snoc_ftbd : forall m e f,
    fstopped m = false ->
    fpr (fsnoc m e) (fsnoc (ftbd nil) f) ->
    m = ftbd nil.
Proof.
  intros [m|m] e f H H0. induction m; try now auto.
  + apply compare_with_snoc in H0. destruct H0.
    now apply no_snoc_fpr_ftb in H0.
    simpl in H0. inversion H0.
    destruct m; auto.
    simpl in *. clear H. inversion H2. subst.
    assert (H: ~ (snoc m e = nil)).
    { now induction m. }
    contradiction.
Qed.

Lemma same_snoc_same_finpref : forall m m0 e1 e2 i1 i2,
    i1 <> i2  -> e1 <> e2 ->
    fstopped m0 = false ->
    fstopped m = false ->
    fpr (fsnoc m0 i1) (fsnoc m e1) ->
    fpr (fsnoc m0 i2) (fsnoc m e2) ->
    m0 = m.
Proof.
  destruct m as [m | m]; induction m as [| e' m' IHm'];
  intros m0 e1 e2 i1 i2 H H0 H1 H2 H3 H4;
  try now auto; simpl in *.
  + now apply (fpr_snoc_ftbd m0 i1 e1).
  + destruct m0 as [m0 | m0].
    inversion H1.
    destruct m0 as [| e0 m0]; simpl in *. destruct H3, H4; subst; contradiction.
    destruct H3, H4; subst.
    specialize (IHm' (ftbd m0) e1 e2 i1 i2 H H0 H1 H2 H5 H6). now inversion IHm'.
Qed.

Lemma snoc_lemma : forall m,
    m = ftbd nil \/
    (exists m' e', m = fsnoc m' e').
Proof.
  intros [m | m]; induction m.
  - right. now exists (fstop nil), an_event.
  - destruct IHm as [H | H]; try now inversion H.
    right. destruct H as [m' [e' H]]. now exists (fstop (cons a m)), e'.
  - now left.
  - destruct IHm as [H | H]. 
    + inversion H; subst. right. now exists (ftbd nil), a.
    + destruct H as [m' [e' H]]. right.
      destruct m' as [m' | m'].
      now exists (ftbd (cons a m')), e'.
      inversion H. exists (ftbd (cons a m')), e'. now subst. 
Qed.

Lemma not_stop_not_snoc_pref : forall m e,
    fstopped m = false ->
    fpr (fsnoc m e) m -> False.
Proof.
  intros [m | m] e H H0; induction m; try now auto.
  simpl in *. destruct H0 as [Heq H0].
  now apply IHm.
Qed.

Lemma snoc_m_event_equal : forall m e1 e2,
    fstopped m = false ->
    fpr (fsnoc m e1) (fsnoc m e2) ->
    e1 = e2.
Proof.
  intros [m | m] e1 e2 Hstop Hfpr;
  induction m; inversion Hfpr; try now auto.
Qed.

Lemma same_snoc_same_pointwise : forall m1 m2 e1 e2,
    fstopped m1 = false ->
    fstopped m2 = false ->
    fsnoc m1 e1 = fsnoc m2 e2 ->
    m1 = m2 /\ e1 = e2.
Proof.
  destruct m1 as [m1 | m1]; induction m1; intros m2 e1 e2 Hstop1 Hstop2 Heq;
    try now auto.
  + destruct m2 as [m2 | m2]; destruct m2; inversion Heq; try now auto.
    simpl in *. 
    ++ now destruct m2. 
  + destruct m2 as [m2 | m2]; destruct m2; inversion Heq; try now auto.
    ++ exfalso. apply (no_snoc_fpr_ftb (ftbd m1) e1). simpl in *. now rewrite H1. 
    ++ destruct (IHm1 (ftbd m2) e1 e2); simpl in *; subst; try now auto.
       now rewrite H1. inversion H; now subst.
Qed.

(* TODO: TM#2 *)
Inductive diverges : trace -> Prop :=
| div_silent : diverges tsilent
| div_cons : forall e t, diverges t -> diverges (tcons e t).

(* Lemma proper_prefix : forall m t, *)
(*     prefix m t -> *)
(*     embedding m <> t -> *)
(*     fstopped m = false -> *)
(*     (exists e, prefix (fsnoc m e) t). *)
Lemma proper_prefix : forall m t,
    prefix m t ->
    embedding m <> t ->
    fstopped m = false ->
    ~ diverges t ->
    (exists e, prefix (fsnoc m e) t).
Proof.
  destruct m as [m | m]; induction m; intros t Hpref Hembed Hstop Hdiv; try now auto.
  + destruct t.
    * now auto.
    * now pose proof div_silent.
    * now exists e.
  + destruct t; try now auto.
    inversion Hpref. subst. destruct (IHm t) as [e' H]; try now auto.
    * intros ff. apply Hembed. simpl. pose proof embed_cons (ftbd m) t e.
      now specialize (H ff).
    * intros ff. now pose proof div_cons e t ff.
    * now exists e'.
Qed.

Lemma fpr_stop_equal : forall m1 m2,
    fpr m1 m2 ->
    fstopped m1 = true ->
    m1 = m2.
Proof.
  intros [m1 | m1]; induction m1; intros [m2 | m2] Hpref Hstop.
  + now destruct m2.
  + inversion Hpref.
  + destruct m2; try now auto.
    inversion Hpref. now subst.
  + destruct m2; try now auto.
  + inversion Hstop.
  + inversion Hstop.
  + destruct m2; now auto.
  + destruct m2; now auto.
Qed.


(**********************************************************************)

(** *m[fstop/ftbd] *)

Definition same_events_with_stop (m : finpref) : finpref :=
  match m with
  | ftbd m => fstop m
  | fstop m => fstop m
  end.

Notation "m [fstop/ftbd]" := (same_events_with_stop m)
                             (at level 50).

Lemma with_stop_fstopped : forall m,
    fstopped (m[fstop/ftbd]) = true.
Proof. now destruct m. Qed.

Lemma if_fstopped_equal : forall m,
    fstopped m = true ->
    m = m[fstop/ftbd].
Proof.
  now destruct m.
Qed.

Lemma embedding_is_the_same : forall m,
    embedding m =
    embedding (m[fstop/ftbd]).
Proof.
  now destruct m.
Qed.

Lemma m_fpr_with_stop : forall m,
    fpr m (m[fstop/ftbd]).
Proof. destruct m as [m | m]; now induction m. Qed.

Lemma with_stop_prefix_embedding :forall m,
    prefix (m [fstop/ftbd]) (embedding m).
Proof. destruct m as [m | m]; now induction m. Qed.

Lemma equal_with_stop_same_embedding : forall m mm,
    fstopped m = true ->
    fpr mm m ->
    fpr m (mm[fstop/ftbd]) ->
    embedding m = embedding mm.
Proof.
  destruct m as [m | m]; destruct m;
    intros mm Hstop Hfpr HfprStop; try now destruct mm.
  simpl in *. 
  destruct mm; try now auto; simpl in *. inversion Hfpr; subst. reflexivity.
  simpl in *; now subst.
  destruct mm as [mm | mm]; simpl in *; now subst.
Qed.

Lemma proper_fpr: forall m0 mm,
    fpr m0 (mm[fstop/ftbd]) ->
    fstopped m0 = false ->
    fpr m0 mm.
Proof. 
  destruct m0 as [m0 | m0]; induction m0; intros mm Hfpr Hstop; try now auto.
  simpl in Hstop. destruct mm; try now auto.
  now destruct mm as [mm | mm]. 
Qed.

(*******************************************************************************)

CoInductive t_eq : trace -> trace -> Prop :=
| estop : t_eq tstop tstop
| esilent : t_eq tsilent tsilent
| etrace : forall (e : event) t1 t2, t_eq t1 t2 -> t_eq (tcons e t1) (tcons e t2).

Lemma t_eq_symm : forall t1 t2, t_eq t1 t2 -> t_eq t2 t1.
Proof.
  cofix CH.
  intros t1 t2 Heq.
  inversion Heq; subst; constructor.
  now apply CH.
Qed.

Lemma prefix_preserved : forall m t1 t2, prefix m t1 -> t_eq t1 t2 -> prefix m t2.
Proof.
  intros [m | m]; induction m; intros t1 t2 hpref heq; try now auto.
  + now destruct t1, t2. 
  + destruct t1, t2; try now auto. inversion hpref. subst.   
    inversion heq. subst. simpl. split; try now auto.
    now apply (IHm t1 t2).
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
  - apply contra. intros H.
    rewrite <- dne.
    generalize dependent t2. generalize dependent t1.
    cofix Hfix.
    intros t1 t2 H.
    destruct t1 as [| | e1' t1']; destruct t2 as [| | e2' t2'].
    + constructor.
    + exfalso; apply H.
      exists (fstop nil). exists (ftbd nil).
      repeat split; try now auto.
    + exfalso; apply H.
      exists (fstop nil). exists (ftbd (cons e2' nil)).
      repeat split; try now auto.
    + exfalso; apply H.
      exists (ftbd nil). exists (fstop nil).
      repeat split; try now auto.
    + constructor.
    + exfalso; apply H.
      exists (ftbd nil). exists (ftbd (cons e2' nil)).
      repeat split; try now auto.
    + exfalso; apply H.
      exists (ftbd (cons e1' nil)). exists (fstop nil).
      repeat split; try now auto.
    + exfalso; apply H.
      exists (ftbd (cons e1' nil)). exists (ftbd nil).
      repeat split; try now auto.
    + destruct (classic (e1' = e2')).
      * subst. specialize (Hfix t1' t2').
        assert (H0: ~(exists m1 m2 : finpref, prefix m1 t1' /\ prefix m2 t2'
                                     /\ ~ (prefix m1 t2' /\ prefix m2 t1'))).
        { intros Hn.
          apply H. destruct Hn as [m1 [m2 [Hm1 [Hm2 Hn]]]].
          destruct m1, m2.
          - exists (fstop (cons e2' p)). exists (fstop (cons e2' p0)).
            repeat split; try now auto. intros Hn'.
            destruct Hn' as [Hn1 Hn2].
            inversion Hn1; inversion Hn2. now auto.
          - exists (fstop (cons e2' p)). exists (ftbd (cons e2' p0)).
            repeat split; try now auto. intros Hn'.
            destruct Hn' as [Hn1 Hn2].
            inversion Hn1; inversion Hn2. now auto.
          - exists (ftbd (cons e2' p)). exists (fstop (cons e2' p0)).
            repeat split; try now auto. intros Hn'.
            destruct Hn' as [Hn1 Hn2].
            inversion Hn1; inversion Hn2. now auto.
          - exists (ftbd (cons e2' p)). exists (ftbd (cons e2' p0)).
            repeat split; try now auto. intros Hn'.
            destruct Hn' as [Hn1 Hn2].
            inversion Hn1; inversion Hn2. now auto.
        }
        specialize (Hfix H0). constructor. assumption.
      * exfalso; apply H.
        exists (ftbd (cons e1' nil)). exists (ftbd (cons e2' nil)).
        repeat split; try now auto. simpl.
        intros Hn.
        inversion Hn. inversion H1. contradiction.
  - intros [m1 [m2 [h1 [h2 hn]]]] hf. apply hn. split.
    + now apply (same_finite_prefixes t1 t2).
    + apply t_eq_symm in hf. now apply (same_finite_prefixes t2 t1).
Qed.

(*******************************************************************************)

Axiom is_input : event -> Prop.

Definition traces_match (t1 t2 : trace) : Prop := 
 t1 = t2 \/
 (exists (m : finpref) (e1 e2 : event),
   is_input e1 /\ is_input e2 /\  e1 <> e2 /\
   fstopped m = false /\ prefix (fsnoc m e1) t1 /\ prefix (fsnoc m e2) t2).


(* Various lemmas about snoc, fsnoc, and fpr *)

Lemma destruct_pref : forall (m : pref), m = nil \/ exists (e : event) (m' : pref),  m = snoc m' e.
Proof.
  induction m.
  - now left.
  - right. destruct IHm.
    + subst. now exists a, nil.
    + destruct H as [e [m' H]]. subst.
      now exists e, (cons a m').
Qed.

Lemma snoc_length : forall (m' : pref) (e : event) (n : nat),
    Datatypes.length (snoc m' e) = S n -> Datatypes.length m' = n.
Proof.
  induction m'.
  - intros. simpl in H. inversion H. reflexivity.
  - intros e n Hlen. simpl in *. inversion Hlen.
    destruct n as [| m].
    + destruct m'; now auto.
    + specialize (IHm' e m H0). now subst.
Qed.

Definition length (m : finpref) :=
  match m with
  | fstop m => Datatypes.length m
  | ftbd  m => Datatypes.length m
  end.

Theorem finpref_ind_snoc :
  forall (P : finpref -> Prop),
    P (ftbd nil) ->
    (forall (m : pref), P (fstop m)) ->
    (forall (m : finpref) (e : event), P m -> P (fsnoc m e)) ->
    forall m, P m.
Proof.
  intros P Hnil Hstop Hind.
  assert (H: forall (n : nat) (m : finpref), length m = n -> P m).
  { induction n.
    - intros [m | m] Hlen; try now auto.
      destruct m; try now auto.
    - intros m Hlen.
      destruct m; try now auto.
      destruct (destruct_pref p).
      subst; simpl in *. inversion Hlen.
      destruct H as [e' [p' H']].
      subst; apply snoc_length in Hlen. specialize (IHn (ftbd p') Hlen).
      now specialize (Hind (ftbd p') e' (IHn)).
  }
  intros m. now apply (H (length m) m).
Qed.

Theorem pref_ind_snoc :
  forall (P : pref -> Prop),
    P nil ->
    (forall (p : pref) (e : event), P p -> P (snoc p e)) ->
    forall p, P p.
Proof.
  intros P Hnil Hind.
  assert (H: forall (n : nat) (p : pref), Datatypes.length p = n -> P p).
  { induction n.
    - intros p Hlen; try now auto.
      destruct p; try now auto.
    - intros p Hlen.
      destruct (destruct_pref p); try now auto.
      subst; assumption.
      destruct H as [e' [p' H']].
      subst; apply snoc_length in Hlen. specialize (IHn p' Hlen).
      now specialize (Hind p' e' IHn). }
  intros p. now apply (H (Datatypes.length p) p).
Qed.

Lemma snoc_injective : forall (e1 e2 : event) p1 p2,
  snoc p1 e1 = snoc p2 e2 -> e1 = e2 /\ p1 = p2.
Proof.
  intros e1 e2. induction p1.
  - intros p2 H; destruct p2; inversion H; try now auto.
    destruct p2; try now auto.
  - intros p2 H. simpl in *. destruct p2; try now auto.
    inversion H. subst. simpl in *. destruct p1; try now auto.
    simpl in *. inversion H.
    specialize (IHp1 p2 H2). destruct IHp1 as [Heq Heq'].
    split. assumption. now subst.
Qed.

Lemma destruct_fpr_ftbd_snoc : forall p' p e,
  fpr_ftbd p' (snoc p e) ->
  p' = snoc p e \/ fpr_ftbd p' p.
Proof.
  induction p' as [| e' p''].
  - intros p e H. simpl in *. tauto.
  - intros p e H. simpl in H.
    remember (snoc p e) as pe. destruct pe as [| e'' p''']. tauto.
    destruct H as [H1 H2]. subst e''.
    destruct (destruct_pref p''') as [| [e''' [p'''' H]]].
    + subst p'''. destruct p as [| e1 [| e2 ]]; simpl in Heqpe.
      * destruct p''. now left. simpl in H2; tauto.
      * now inversion Heqpe.
      * now inversion Heqpe.
    + subst p'''. destruct (IHp'' _ _ H2) as [IH | IH].
      * subst p''. left. reflexivity.
      * destruct p as [| e1 [| e2 ]]; simpl in Heqpe.
        ++ destruct p''''; simpl in *; now inversion Heqpe.
        ++ inversion Heqpe. destruct p''''; simpl in *.
           -- right. tauto.
           -- inversion H1. subst. destruct p''''; simpl in *; now inversion Heqpe.
        ++ inversion Heqpe. subst e1. right. simpl. split. reflexivity.
           replace (e2 :: snoc l e) with (snoc (e2 :: l) e) in H1 by reflexivity.
           apply snoc_injective in H1. destruct H1 as [H11 H12]. now subst.
Qed.


(* Axiom tapp : finpref -> trace -> trace. *) (* Where have all the flowers gone? *)

Fixpoint tapp' (p : pref) (t : trace) : trace :=
  match p with
  | nil => t
  | cons e p' => tcons e (tapp' p' t)
  end.

Definition tapp (m : finpref) (t : trace) : trace :=
  match m with
  | fstop p => embedding (fstop p) (* justification:  
                           we can't really add anything after a stopped trace. *)
  | ftbd  p => tapp' p t
  end.

Lemma tapp_pref : forall (m : finpref) (t : trace),
    prefix m (tapp m t).
Proof.
  induction finpref m as e p IHp; intros; try now auto;
    split; simpl in *; now auto.
Qed.

Lemma tapp_div_pref : forall (t : trace),
    diverges t -> exists (m : finpref), fstopped m = false /\ t = tapp m tsilent.
Proof.
  intros t Ht.
  induction Ht.
  - now (exists (ftbd nil)).
  - destruct IHHt as [m Hm].
    destruct m as [p | p].
    + now destruct Hm.
    + destruct Hm.
      exists ((ftbd (cons e p))).
      split; now subst.
Qed.

Lemma tapp_fin_pref : forall (t : trace),
    fin t -> exists (m : finpref), t = tapp m tstop.
Proof.
  intros t Ht.
  induction Ht.
  - now (exists (fstop nil)).
  - destruct IHHt as [m Hm].
    destruct m as [p | p].
    + exists (fstop (cons e p)). simpl in *. now subst.
    + exists (ftbd (cons e p)). simpl in *. now subst.
Qed.

Lemma pref_inf_ndiv_pref : forall (m : finpref) (t : trace),
  prefix m t -> inf t -> ~diverges t -> exists e, prefix (fsnoc m e) t.
Proof.
  induction finpref m as e p IHp; intros t H H0 H1; try now eauto.
  - destruct t; try now auto.
    + exfalso; apply H0. now constructor.
    + exfalso; apply H1. now constructor.
    + now (exists e).
  - destruct t; try now auto.
    simpl in *. destruct H; subst.
    specialize (IHp t H2 (inf_tcons e0 t H0)).
    assert (~ diverges (tcons e0 t) -> ~ diverges t).
    { clear.
      destruct t; try now auto.
      - intros H. exfalso. apply H. constructor. constructor.
      - intros H. intros H'. apply H. now constructor. }
    specialize (IHp (H H1)).
    destruct IHp as [e He]. now (exists e).
  Unshelve.
  exact an_event. exact an_event.  
Qed.