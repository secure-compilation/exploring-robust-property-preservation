Require Import List.

CoInductive stream {A : Type} :=
   scons (e : A) (s : stream) : stream.

Fixpoint list_stream_prefix {A : Type} (l : list A) (s : stream) :=
  match l, s with
  | nil, _ => True
  | cons a1 l1, scons a2 s2 => (a1 = a2) /\ (list_stream_prefix l1 s2)
  end.

Fixpoint list_list_prefix {A : Type} (l1 l2 : list A) :=
  match l1, l2 with
  | nil, _ => True
  | cons a1 l1, cons a2 l2 => (a1 = a2) /\ list_list_prefix l1 l2
  | _, _ => False
  end.

Lemma list_list_prefix_ref {A : Type} (l : list A) : list_list_prefix l l.
Proof. now induction l. Qed.

Lemma list_list_prefix_asym {A : Type} : forall (l1 l2 : list A),
    list_list_prefix l1 l2 -> list_list_prefix l2 l1 -> l1 = l2.
Proof.
  induction l1, l2; try now auto.
  simpl. intros [afoo Hpref] [afoo' Hpref']; subst; now rewrite (IHl1 l2).
Qed.

Lemma list_list_prefix_trans {A : Type} : forall l1 l2 l3 : list A,
  list_list_prefix l1 l2 -> list_list_prefix l2 l3 -> list_list_prefix l1 l3.
Proof.
  induction l1; try now auto.
  intros [] [] H1 H2; inversion H1; inversion H2; subst.
  simpl. firstorder.
Qed.

Lemma list_stream_prefix_trans {A : Type} : forall (l1 l2 : list A) (s : stream),
    list_list_prefix l1 l2 -> list_stream_prefix l2 s ->
    list_stream_prefix l1 s.
Proof.
  induction l1; auto.
  + intros [] [] Hpref1 Hpref2; inversion Hpref1; inversion Hpref2; subst.
    simpl. split; auto; now apply (IHl1 l s).
Qed.

Fixpoint app_list_stream {A : Type} (l : list A) (s : stream) :=
  match l with
  | nil => s
  | e :: l => scons e (app_list_stream l s)
  end.

Lemma app_list_stream_app {A : Type} (l1 l2 : list A) (s : stream) :
  app_list_stream (l1 ++ l2) s = app_list_stream l1 (app_list_stream l2 s).
Proof.
  induction l1.
  - eauto.
  - simpl; now rewrite IHl1.
Qed.

Lemma list_stream_prefix_app {A : Type} :
  forall (l' : list A) l s0, list_stream_prefix l s0 -> list_stream_prefix (l' ++ l) (app_list_stream l' s0).
Proof.
  intros l'.
  induction l'.
  - eauto.
  - intros l s0 H.
    simpl. split; eauto using IHl'.
Qed.

Lemma list_list_prefix_stream_app {A : Type} :
  forall (l' l : list A) s0, list_list_prefix l' l -> list_stream_prefix l' (app_list_stream l s0).
Proof.
  induction l'.
  - eauto.
  - destruct l. intros s0 H. inversion H.
    intros s0 H. simpl in *. destruct H; subst; split; eauto using IHl'.
Qed.

Lemma list_list_prefix_app {A : Type} : forall (l : list A) l' l'',
    list_list_prefix l' l'' -> list_list_prefix (l ++ l') (l ++ l'').
Proof.
  induction l.
  eauto.
  intros l' l'' H. split; eauto.
Qed.

CoInductive stream_eq {A : Type} : stream -> stream -> Prop :=
| stream_eq_scons : forall (e : A) s1 s2, stream_eq s1 s2 -> stream_eq (scons e s1) (scons e s2).

Lemma stream_eq_refl : forall {A : Type} (s : @stream A), stream_eq s s.
Proof.
  cofix Hfix.
  intros A s.
  destruct s.
  constructor.
  apply Hfix.
Qed.
Hint Resolve stream_eq_refl.

Lemma stream_eq_trans : forall {A : Type} (s1 s2 s3 : @stream A), stream_eq s1 s2 -> stream_eq s2 s3 -> stream_eq s1 s3.
Proof.
  cofix Hfix.
  intros A s1 s2 s3 H H0.
  destruct s1, s2, s3.
  inversion H; inversion H0; subst.
  econstructor.
  eapply Hfix. eauto. eauto.
Qed.

Lemma stream_eq_sym : forall {A : Type} (s1 s2 : @stream A), stream_eq s1 s2 -> stream_eq s2 s1.
Proof.
  cofix Hfix.
  intros A s1 s2 H.
  inversion H; subst.
  econstructor; eauto.
Qed.
