(** A library of relation operators defining sequences of transitions
  and useful properties about them. *)

Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Import Stream.
Import ListNotations.

Section Sequences_Traces.
Variable A E: Type.                 (**r the type of states *)
Variable R: A -> list E -> A -> Prop.       (**r the transition relation, from one state to the next *)

(** ** Finite sequences of transitions *)

(** Zero, one or several transitions: reflexive, transitive closure of [R]. *)

Inductive star_tr: A -> list E -> A -> Prop :=
  | star_tr_refl: forall a,
      star_tr a nil a
  | star_tr_step : forall a b c l1 l2,
      R a l1 b -> star_tr b l2 c -> star_tr a (l1 ++ l2) c
.

Lemma star_tr_one:
  forall (a b: A) l, R a l b -> star_tr a l b.
Proof.
  intros a b l H.
  replace l with (l ++ []); try now rewrite app_nil_r.
  apply star_tr_step with (b := b);
    eauto using star_tr.
Qed.

Lemma star_tr_trans:
  forall (a b: A) (lab : list E), star_tr a lab b ->
              forall c (lbc : list E), star_tr b lbc c -> star_tr a (lab ++ lbc) c.
Proof.
  intros a b lab Hab.
  induction Hab; intros.
  assumption.
  rewrite <- app_assoc.
  eapply star_tr_step. eassumption.
  apply IHHab. eassumption.
Qed.

(** One or several transitions: transitive closure of [R]. *)

Inductive plus_tr: A -> list E -> A -> Prop :=
| plus_tr_left : forall a b c l l',
    R a l b -> star_tr b l' c -> plus_tr a (l ++ l') c.

Lemma plus_tr_one:
  forall a b l, R a l b -> plus_tr a l b.
Proof.
  intros a b l H.
  replace l with (l ++ []);
    eauto using star_tr, plus_tr.
  now rewrite app_nil_r.
Qed.

Lemma plus_tr_star_tr:
  forall a b l,
  plus_tr a l b -> star_tr a l b.
Proof.
  intros. inversion H; eauto using star_tr.
Qed.

Lemma plus_tr_star_tr_trans:
  forall a b c lab lbc, plus_tr a lab b -> star_tr b lbc c ->
                   plus_tr a (lab ++ lbc) c.
Proof.
  intros. inversion H; subst; eauto using plus_tr, star_tr_trans.
  rewrite <- app_assoc.
  eapply plus_tr_left. eassumption.
  eapply star_tr_trans; eauto.
Qed.

Lemma star_tr_plus_tr_trans:
  forall a b c lab lbc, star_tr a lab b -> plus_tr b lbc c ->
                   plus_tr a (lab ++ lbc) c.
Proof.
  intros.
  inversion H0; inversion H; subst;
    eauto using plus_tr_left, plus_tr, star_tr, star_tr_trans.
  rewrite <- app_assoc.
  eapply plus_tr_left; eauto using star_tr, star_tr_trans.
Qed.

Lemma plus_tr_right:
  forall a b c l l', star_tr a l b -> R b l' c -> plus_tr a (l ++ l') c.
Proof.
  intros a b c l  l' H H0.
  eapply star_tr_plus_tr_trans. eauto. apply plus_tr_one; eauto.
Qed.

(** ** Infinite sequences of transitions *)

Variable measure: A -> nat.                  (**r the anti-stuttering measure *)

CoInductive infseq_tr: @stream E -> A -> Prop :=
  | infseq_tr_step: forall a s b l,
      R a l b -> infseq_tr s b -> infseq_tr (Stream.app_list_stream l s) a.

(* CF CompCert smallstep file *)
CoInductive infseq_tr_N : @stream E -> nat -> A -> Prop :=
| infseq_tr_N_star : forall a b n1 n2 l s,
    n2 < n1 ->
    star_tr a l b ->
    infseq_tr_N s n2 b ->
    infseq_tr_N (Stream.app_list_stream l s) n1 a
| infseq_tr_N_plus : forall a b n1 n2 l s,
    plus_tr a l b ->
    infseq_tr_N s n2 b ->
    infseq_tr_N (Stream.app_list_stream l s) n1 a.

Lemma infseq_tr_N_inv : forall n s a,
    infseq_tr_N s n a ->
    exists l, exists s', exists n', exists a',
        R a l a' /\ infseq_tr_N s' n' a' /\ Stream.app_list_stream l s' = s.
Proof.
  intros n. pattern n.
  eapply well_founded_ind with (R := lt).
  apply PeanoNat.Nat.lt_wf_0.
  intros x H s a H0.
  inversion H0; subst; clear H0.
  - inversion H2; subst; clear H2.
    + apply H with n2. now apply H1.
      apply H3.
    + exists l1. exists (app_list_stream l2 s0). exists x. exists b0.
      repeat split; eauto.
      eapply infseq_tr_N_star; eauto.
      clear.
      induction l1; eauto.
      simpl; now rewrite IHl1.
  - inversion H1; subst; clear H1.
    exists l0, (app_list_stream l' s0), n2, b0.
    repeat split; eauto.
    inversion H3; subst; clear H3.
    assumption.
    eapply infseq_tr_N_plus; eauto.
    econstructor; eauto.
    clear.
    induction l0; eauto.
    simpl; now rewrite IHl0.
Qed.

Lemma infseq_tr_N_infseq_tr :
  forall a s n, infseq_tr_N s n a -> infseq_tr s a.
Proof.
  cofix Hfix.
  intros a s n H.
  destruct (infseq_tr_N_inv H) as [l [s' [n' [a' [HR [Hinf Heq]]]]]].
  subst.
  apply infseq_tr_step with (b := a').
  eauto.
  eapply Hfix; eauto.
Qed.


(* Infinitely many silent steps *)
CoInductive infseq_silent: A -> Prop :=
  | infseq_silent_step: forall a b,
      R a [] b -> infseq_silent b -> infseq_silent a.

(* CF CompCert smallstep file *)
CoInductive infseq_silent_N : nat -> A -> Prop :=
| infseq_silent_N_star : forall a b n1 n2 ,
    n2 < n1 ->
    star_tr a [] b ->
    infseq_silent_N n2 b ->
    infseq_silent_N n1 a
| infseq_silent_N_plus : forall a b n1 n2,
    plus_tr a [] b ->
    infseq_silent_N n2 b ->
    infseq_silent_N n1 a.

Lemma infseq_silent_N_inv : forall n a,
    infseq_silent_N n a ->
    exists n', exists a',
        R a [] a' /\ infseq_silent_N n' a'. 
Proof.
  intros n. pattern n.
  eapply well_founded_ind with (R := lt).
  apply PeanoNat.Nat.lt_wf_0.
  intros x H a H0.
  inversion H0; subst; clear H0.
  - inversion H2; subst; clear H2.
    + apply H with n2. now apply H1.
      apply H3.
    + exists x. exists b0.
      assert (Heq: l1 = [] /\ l2 = []) by now apply app_eq_nil.
      destruct Heq; subst.
      split; auto.
      eapply infseq_silent_N_star; eauto.
  - inversion H1; subst; clear H1.
    exists n2, b0.
    assert (Heq: l = [] /\ l' = []) by now apply app_eq_nil.
    destruct Heq; subst.
    split; auto.
    inversion H5; subst; clear H5.
    assumption.
    eapply infseq_silent_N_plus; eauto.
    rewrite <- H1.
    econstructor; eauto.
Qed.

Lemma infseq_silent_N_infseq_silent :
  forall a n, infseq_silent_N n a -> infseq_silent a.
Proof.
  cofix Hfix.
  intros a n H.
  destruct (infseq_silent_N_inv H) as [n' [a' [Hr Hinf]]].
  apply infseq_silent_step with (b := a').
  eauto.
  eapply Hfix; eauto.
Qed.


Definition irred_tr (a: A) : Prop := forall b e, ~(R a e b).

(** ** Determinism properties for functional transition relations. *)

(** A transition relation is functional if every state can transition to at most
  one other state. *)

Hypothesis R_functional:
  forall a b c l1 l2, R a l1 b -> R a l2 c -> b = c /\ l1 = l2.

(** Uniqueness of finite transition sequences. *)

Lemma star_tr_star_tr_inv:
  forall a b l1, star_tr a l1 b ->
            forall c l2, star_tr a l2 c ->
                    (exists l3, l1 = l2 ++ l3 /\ star_tr c l3 b) \/
                    (exists l3, l2 = l1 ++ l3 /\ star_tr b l3 c).
Proof.
  induction 1; intros.
  - right; now eexists.
  - inversion H1; subst.
    + left. eexists; split; eauto using star_tr.
      now rewrite app_nil_l.
    + assert (b = b0) by (eapply R_functional; eauto).
      assert (He: l1 = l3) by (eapply R_functional; eauto).
      subst b0 l3.
      edestruct (IHstar_tr c0) as [[l3 [IH1 IH2]] | [l3 [IH1 IH2]]]. eauto.
      * subst.
        left.
        eexists; split; eauto using star_tr.
        now rewrite app_assoc.
      * subst.
        right.
        eexists; split; eauto using star_tr.
        now rewrite app_assoc.
Qed.

Lemma finseq_tr_unique:
  forall a b b' l l',
  star_tr a l b -> irred_tr b ->
  star_tr a l' b' -> irred_tr b' ->
  b = b' /\ l = l'.
Proof.
  intros.
  destruct (star_tr_star_tr_inv H H1) as [[l'' [H3 H4]] | [l'' [H3 H4]]].
  - inversion H4; split; subst; auto; try elim (H2 _ _ H5).
    apply app_nil_r.
  - inversion H4; split; subst; auto; try elim (H0 _ _ H5).
    now rewrite app_nil_r.
Qed.

(** A state cannot both diverge and terminate on an irreducible state. *)

(* Lemma infseq_tr_star_tr_inv: *)
(*   forall a b l s, star_tr a l b -> infseq_tr s a -> infseq_tr (l++s) b. *)
(* Proof. *)
(*   induction 1; intros. *)
(* - auto. *)
(* - inversion H1; subst. *)
(*   assert (b = b0) by (eapply R_functional; eauto). subst b0. *)
(*   apply IHstar_tr; auto. *)
(* Qed. *)

Lemma infseq_tr_finseq_excl:
  forall a b l s,
  star_tr a l b -> irred_tr b -> infseq_tr s a -> False.
Proof.
  intros.
  assert (exists s', infseq_tr s' b).
  { generalize dependent s.
    induction H; intros.
    - inversion H1; subst; elim (H0 _ _ H).
    - inversion H2; subst.
      + assert (b = b0) by (eapply R_functional; eauto).
        subst b0.
        eapply IHstar_tr; eassumption.
  }
  destruct H2 as [s' Hs'].
  inversion Hs'; subst; elim (H0 _ _ H2).
Qed.

(** If there exists an infinite sequence of transitions from [a],
  all sequences of transitions arising from [a] are infinite. *)

(* Lemma infseq_tr_all_seq_inf: *)
(*   forall a, infseq_tr a -> all_seq_inf a. *)
(* Proof. *)
(*   intros. unfold all_seq_inf. intros.  *)
(*   assert (infseq_tr b) by (eapply infseq_star_tr_inv; eauto).  *)
(*   inversion H1. subst. exists b0; auto. *)
(* Qed. *)

Lemma star_tr_infseq_tr :
  forall a b s l,
    star_tr a l b -> infseq_tr s b ->
    infseq_tr (Stream.app_list_stream l s) a.
Proof.
  intros until l.
  intros H.
  induction H; subst.
  - intros H1; eauto.
  - intros H1.
    replace (app_list_stream (l1 ++ l2) s) with
        (app_list_stream l1 (app_list_stream l2 s)).
    econstructor; eauto.
    clear.
    induction l1. reflexivity.
    simpl.
    rewrite <- IHl1.
    reflexivity.
Defined.

Lemma plus_tr_infseq_tr :
  forall a b s l,
    plus_tr a l b -> infseq_tr s b ->
    infseq_tr (Stream.app_list_stream l s) a.
Proof.
  intros until l.
  intros H.
  inversion H; subst.
  eapply star_tr_infseq_tr.
  econstructor; eauto.
Defined.

End Sequences_Traces.
