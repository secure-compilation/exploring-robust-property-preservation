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
  
  Inductive star : A -> list E -> A -> Prop :=
  | star_refl: forall a,
      star a nil a
  | star_step : forall a b c l1 l2,
      R a l1 b -> star b l2 c -> star a (l1 ++ l2) c
  .

  Lemma star_one:
    forall (a b: A) l, R a l b -> star a l b.
  Proof.
    intros a b l H.
    replace l with (l ++ []); try now rewrite app_nil_r.
    apply star_step with (b := b);
      eauto using star.
  Qed.

  Lemma starans:
    forall (a b: A) (lab : list E), star a lab b ->
                               forall c (lbc : list E), star b lbc c -> star a (lab ++ lbc) c.
  Proof.
    intros a b lab Hab.
    induction Hab; intros.
    assumption.
    rewrite <- app_assoc.
    eapply star_step. eassumption.
    apply IHHab. eassumption.
  Qed.

  (** One or several transitions: transitive closure of [R]. *)

  Inductive plus: A -> list E -> A -> Prop :=
  | plus_left : forall a b c l l',
      R a l b -> star b l' c -> plus a (l ++ l') c.

  Lemma plus_one:
    forall a b l, R a l b -> plus a l b.
  Proof.
    intros a b l H.
    replace l with (l ++ []);
      eauto using star, plus.
    now rewrite app_nil_r.
  Qed.

  Lemma plus_star:
    forall a b l,
      plus a l b -> star a l b.
  Proof.
    intros. inversion H; eauto using star.
  Qed.

  Lemma plus_starans:
    forall a b c lab lbc, plus a lab b -> star b lbc c ->
                     plus a (lab ++ lbc) c.
  Proof.
    intros. inversion H; subst; eauto using plus, starans.
    rewrite <- app_assoc.
    eapply plus_left. eassumption.
    eapply starans; eauto.
  Qed.

  Lemma star_plusans:
    forall a b c lab lbc, star a lab b -> plus b lbc c ->
                     plus a (lab ++ lbc) c.
  Proof.
    intros.
    inversion H0; inversion H; subst;
      eauto using plus_left, plus, star, starans.
    rewrite <- app_assoc.
    eapply plus_left; eauto using star, starans.
  Qed.

  Lemma plus_right:
    forall a b c l l', star a l b -> R b l' c -> plus a (l ++ l') c.
  Proof.
    intros a b c l  l' H H0.
    eapply star_plusans. eauto. apply plus_one; eauto.
  Qed.

  (** ** Infinite sequences of transitions *)

  Variable measure: A -> nat.                  (**r the anti-stuttering measure *)

  (* Infinite execution: either produces the whole stream, or a prefix and then
     silent divergence *)
  CoInductive infseq: @stream E -> A -> Prop :=
  | infseq_step: forall a s b l,
      R a l b -> infseq s b -> infseq (Stream.app_list_stream l s) a.

  (* CF CompCert smallstep file *)
  CoInductive infseq_N : @stream E -> nat -> A -> Prop :=
  | infseq_N_star : forall a b n1 n2 l s,
      n2 < n1 ->
      star a l b ->
      infseq_N s n2 b ->
      infseq_N (Stream.app_list_stream l s) n1 a
  | infseq_N_plus : forall a b n1 n2 l s,
      plus a l b ->
      infseq_N s n2 b ->
      infseq_N (Stream.app_list_stream l s) n1 a.

  Lemma infseq_N_inv : forall n s a,
      infseq_N s n a ->
      exists l, exists s', exists n', exists a',
              R a l a' /\ infseq_N s' n' a' /\ Stream.app_list_stream l s' = s.
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
        eapply infseq_N_star; eauto.
        clear.
        induction l1; eauto.
        simpl; now rewrite IHl1.
    - inversion H1; subst; clear H1.
      exists l0, (app_list_stream l' s0), n2, b0.
      repeat split; eauto.
      inversion H3; subst; clear H3.
      assumption.
      eapply infseq_N_plus; eauto.
      econstructor; eauto.
      clear.
      induction l0; eauto.
      simpl; now rewrite IHl0.
  Qed.

  Lemma infseq_N_infseq :
    forall a s n, infseq_N s n a -> infseq s a.
  Proof.
    cofix Hfix.
    intros a s n H.
    destruct (infseq_N_inv H) as [l [s' [n' [a' [HR [Hinf Heq]]]]]].
    subst.
    apply infseq_step with (b := a').
    eauto.
    eapply Hfix; eauto.
  Qed.

  Lemma infseq_infseq_N :
    forall a n s, infseq s a -> infseq_N s n a.
  Proof.
    cofix Hfix.
    intros a n s H.
    inversion H; subst.
    eapply infseq_N_plus with (n2 := 0).
    replace l with (l ++ []) by now rewrite app_nil_r.
    econstructor. eauto. econstructor.
    eapply Hfix. eauto.
  Qed.

  (* Now, we can start defining interesting notions of infseq.
     [infseq_prod s a] means that [a] actually produces the stream [s]*)
  CoInductive infseq_prod : @stream E -> A -> Prop :=
  | infseq_prod_star: forall a b l s,
      star a l b ->
      l <> [] ->
      infseq_prod s b ->
      infseq_prod (app_list_stream l s) a
  .

  Lemma star_infseq_prod : forall a b l s,
      star a l b ->
      infseq_prod s b ->
      infseq_prod (app_list_stream l s) a.
  Proof.
    intros a b l s H H0.
    inversion H0; subst.
    assert (star a (l ++ l0) b0) by now eapply starans; eauto.
    replace (app_list_stream l (app_list_stream l0 s0)) with (app_list_stream (l ++ l0) s0).
    econstructor; eauto.
    now destruct l, l0.
    clear.
    induction l; auto.
    now simpl; rewrite IHl.
  Qed.

  Lemma star_inv : forall a l b,
      star a l b ->
      (a = b /\ l = []) \/ plus a l b.
  Proof.
    intros a l b H.
    inversion H; subst; clear H.
    - left; auto.
    - right; econstructor; eauto.
  Qed.

  Lemma star_infseq : forall a l b s,
      star a l b ->
      infseq s b ->
      infseq (app_list_stream l s) a.
  Proof.
    intros a l b s H H0.
    induction H.
    - eauto.
    - rewrite app_list_stream_app.
      now econstructor; eauto.
  Qed.

  Lemma infseq_prod_infseq : forall s a,
      infseq_prod s a ->
      infseq s a.
  Proof.
    assert (forall s a n, infseq_prod s a -> infseq_N s n a).
    {
      cofix Hfix.
      intros s a n H.
      inversion H; subst.
      destruct l as [| e l]; try congruence.
      replace (app_list_stream (e :: l) s0) with (app_list_stream ([e] ++ l) s0) in H by reflexivity.
      destruct (star_inv H0) as [[] |]; try congruence.
      inversion H3; subst; clear H3.
      rewrite app_list_stream_app.
      eapply infseq_N_plus.
      - eapply plus_one. eauto.
      - eapply Hfix.
        replace ([e] ++ l) with (e :: l) in H by reflexivity.
        rewrite <- H4 in H.
        eapply star_infseq_prod.
        eauto. eauto.
    }
    intros s a H0.
    eapply infseq_N_infseq.
    eapply H.
    eassumption.
    Unshelve.
    all: exact 0.
  Qed.

  (* Infinitely many silent steps *)
  CoInductive infseq_silent: A -> Prop :=
  | infseq_silent_step: forall a b,
      R a [] b -> infseq_silent b -> infseq_silent a.

  (* CF CompCert smallstep file *)
  CoInductive infseq_silent_N : nat -> A -> Prop :=
  | infseq_silent_N_star : forall a b n1 n2 ,
      n2 < n1 ->
      star a [] b ->
      infseq_silent_N n2 b ->
      infseq_silent_N n1 a
  | infseq_silent_N_plus : forall a b n1 n2,
      plus a [] b ->
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

  Lemma infseq_silent_infseq_silent_N :
    forall a n, infseq_silent a -> infseq_silent_N n a.
  Proof.
    cofix Hfix.
    intros a n H.
    inversion H; subst.
    eapply infseq_silent_N_plus with (n2 := 0).
    replace [] with ([] ++ [] : list E) by reflexivity.
    econstructor; eauto; eapply star_refl.
    now eapply Hfix.
  Qed.

  Lemma infseq_silent_infseq :
    forall a s, infseq_silent a -> infseq s a.
  Proof.
    cofix Hfix.
    intros a s H.
    inversion H; subst; clear H.
    replace s with (app_list_stream [] s) by reflexivity.
    econstructor; eauto.
  Qed.

  Lemma infseq_infseq_silent :
    forall P s a, (infseq s a -> P a) ->
             (infseq_silent a -> P a).
  Proof.
    intros P s a X H.
    apply X. now apply infseq_silent_infseq.
  Qed.


  Lemma diverges_infseq_silent:
    forall s0,
      (forall s1 t1, star s0 t1 s1 -> exists s2, R s1 [] s2) ->
      infseq_silent s0.
  Proof.
    cofix Hfix; intros.
    destruct (H s0 []) as [s1 H']. constructor.
    econstructor; try eassumption.
    apply Hfix.
    intros s2 t1 H0.
    eapply H. eapply star_step; eauto.
  Qed.

  Definition irred (a: A) : Prop := forall b e, ~(R a e b).

  (* Inductive behavior := *)
  (* | Reactive : @stream E -> behavior *)
  (* | Diverges : list E -> behavior *)
  (* | Terminates : list E -> behavior *)
  (* . *)

  (** ** Determinism properties for functional transition relations. *)

  (** A transition relation is functional if every state can transition to at most
  one other state. *)

  Hypothesis R_functional:
    forall a b c l1 l2, R a l1 b -> R a l2 c -> b = c /\ l1 = l2.

  Lemma star_infseq_prod_inv : forall a l b,
      star a l b ->
      forall s, infseq_prod s a ->
           exists s', infseq_prod s' b /\ s = app_list_stream l s'.
  Proof.
    induction 1; intros.
    - eexists; eauto.
    - inversion H1; subst; clear H1.
      inversion H2; subst; clear H2.
      congruence.
      assert (b1 = b /\ l0 = l1) as [? ?]
          by (now eapply R_functional; eassumption); subst.
      specialize (IHstar (app_list_stream l3 s0)).
      destruct IHstar as [s' [? ?]].
      eapply star_infseq_prod; eauto.
      exists s'. split; eauto.
      clear -H6.
      induction l1. simpl. rewrite H6. reflexivity.
      simpl. rewrite IHl1. reflexivity.
  Qed.


  Lemma infseq_prod_inv : forall a l1 b,
      star a l1 b ->
      forall c l2 s1 s2,
        star a l2 c ->
        l1 <> [] -> l2 <> [] ->
        infseq_prod s1 b ->
        infseq_prod s2 c ->
        exists a', exists l, exists s1', exists s2',
                l <> [] /\
                infseq_prod s1' a' /\ infseq_prod s2' a' /\
                app_list_stream l1 s1 = app_list_stream l s1' /\
                app_list_stream l2 s2 = app_list_stream l s2'.
  Proof.
    induction 1; intros.
    congruence.
    inversion H1; subst; clear H1. congruence.
    assert (b = b0 /\ l1 = l3) as [? ?] by (eapply R_functional; eassumption); subst.
    destruct l3.
    - simpl in *. eapply IHstar; eauto.
    - exists b0. exists (e :: l3). exists (app_list_stream l2 s1). exists (app_list_stream l4 s2).
      repeat split.
      congruence.
      eapply star_infseq_prod; eauto.
      eapply star_infseq_prod; eauto.
      eapply app_list_stream_app. eapply app_list_stream_app.
  Qed.


  (** Uniqueness of finite transition sequences. *)

  Lemma star_star_inv:
    forall a b l1, star a l1 b ->
              forall c l2, star a l2 c ->
                      (exists l3, l1 = l2 ++ l3 /\ star c l3 b) \/
                      (exists l3, l2 = l1 ++ l3 /\ star b l3 c).
  Proof.
    induction 1; intros.
    - right; now eexists.
    - inversion H1; subst.
      + left. eexists; split; eauto using star.
        now rewrite app_nil_l.
      + assert (b = b0) by (eapply R_functional; eauto).
        assert (He: l1 = l3) by (eapply R_functional; eauto).
        subst b0 l3.
        edestruct (IHstar c0) as [[l3 [IH1 IH2]] | [l3 [IH1 IH2]]]. eauto.
        * subst.
          left.
          eexists; split; eauto using star.
          now rewrite app_assoc.
        * subst.
          right.
          eexists; split; eauto using star.
          now rewrite app_assoc.
  Qed.

  Lemma finseq_unique:
    forall a b b' l l',
      star a l b -> irred b ->
      star a l' b' -> irred b' ->
      b = b' /\ l = l'.
  Proof.
    intros.
    destruct (star_star_inv H H1) as [[l'' [H3 H4]] | [l'' [H3 H4]]].
    - inversion H4; split; subst; auto; try elim (H2 _ _ H5).
      apply app_nil_r.
    - inversion H4; split; subst; auto; try elim (H0 _ _ H5).
      now rewrite app_nil_r.
  Qed.

  Lemma infseq_silent_star_inv : forall a b l,
    star a l b ->
    infseq_silent a ->
    l = [] /\ infseq_silent b.
  Proof.
    intros a b l H.
    induction H.
    - auto.
    - intros H1.
      inversion H1; subst; clear H1.
      destruct (R_functional H H2); subst; eauto.
  Qed.
   


  (** A state cannot both diverge and terminate on an irreducible state. *)

  (* Lemma infseq_star_inv: *)
  (*   forall a b l s, star a l b -> infseq s a -> infseq (l++s) b. *)
  (* Proof. *)
  (*   induction 1; intros. *)
  (* - auto. *)
  (* - inversion H1; subst. *)
  (*   assert (b = b0) by (eapply R_functional; eauto). subst b0. *)
  (*   apply IHstar; auto. *)
  (* Qed. *)

  Lemma infseq_finseq_excl:
    forall a b l s,
      star a l b -> irred b -> infseq s a -> False.
  Proof.
    intros.
    assert (exists s', infseq s' b).
    { generalize dependent s.
      induction H; intros.
      - inversion H1; subst; elim (H0 _ _ H).
      - inversion H2; subst.
        + assert (b = b0) by (eapply R_functional; eauto).
          subst b0.
          eapply IHstar; eassumption.
    }
    destruct H2 as [s' Hs'].
    inversion Hs'; subst; elim (H0 _ _ H2).
  Qed.

  Lemma infseq_silent_irred_excl:
    forall a,
      irred a -> infseq_silent a -> False.
  Proof.
    intros a H H0.
    unfold irred in *.
    destruct H0.
    now apply (H b []).
  Qed.

  Lemma infseq_silent_finseq_excl:
    forall a b c l l',
      star a l b ->
      star a l' c ->
      infseq_silent b ->
      irred c ->
      False.
  Proof.
    intros a b c l l' H H0 H1 H2.
    destruct (star_star_inv H H0) as [[l'' [H3 H4]] | [l'' [H3 H4]]].
    - inversion H4; subst.
      + now eapply infseq_silent_irred_excl.
      + unfold irred in H2.
        eapply H2; eassumption.
    - induction H4; subst.
      + now eapply infseq_silent_irred_excl.
      + inversion H1; subst.
        assert (b = b0 /\ l1 = []) as [? ?] by (eapply R_functional; eauto); subst.
        simpl in *.
        apply IHstar; eauto.
        replace l with (l ++ []) by now apply app_nil_r.
        eapply starans. eauto.
        replace [] with ([] ++ [] : list E) by reflexivity.
        econstructor; eauto. constructor.
  Qed.

  (** If there exists an infinite sequence of transitions from [a],
  all sequences of transitions arising from [a] are infinite. *)

  (* Lemma infseq_all_seq_inf: *)
  (*   forall a, infseq a -> all_seq_inf a. *)
  (* Proof. *)
  (*   intros. unfold all_seq_inf. intros.  *)
  (*   assert (infseq b) by (eapply infseq_star_inv; eauto).  *)
  (*   inversion H1. subst. exists b0; auto. *)
  (* Qed. *)

  Lemma plus_infseq :
    forall a b s l,
      plus a l b -> infseq s b ->
      infseq (Stream.app_list_stream l s) a.
  Proof.
    intros until l.
    intros H.
    inversion H; subst.
    eapply star_infseq.
    econstructor; eauto.
  Defined.

  (** Alternative view of streams *)
  CoInductive stream' :=
  | scons' : forall (l : list E) (s : stream'), l <> [] -> stream'.

  Program Definition split_traceinf' (l : list E) (s: stream') (NE: l <> []): E * stream' :=
    match l with
    | nil => _
    | e :: nil => (e, s)
    | e :: t' => (e, @scons' t' s _)
    end.
  Next Obligation.
    destruct t'; congruence.
  Qed.

  CoFixpoint stream_of_stream' (s': stream') : stream :=
    match s' with
    | @scons' t T'' NOTEMPTY =>
      let (e, tl) := @split_traceinf' t T'' NOTEMPTY in
      scons e (stream_of_stream' tl)
    end.

  Remark unroll_stream':
    forall T, T = match T with @scons' t T' NE => @scons' t T' NE end.
  Proof.
    intros. destruct T; auto.
  Qed.

  Remark unroll_stream:
    forall (T : @stream E), T = match T with scons t T' => scons t T' end.
  Proof.
    intros. destruct T; auto.
  Qed.

  Lemma stream_stream'_app:
    forall t T NE,
      stream_of_stream' (@scons' t T NE) = Stream.app_list_stream t (stream_of_stream' T).
  Proof.
    induction t.
    intros. elim NE. auto.
    intros. simpl.
    rewrite (unroll_stream (stream_of_stream' (@scons' (a :: t) T NE))).
    simpl. destruct t. auto.
    simpl. f_equal. apply IHt.
  Qed.

End Sequences_Traces.
