Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import ClassicalExtras.
Require Import List.
Import ListNotations.


(** This file provides a abstract definition of small-step operational
    semantics.  Then, we show that under certain assumptions of
    *determinacy* of configurations, these semantics satisfy the
    particular property that we call "Safety-Like". This property,
    along with determinacy, can be used to prove that R2rSP => RTEP
    (file r2RSC_teq.v) 
*)
Section SmallSteps.

Variable partial : Set.
Variable program : Set.
Variable context : Set.
Variable plug : partial -> context -> program.

Variable cfg : Set.
Variable init : program -> cfg.
Variable step : cfg -> event -> cfg -> Prop.

Definition stuck (c:cfg) : Prop :=  forall e c', ~step c e c'.

Variable silent : event -> Prop.

CoInductive can_loop_silent : cfg -> Prop :=
| FSilent : forall c e c', step c e c' -> silent e -> can_loop_silent c' -> can_loop_silent c.
Hint Constructors can_loop_silent.

(** Reflexive Transitive Closure of the step relation *)
Inductive steps' : cfg -> pref -> cfg -> Prop :=
| SSTbd : forall c, steps' c nil c
| SSCons : forall c e c' m c'', step c e c' -> ~silent e -> steps' c' m c'' ->
                                                            steps' c (cons e m) c''
| SSSilent : forall c e c' c'' m, step c e c' -> silent e -> steps' c' m c'' -> steps' c m c''.
Hint Constructors steps'.

Lemma steps'_refl : forall c,
    steps' c [] c.
Proof.
  eauto.
Qed.
Hint Resolve steps'_refl.

Lemma steps'_trans : forall c1 c2 c3 m m',
    steps' c1 m c2 -> steps' c2 m' c3 -> steps' c1 (m ++ m') c3.
Proof.
  intros c1 c2 c3 m m' H H0. generalize dependent c3. generalize dependent m'.
  induction H; intros; simpl; eauto.
Qed.
Hint Resolve steps'_trans.

Lemma steps'_cons : forall c c' e m,
    steps' c (e :: m) c' -> exists c'', steps' c [e] c'' /\ steps' c'' m c'.
Proof.
  intros c c' e m H.
  remember (e :: m) as mm.
  induction H.
  - inversion Heqmm.
  - inversion Heqmm; subst.
    exists c'. split; eauto.
  - inversion Heqmm; subst.
    specialize (IHsteps' H2).
    destruct IHsteps' as [c0 [Hc01 Hc02]].
    exists c0; eauto.
Qed.
Hint Resolve steps'_cons.

Definition steps (c:cfg) (m:finpref) (c':cfg) : Prop :=
  match m with
  | ftbd m' => steps' c m' c'
  | fstop m' => steps' c m' c' /\ stuck c'
  end.

Hint Unfold steps.


(* Keep that for later, maybe it will be useful *)
(* Inductive steps_silent : cfg -> cfg -> Prop := *)
(* | SilOne : forall (c c': cfg) (e : event), step c e c' -> silent e -> steps_silent c c' *)
(* | SilCons : forall (c c' c'' : cfg) (e : event), *)
(*     step c e c' -> silent e -> steps_silent c' c'' -> steps_silent c c''. *)
(* Hint Constructors steps_silent. *)

(* Lemma steps_silent_trans : forall c1 c2 c3, *)
(*     steps_silent c1 c2 -> steps_silent c2 c3 -> steps_silent c1 c3. *)
(* Proof. *)
(*   intros c1 c2 c3 H H0. generalize dependent c3. *)
(*   induction H; intros; simpl; eauto. *)
(* Qed. *)
(* Hint Resolve steps_silent_trans. *)

(* Lemma steps_silent_cons : forall c c', *)
(*     steps_silent c c' -> *)
(*     (exists e, step c e c' /\ silent e) \/ (exists c'', steps_silent c c'' /\ steps_silent c'' c'). *)
(* Proof. *)
(*   intros c c' H. *)
(*   induction H. *)
(*   - left; eexists; now eauto. *)
(*   - right; eexists; eauto. *)
(* Qed. *)
(* Hint Resolve steps_silent_cons. *)

(* must terminate or cause non-silent event ... TODO: but that's not
   what we can easily write, folowing definition may termination *)
Definition cannot_loop_silent (c:cfg) : Prop :=
  forall c', steps' c nil c' -> exists e c'', steps' c' (cons e nil) c''.

Definition does_event_or_goes_wrong (c:cfg) :=
  (* (exists e c', steps' c (cons e nil) c') \/ (exists c', steps' c nil c' /\ stuck c'). *)
  {exists e c', steps' c (cons e nil) c'} + {exists c', steps' c nil c' /\ stuck c'}.
  
Lemma not_can_loop_silent : forall c, ~(can_loop_silent c) -> does_event_or_goes_wrong c.
Proof.
  (* intro c. rewrite contra. intro Hc. rewrite <- dne. cofix. -- no longer works with + *)
Admitted.

(** Semantics: the semantics produce full traces, not finite prefixes. *)
(* A definition of the semantics, using a well-founded order 
   and based on Compcert, module Smallstep *)
Variable A: Type.
Variable order: A -> A -> Prop.
Hypothesis an_A : A. (* A is not empty *)
Hypothesis order_wf: well_founded order.
Hypothesis order_inf: forall (a : A), exists a', order a a'. (* Example: natural numbers *)

CoInductive sem'_N : A -> cfg -> trace -> Prop :=
| SStopN : forall c a, stuck c -> sem'_N a c tstop
| SSilentDivN : forall c a, can_loop_silent c -> sem'_N a c tsilent
| SAppNilN : forall c c' t a1 a2, steps' c [] c' -> order a2 a1 ->
                             sem'_N a2 c' t -> sem'_N a1 c t
| SAppN : forall c c' m t a1 a2, m <> [] -> steps' c m c' ->
                            sem'_N a2 c' t -> sem'_N a1 c (tapp (ftbd m) t).

Lemma sem'_N_inv:
  forall a c t,
  sem'_N a c t ->
  exists m, exists c', exists a', exists t',
          steps' c m c' /\ sem'_N a' c' t' /\ t = tapp (ftbd m) t'.
Proof.
  intros a. pattern a. apply (well_founded_ind order_wf).
  intros a' Hi c t H.
  inversion H; subst; repeat eexists; eauto.
Qed.
Hint Resolve sem'_N_inv.

Inductive sem' : cfg -> trace -> Prop :=
| sem'_cons : forall a c t, sem'_N a c t -> sem' c t.
Hint Constructors sem'.

Lemma sem'_inv : forall c t,
    sem' c t -> exists m c' t', steps' c m c' /\ sem' c' t' /\ t = tapp (ftbd m) t'.
Proof.
  intros c t H.
  inversion H; subst. repeat eexists; eauto.
Qed.
Hint Resolve sem'_inv.


(* Another definition of the semantics, based on the reflexive transitive closrure of the step 
   relation but without restrictions on appplying the silent event only finitely many times *)
CoInductive sem'' : cfg -> trace -> Prop :=
| SStop : forall c, stuck c -> sem'' c tstop
| SSilentDiv : forall c, can_loop_silent c -> sem'' c tsilent
| SApp : forall c c' m t, steps' c m c' -> sem'' c' t -> sem'' c (tapp (ftbd m) t).

Lemma sem'_sem'':
  forall c t, sem' c t -> sem'' c t.
Proof.
  cofix Hfix; intros.
  destruct (sem'_inv c t H) as [m [c' [t' [H1 [H2 H3]]]]].
  rewrite H3.
  apply SApp with (c' := c'). assumption.
  apply Hfix. auto.
Qed.


(* Might be useful later? *)
(* CoInductive sem'_N : A -> cfg -> trace -> Prop := *)
(* | SStopN : forall c a, stuck c -> sem'_N a c tstop *)
(* | SConsN : forall c e c' t a1 a2, step c e c' -> ~silent e -> sem'_N a1 c' t -> sem'_N a2 c (tcons e t) *)
(* | SSilentN : forall c c' t a1 a2, steps_silent c c' -> order a1 a2 -> sem'_N a1 c' t -> sem'_N a2 c t *)
(*    (* Shouldn't be able to infinitely step with a silent event *) *)
(* | SSilentDivN : forall c a, can_loop_silent c -> sem'_N a c tsilent. *)





(* This lemma should accurately model one expectation from the small-step semantics:
   if a configuration can produce a whole trace with a least one single event, then
   in particular it can finitely produce this event. *)

Lemma sem'_N_tcons : forall a c e t,
    sem'_N a c (tcons e t) -> exists c' a', steps' c [e] c' /\ sem'_N a' c' t.
Proof.
  intros a. pattern a. apply (well_founded_ind order_wf).
  intros a' Hi c e t H.
  inversion H; subst.
  - specialize (Hi a2 H1 c' e t H2).
    destruct Hi as [c'0 [a'0 [H1' H2']]].
    repeat eexists; eauto. eapply steps'_trans with (m := []) (m' := [e]); eassumption.
  - destruct m; subst.
    + contradiction.
    + inversion H0; subst. simpl in *.
      apply steps'_cons in H2.
      destruct H2 as [c'' [H3 H4]]. clear H0. clear H1.
      destruct m.
      * exists c'. exists a2. split. eapply steps'_trans with (m := [e]) (m' := []); eauto.
        simpl. eauto.
      * exists c''. exists a2. split. assumption.
        pose proof (SAppN c'' c' (e0 :: m) t0 a2 a2).
        assert (e0 :: m <> []) by now destruct m.
        specialize (H0 H1 H4 H5). assumption.
Qed.
Hint Resolve sem'_N_tcons.

Lemma sem'_tcons : forall c e t,
    sem' c (tcons e t) -> exists c', steps' c [e] c' /\ sem' c' t.
Proof.
  intros c e t H.
  inversion H; subst.
  eapply sem'_N_tcons in H0.
  destruct H0 as [c' [a' [H1 H2]]]. eexists; eauto.
Qed.

Axiom classicT : forall (P : Prop), {P} + {~ P}.
Axiom indefinite_description : forall (A : Type) (P : A->Prop),
   ex P -> sig P.

Definition sem (p:program) : trace -> Prop := sem' (init p).


CoFixpoint trace_of (c:cfg) : trace.
  destruct (classicT (stuck c)) as [H | H]. exact tstop.
  unfold stuck in H. do 2 setoid_rewrite not_forall_ex_not in H.
  apply indefinite_description in H. destruct H as [e H].
  apply indefinite_description in H. destruct H as [c' H].
  apply NNPP in H.
  destruct (classicT (silent e)) as [He | He].
  - destruct (classicT (can_loop_silent c')) as [Hc | Hc].
    + exact tsilent.
    + apply not_can_loop_silent in Hc. destruct Hc as [Hc | Hc].
      * apply indefinite_description in Hc. destruct Hc as [e' Hc].
        apply indefinite_description in Hc. destruct Hc as [c'' Hs].
        exact (tcons e' (trace_of c'')).
      * apply indefinite_description in Hc. destruct Hc as [c'' [Hs1 Hs2]].
        exact tstop.
  - exact (tcons e (trace_of c')).
Defined.

(* The usual hack to unfold CoFixpoints, but it ain't pretty and
   it still doesn't compute because of all the axioms
   TODO: update this
 *)
Lemma trace_of_eta : forall c,
  trace_of c =
        match classicT (stuck c) with
        | left _ => tstop
        | right H0 =>
            let (e, H1) :=
              indefinite_description event
                (fun n : event => exists n0 : cfg, ~ ~ step c n n0)
                (Morphisms.subrelation_proper Morphisms_Prop.ex_iff_morphism tt
                   (Morphisms.subrelation_respectful
                      (Morphisms.subrelation_refl
                         (Morphisms.pointwise_relation event iff))
                      Morphisms.iff_impl_subrelation)
                   (fun n : event => ~ (forall c' : cfg, ~ step c n c'))
                   (fun n : event => exists n0 : cfg, ~ ~ step c n n0)
                   (fun n : event =>
                    not_forall_ex_not cfg (fun n0 : cfg => ~ step c n n0))
                   (Morphisms.iff_impl_subrelation
                      (~ (forall (n : event) (c' : cfg), ~ step c n c'))
                      (exists n : event, ~ (forall c' : cfg, ~ step c n c'))
                      (not_forall_ex_not event
                         (fun n : event => forall c' : cfg, ~ step c n c')) H0)) in
            let (c', _) :=
              indefinite_description cfg (fun n : cfg => ~ ~ step c e n) H1 in
            tcons e (trace_of c')
        end.
Proof.
Admitted.

(* CoFixpoint sem'_trace_of (c:cfg) : sem'' c (trace_of c). *)
(*   rewrite trace_of_eta. destruct (classicT (stuck c)) as [H | H]. *)
(*   - now apply SStop. *)
(*   - unfold stuck in H. (* rewrite not_forall_ex_not in H. -- strange error *) *)
(*     assert (exists (e : event), ~ (forall (c' : cfg), ~ step c e c')) *)
(*       as [e H1] by now apply not_forall_ex_not. *)
(*     assert (exists c', ~ ~ step c e c') as [c' H2] by now apply not_forall_ex_not. *)
(*     clear H1. *)
(*     apply NNPP in H2. *)
(* Admitted. *)

Lemma sem'_trace_of (c : cfg) : sem' c (trace_of c).
  apply sem'_cons with (a := an_A).
  generalize dependent c.
  cofix Hfix.
  intros c.
  rewrite trace_of_eta. destruct (classicT (stuck c)) as [H | H].
  - now apply SStopN.
  - unfold stuck in H.
    assert (exists (e : event), ~ (forall (c' : cfg), ~ step c e c'))
      as [e H1] by now apply not_forall_ex_not.
    assert (exists c', ~ ~ step c e c') as [c' H2] by now apply not_forall_ex_not.
    clear H1.
    apply NNPP in H2.
    destruct (classicT (silent e)) as [He | He].
    + (* silent *)
      admit.
    + (* not silent *)
      specialize (Hfix c').
Admitted.

Lemma non_empty_sem : forall W, exists t, sem W t.
Proof. intro W. exists (trace_of (init W)). apply sem'_trace_of.
Qed.

(** Definition of the language *)
Definition lang : language := @Build_language partial
                                        program
                                        context
                                        plug
                                        sem
                                        non_empty_sem.

(** Build links between the semantics of the language and the
    step by step relation *)
Lemma steps'_sem'_single : forall c c' t,
    steps' c [] c' ->
    sem' c' t ->
    sem' c t.
Proof.
  intros c c' t H H0.
  inversion H0; subst; eauto.
  destruct (order_inf a) as [a' Ha'].
  apply sem'_cons with (a := a').
  econstructor; eauto.  
Qed.
Hint Resolve steps'_sem'_single.

Lemma steps'_sem' : forall c e c' t,
  steps' c [e] c' ->
  sem' c' t ->
  sem' c (tcons e t).
Proof.
  intros c e c' t H H0.
  inversion H0; subst; eauto.
  destruct (order_inf a) as [a' Ha'].
  apply sem'_cons with (a := a').
  eapply SAppN with (m := [e]); eauto.
  intros Hn; inversion Hn.
Qed.
Hint Resolve steps'_sem'.

Lemma steps'_sem'_N : forall c e c' t a,
    steps' c [e] c' ->
    sem'_N a c' t ->
    sem'_N a c (tcons e t).
Proof.
  intros c e c' t a H H0.
  eapply SAppN with (m := [e]); eauto.
  intros Hn; inversion Hn.
Qed.

Lemma steps_sem'_app : forall c m c' t,
  steps c m c' ->
  sem' c' t ->
  sem' c (tapp m t).
Proof.
  intros c m c' t H H0.
  destruct m.
  - simpl in *.
    inversion H; subst; try now auto.
    induction H1; subst; try now auto.
    + simpl in *. econstructor. now constructor.
    + specialize (IHsteps' (conj H4 H2) H0 H2).
      inversion IHsteps'; subst; eauto.
      simpl in *. econstructor.
      eapply SAppN with (m := [e]) (c' := c'); eauto.
      intros Hn; inversion Hn.
    + specialize (IHsteps' (conj H4 H2) H0 H2).
      inversion IHsteps'; subst; eauto.    
  - inversion H0; subst; eauto.
    destruct (order_inf a) as [a' Ha'].
    apply sem'_cons with (a := a').
    destruct p as [| e' p'].
    + econstructor; eauto.
    + eapply SAppN with (m := e' :: p'); eauto.
      intros Hn; inversion Hn.
      Unshelve.
      exact an_A. exact a.   
Qed.

Lemma steps_psem : forall P m c,
  steps (init P) m c ->
  @psem lang P m.
Proof.
  intros P m c Hsteps.
  unfold psem. simpl. exists (tapp m (trace_of c)). split.
  - destruct m.
    + destruct Hsteps.
      apply tapp_pref.
    + unfold sem.
      inversion Hsteps; subst.
      ++ now split.
      ++ apply tapp_pref.
      ++ apply tapp_pref.
  - unfold sem.
    eapply steps_sem'_app. eassumption.
    now apply sem'_trace_of.
Qed.

Lemma sem'_prefix : forall m c0 t,
  sem' c0 t ->
  prefix m t ->
  fstopped m = false ->
  exists c, steps c0 m c.
Proof.
  induction finpref m as e p IHp; intros c0 t Hsem Hpref Hnot_stopped; try inversion Hnot_stopped.
  - exists c0. apply SSTbd.
  - destruct t as [| | e' t']; try now inversion Hpref.
    destruct Hpref as [Heq Hpref]; subst.
    (* inversion Hsem; subst; simpl in *. *)
    apply sem'_tcons in Hsem.
    destruct Hsem as [c' [H1 H2]].
    specialize (IHp c' t' H2 Hpref Hnot_stopped).
    destruct IHp as [c'' Hc''].
    exists c''.
    simpl.
    apply steps'_trans with (m := [e']) (m' := p) (c2 := c'); eauto.
Qed.

Lemma sem_prefix : forall m P t,
  sem P t ->
  prefix m t ->
  fstopped m = false ->
  exists c, steps (init P) m c.
(* /\ exists t', t_eq t (tapp m t') /\ sem' c t' *)
(* A better way to state this might be to avoid t_eq and use
   an operation to remove m from t -- for now removed that part since not needed *)
Proof. intros m P. now apply (sem'_prefix m (init P)). Qed.

Lemma psem_steps : forall m P,
  @psem lang P m ->
  fstopped m = false ->
  exists c, steps (init P) m c.
Proof. intros m P [t [H1 H2]] Hstopped. eapply sem_prefix; eassumption. Qed.

Definition semantics_safety_like_reverse : forall t P m,
  sem P t ->
  prefix m t ->
  @psem lang P m.
Proof.
  intros t P m H H0. unfold psem. exists t. split; assumption.
Qed.

Fixpoint fsnoc' (m : finpref) (e : event) : finpref :=
  match m with
  | fstop m' => fstop (snoc m' e)
  | ftbd m' => ftbd (snoc m' e)
  end.

Theorem finpref_ind_snoc :
  forall (P : finpref -> Prop),
    P (ftbd nil) ->
    (forall (m : pref), P (fstop m)) ->
    (forall (m : finpref) (e : event), P m -> P (fsnoc m e)) ->
    forall m, P m.
Proof.
  (* Proof similar to list_rev_ind in the Coq library *)
  intros P H H0 H1 m.
  destruct m; eauto.
  rewrite <- (@rev_involutive event p).
  induction (rev p).
  apply H.
  simpl.
  assert (forall l, l ++ [a] = snoc l a).
  { clear.
    induction l. now simpl.
    simpl in *. rewrite IHl. reflexivity. }
  specialize (H2 (rev l)). rewrite H2.
  specialize (H1 (ftbd (rev l)) a IHl). assumption.
Qed.

Lemma not_diverges_cons : forall e t, ~ diverges (tcons e t) -> ~ diverges t.
  intros e t H Hn.
  apply H. now constructor.
Qed.

Definition configuration_determinacy := forall (c c1 c2 : cfg) (m : pref),
    steps' c m c1 -> steps' c m c2 -> steps' c1 [] c2 \/ steps' c2 [] c1.

Definition very_strong_determinacy := forall (c c1 c2 : cfg) (e1 e2 : event),
    steps' c [e1] c1 -> steps' c [e2] c2 -> ((e1 = e2 /\ c1 = c2) \/ (is_input e1 /\ is_input e2 /\ e1 <> e2)).

Definition strong_determinacy := forall (c c1 c2 : cfg) (e1 e2 : event),
    step c e1 c1 -> step c e2 c2 -> ((e1 = e2 /\ c1 = c2) \/ (is_input e1 /\ is_input e2 /\ e1 <> e2)).

Definition rel_cfg (c1 c2 : cfg) : Prop := forall (t : trace), sem' c1 t <-> sem' c2 t.

Lemma rel_cfg_reflexivity : forall (c : cfg), rel_cfg c c.
Proof.
  now unfold rel_cfg.
Qed.

Lemma rel_cfg_transitivity : forall (c1 c2 c3 : cfg), rel_cfg c1 c2 -> rel_cfg c2 c3 -> rel_cfg c1 c3.
Proof.
  unfold rel_cfg. firstorder.
Qed.

Lemma rel_cfg_symmetry : forall (c1 c2 : cfg), rel_cfg c1 c2 -> rel_cfg c2 c1.
Proof.
  now firstorder.
Qed.

Definition rel_cfg_pref (c1 c2 : cfg) : Prop := forall (m : pref),
    (exists c1', steps' c1 m c1') <-> (exists c2', steps' c2 m c2').

Lemma steps'_to_sem'_N_pref : forall c c' m,
    steps' c m c' ->
    exists t a, prefix (ftbd m) t /\ sem'_N a c t.
Proof.
  intros c c' m H.
  induction H.
  - pose proof (sem'_trace_of c).
    inversion H; subst.
    exists (trace_of c). exists a.
    split; simpl; eauto.
  - destruct IHsteps' as [t' [a [H2 H3]]].
    exists (tcons e t'). exists a. split. now simpl.
    eapply SAppN with (c' := c') (m := [e]); eauto. intros Hn; inversion Hn.
  - destruct IHsteps' as [t' [a [H2 H3]]].
    destruct (order_inf a) as [a' Ha'].
    exists t'. exists a'. split. now simpl.
    eapply SAppNilN with (c' := c'); eauto.
Qed.

Lemma steps'_to_sem'_pref : forall c c' m,
    steps' c m c' ->
    exists t, prefix (ftbd m) t /\ sem' c t.
Proof.
  intros c c' m H.
  apply steps'_to_sem'_N_pref in H.
  destruct H as [t [a [H1 H2]]]. eauto.
Qed.


Lemma sem'_N_pref_to_steps' : forall c m t a,
    prefix (ftbd m) t -> sem'_N a c t -> exists c', steps' c m c'.
Proof.
  intros c m.
  generalize dependent c.
  induction m; intros.
  - now eauto.
  - destruct t.
    + inversion H.
    + inversion H.
    + apply sem'_N_tcons in H0. destruct H0 as [c' [a' [H1 H2]]].
      assert (Hpref: prefix (ftbd m) t) by now inversion H.
      inversion H; subst. clear H3.
      specialize (IHm c' t a' Hpref H2). destruct IHm as [c'0 H3].
      exists c'0.
      eapply steps'_trans with (m := [e]) (m' := m); eassumption.
Qed.

Lemma sem'_pref_to_steps' : forall c m t,
    prefix (ftbd m) t -> sem' c t -> exists c', steps' c m c'.
Proof.
  intros c m t H H0.
  inversion H0; subst. 
  eauto using sem'_N_pref_to_steps'.
Qed.

Lemma rel_cfg_to_rel_cfg_pref : forall c1 c2, rel_cfg c1 c2 -> rel_cfg_pref c1 c2.
Proof.
  unfold rel_cfg, rel_cfg_pref.
  intros c1 c2 H m.
  split.
  - intros H'. destruct H' as [c1' H'].
    apply steps'_to_sem'_pref in H'.
    destruct H' as [t [H1 H2]].
    apply H in H2. inversion H2; subst; eauto.
    eapply sem'_N_pref_to_steps' with (t := t).
    assumption. eassumption.
  - intros H'. destruct H' as [c1' H'].
    apply steps'_to_sem'_pref in H'.
    destruct H' as [t [H1 H2]].
    apply sem'_pref_to_steps' with (t := t).
    assumption.
    now apply (H t).
Qed.

Definition weak_determinacy := forall (c1 c1' c2 c2' : cfg) (m : pref),
    rel_cfg c1 c1' -> steps' c1 m c2 -> steps' c1' m c2' -> rel_cfg c2 c2'.

(* Lemma steps'_cons_smaller : forall c1 c3 m e, *)
(*     steps' c1 (e :: m) c3 -> exists c2, steps' c1 [e] c2 /\ steps' c2 m c3. *)
(* Proof. *)
(*   intros c1 c3 m e H. *)
(*   remember (e :: m) as p. *)
(*   induction H. *)
(*   - inversion Heqp. *)
(*   - inversion Heqp; subst. clear Heqp. *)
(*     exists c'; split. apply SSCons with (c' := c'); auto. *)
(*     constructor. assumption. *)
(*   - inversion Heqp; subst. specialize (IHsteps' H2). *)
(*     destruct IHsteps' as [c2 [Hc2 Hc2']]. *)
(*     exists c2. split. *)
(*     apply SSSilent with (e := e0) (c' := c'); auto. *)
(*     assumption. *)
(* Qed. *)

Lemma steps'_not_silent : forall c c' e, steps' c [e] c' -> ~ silent e.
Proof.
  intros c c' e H.
  remember [e] as m.
  induction H; eauto; inversion Heqm; now subst.
Qed.

Inductive stopped : trace -> Prop :=
  | stopped_stop : stopped tstop
  | stopped_cons : forall (e : event) (t : trace), stopped t -> stopped (tcons e t).

Lemma ind_hyp (det : weak_determinacy) : forall t c,
    ~ diverges t -> ~ stopped t ->
    (forall m, prefix (ftbd m) t -> exists c', steps' c m c') ->
    sem' c t.
Proof.
  intros.
  apply sem'_cons with (a := an_A).
  generalize dependent an_A.
  generalize dependent t. generalize dependent c.
  cofix. intros c t Hndiv Hnstopped H a.
  destruct t as [| | e t'].
  - apply False_ind. apply Hnstopped. now constructor.
  - apply False_ind. apply Hndiv. now constructor.
  - assert (Hsilent: ~silent e).
    { specialize (H [e]).
      assert (prefix (ftbd [e]) (tcons e t')) by now simpl.
      specialize (H H0). destruct H as [c' Hc'].
      eapply steps'_not_silent; now eauto.
    }
    pose proof H as H'.
    assert (H1: prefix (ftbd [e]) (tcons e t')) by now split.
    specialize (H' [e] H1); clear H1. destruct H' as [c' Hc'].
    destruct (order_inf a) as [a1 Ha1].
    apply SAppN with (c' := c') (m := [e]) (a2 := a1).
    intros Hn; inversion Hn.
    (* apply steps'_sem'_N with (c' := c'). *)
    assumption.
    assert (Hndiv' : ~ diverges t').
    { intros Hn; apply Hndiv; now constructor. }
    assert (Hnstopped' : ~ stopped t').
    { intros Hn; apply Hnstopped; now constructor. }
    Guarded.
    apply ind_hyp; try now assumption.
    Guarded.
    intros m H0.
    assert (H': prefix (ftbd (e :: m)) (tcons e t')) by now split.
    specialize (H (e :: m) H'); clear H'.
    unfold weak_determinacy in det.
    destruct H as [c'' Hc''].
    apply steps'_cons in Hc''.
    destruct Hc'' as [cc [Hcc1 Hcc2]].
    specialize (det c c c' cc [e] (rel_cfg_reflexivity c) Hc' Hcc1).
    apply rel_cfg_to_rel_cfg_pref in det. unfold rel_cfg_pref in det.
    specialize (det m).
    destruct det as [_ det].
    assert (exists c2' : cfg, steps' cc m c2') by (now exists c'').
    specialize (det H).
    apply det.
Qed.

(* The original semantics_safety_like_right can only be obtained if we assume determinacy *)
Lemma semantics_safety_like_right (det : weak_determinacy): forall t P,
  ~ diverges t -> ~ stopped t -> 
  (forall m, prefix m t -> @psem lang P m) -> sem P t.
Proof.
  intros t P Hndiv Hnstopped H.
  destruct t as [| | e0 t0].
  - specialize (H (fstop nil) I). unfold psem in H.
    destruct H as [t [H1 H2]].
    now destruct t.
  - exfalso. apply Hndiv. now constructor.
  - remember (tcons e0 t0) as t.
    apply ind_hyp.
    apply det.
    apply Hndiv.
    apply Hnstopped.
    intros m H'.
    specialize (H (ftbd m) H').
    apply psem_steps in H; [| reflexivity].
    destruct H as [c2 H].
    simpl in H.
    now (exists c2).
Qed.

Lemma tgt_sem (det : weak_determinacy) : semantics_safety_like lang.
  (* Basic idea: if t is not in sem P, there is a prefix of t, m (here
     signified with a dependent type for the sake of simplicity), that
     does not belong to psem P. The argument can be that if every prefix
     of t is in the semantics, then t itself must be, too.

     Consider now the initial bad prefix m. If m is empty, choose it as
     the minimal bad prefix and any event as the bad event: these two
     instantiate the existentials in the goal. If m = snoc m' e, there
     are two possible cases: if m' is in sem P, it is the minimal bad
     prefix and e the bad event, and we are done; if m' is still not in
     sem P, we continue reducing it. (Thus, an easy induction.) *)

Proof.
  unfold semantics_safety_like. simpl.
  intros t P Hsem Hinf Hndiv.
  destruct (classic (stopped t)) as [Hstopped | Hnstopped].
  (* t stopped *)
  assert (Hstopinf : stopped t -> fin t).
  { clear.
    intros H.
    induction H; now constructor. }
  specialize (Hinf (Hstopinf Hstopped)). now contradiction.
  pose proof (semantics_safety_like_right det t P Hndiv Hnstopped).
  rewrite -> contra in H.
  specialize (H Hsem). apply not_all_ex_not in H.
  destruct H as [m Hm]. rewrite not_imp in Hm. destruct Hm as [Hm1 Hm2].
  generalize dependent Hm2. generalize dependent Hm1.
  destruct m as [p | p].
  - (* fstop *)
    intros Hm1 Hm2.
    assert (forall t m, prefix (fstop m) t -> fin t).
    { clear. intros t m. generalize dependent t. induction m; intros t H.
      - destruct t; try now auto. constructor.
      - destruct t; try now auto.
        destruct H as [H1 H2].
        specialize (IHm t H2). now constructor. }
    unfold inf in Hinf. exfalso; apply Hinf. now apply (H t p Hm1).
  - (* ftbd *)
    induction p as [| p' e' IH] using pref_ind_snoc; intros Hm1 Hm2.
    + (* p = nil *)
      assert (Hm2' : @psem lang P (ftbd nil)).
      { clear. unfold psem. pose proof non_empty_sem P. destruct H as [t Ht].
        exists t; now split. }
      now contradiction.
    + (* p = snoc p' e' *)
      pose proof (classic (@psem lang P (ftbd p'))) as [H | H].
      ++ exists (ftbd p'), e'. subst. split; try split; assumption.
      ++ apply IH.
         assert (H0: forall (p : pref) e t, prefix (ftbd (snoc p e)) t -> prefix (ftbd p) t).
         { clear. induction p.
           - intros. now auto.
           - intros. simpl in *. destruct t; try now auto.
             destruct p; try now auto.
             destruct H as [H1 H2].
             specialize (IHp e t H2).
             split; try now auto.
         }
         apply H0 in Hm1. assumption.
         assumption.
Qed.

End SmallSteps.
