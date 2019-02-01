Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import ClassicalExtras.
Require Import List.
Import ListNotations.

Axiom classicT : forall (P : Prop), {P} + {~ P}.
Axiom indefinite_description : forall (A : Type) (P : A->Prop),
   ex P -> sig P.


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
Variable es_of_cfg : forall (c : cfg), stuck c -> endstate.


Variable silent : event -> Prop.

CoInductive can_loop_silent : cfg -> Prop :=
| FSilent : forall c e c', step c e c' -> silent e -> can_loop_silent c' -> can_loop_silent c.
Hint Constructors can_loop_silent.

(** Reflexive Transitive Closure of the step relation *)
Inductive steps' : cfg -> list event -> cfg -> Prop :=
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

Inductive steps : cfg -> finpref -> cfg -> Prop :=
| steps_ftbd : forall c m' c', steps' c m' c' -> steps c (ftbd m') c'
| steps_fstop : forall c m' c' (H : stuck c'), steps' c m' c' -> steps c (fstop m' (es_of_cfg c' H)) c'.

(* Definition steps (c:cfg) (m:finpref) (c':cfg) : Prop := *)
(*   match m with *)
(*   | ftbd m' => steps' c m' c' *)
(*   | fstop m' es => steps' c m' c' /\ stuck c' *)
(*   end. *)

Hint Constructors steps.


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

Definition does_event_or_goes_wrong' (c : cfg) :=
  exists m c', steps' c m c' /\ (stuck c' \/ m <> []).

Lemma not_can_loop_silent' :  forall c, ~(can_loop_silent c) -> does_event_or_goes_wrong' c.
Proof.
  intros c.
  rewrite contra. intros Hc. rewrite <- dne.
  generalize dependent c.
  cofix Hfix.
  - intros c Hc.
    unfold does_event_or_goes_wrong' in Hc.
    assert (~ stuck c).
    { rewrite not_ex_forall_not in Hc. specialize (Hc []).
      rewrite not_ex_forall_not in Hc. specialize (Hc c).
      rewrite de_morgan1 in Hc. destruct Hc.
      - exfalso. apply H. constructor.
      - rewrite de_morgan2 in H. destruct H. assumption.
    }
    unfold stuck in H.
    rewrite not_forall_ex_not in H.
    destruct H as [e Hn].
    rewrite not_forall_ex_not in Hn. destruct Hn as [c' H].
    rewrite <- dne in H.
    destruct (classic (silent e)).
    (* Hfix *)
    apply FSilent with (e := e) (c' := c'); try assumption.
    apply Hfix.
    unfold does_event_or_goes_wrong'.
    intros Hn. destruct Hn as [m [c'0 [H1 H2]]].
    rewrite (not_ex_forall_not) in Hc. specialize (Hc m).
    rewrite (not_ex_forall_not) in Hc. specialize (Hc c'0).
    apply Hc. split.
    econstructor; eassumption.
    assumption.
    rewrite (not_ex_forall_not) in Hc. specialize (Hc [e]).
    rewrite (not_ex_forall_not) in Hc. specialize (Hc c').
    rewrite de_morgan1 in Hc. destruct Hc.
    exfalso. apply H1. econstructor. apply H. apply H0. constructor.
    apply de_morgan2 in H1. destruct H1.
    exfalso. apply H2. intros Hn. inversion Hn.
Qed.

Definition does_event_or_goes_wrong (c:cfg) :=
  (* (exists e c', steps' c (cons e nil) c') \/ (exists c', steps' c nil c' /\ stuck c'). *)
  {exists e c', steps' c [e] c'} + {exists c', steps' c [] c' /\ stuck c'}.
  
Lemma not_can_loop_silent : forall c, ~(can_loop_silent c) -> does_event_or_goes_wrong c.
Proof.
  intros c Hc.
  unfold does_event_or_goes_wrong.
  apply not_can_loop_silent' in Hc. unfold does_event_or_goes_wrong' in Hc.
  apply indefinite_description in Hc. destruct Hc as [m Hc].
  apply indefinite_description in Hc. destruct Hc as [c' Hc].
  destruct Hc as [H1 H2].
  destruct m as [|e p].
  - assert (H3: stuck c') by (destruct H2; now auto).
    right. exists c'. now split.
  - left. apply steps'_cons in H1.
    destruct H1 as [c'0 [H11 H12]].
    exists e. exists c'0. assumption.
Qed.

(** Semantics: the semantics produce full traces, not finite prefixes. *)
(* A definition of the semantics, using a well-founded order 
   and based on Compcert, module Smallstep *)
Variable A: Type.
Variable order: A -> A -> Prop.
Hypothesis an_A : A. (* A is not empty *)
Hypothesis order_wf: well_founded order.
Hypothesis order_inf: forall (a : A), exists a', order a a'. (* Example: natural numbers *)

CoInductive sem'_N : A -> cfg -> trace -> Prop :=
| SStopN : forall c a (H : stuck c), sem'_N a c (tstop nil (es_of_cfg c H))
| SSilentDivN : forall c a, can_loop_silent c -> sem'_N a c (tsilent nil)
| SAppNilN : forall c c' t a1 a2, steps' c [] c' -> order a2 a1 ->
                             sem'_N a2 c' t -> sem'_N a1 c t
| SAppN : forall c c' m t a1 a2, m <> [] -> steps' c m c' ->
                            sem'_N a2 c' t -> sem'_N a1 c (tapp (ftbd m) t).

Lemma tapp_ftbd_nil_id : forall t, t = tapp (ftbd []) t.
Proof.
  now destruct t.
Qed.
Hint Resolve tapp_ftbd_nil_id.

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
| SStop : forall c (H : stuck c), sem'' c (tstop nil (es_of_cfg c H))
| SSilentDiv : forall c, can_loop_silent c -> sem'' c (tsilent nil)
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

Lemma sem'_N_tapp : forall a c e t,
    sem'_N a c (tapp (ftbd [e]) t) -> exists c' a', steps' c [e] c' /\ sem'_N a' c' t.
Proof.
  intros a. pattern a. apply (well_founded_ind order_wf).
  intros a' Hi c e t H.
  inversion H; subst.
  - destruct t; inversion H4.
  - destruct t; inversion H0.
  - specialize (Hi a2 H1 c' e t H2).
    destruct Hi as [c'0 [a'0 [H1' H2']]].
    repeat eexists; eauto.
    eapply steps'_trans with (m := []) (m' := [e]); eassumption.
  - destruct m; subst.
    + contradiction.
    + simpl in *.
      apply steps'_cons in H2.
      assert (Hee0 : e = e0) by (destruct t0, t; now inversion H0).
      rewrite <- Hee0 in *.
      destruct H2 as [c'' [H3 H4]]. (* clear H0. clear H1. *)
      destruct m.
      * exists c'. exists a2. split. eapply steps'_trans with (m := [e]) (m' := []); eauto.
        destruct t, t0; inversion H0; subst; assumption.
      * exists c''. exists a2. split. assumption.
        pose proof (SAppN c'' c' (e1 :: m) t0 a2 a2).
        assert (e1 :: m <> []) by now destruct m.
        specialize (H2 H6 H4 H5).
        destruct t, t0; inversion H0; subst; assumption.
Qed.
Hint Resolve sem'_N_tapp.

Lemma sem'_tapp : forall c e t,
    sem' c (tapp (ftbd [e]) t) -> exists c', steps' c [e] c' /\ sem' c' t.
Proof.
  intros c e t H.
  inversion H; subst.
  eapply sem'_N_tapp in H0.
  destruct H0 as [c' [a' [H1 H2]]]. eexists; eauto.
Qed.


Definition sem (p:program) : trace -> Prop := sem' (init p).

CoFixpoint dummy_stream : @stream event :=
  scons an_event dummy_stream.

Inductive can_get_stuck : cfg -> Prop :=
| stuck_now : forall c, stuck c -> can_get_stuck c
| stuck_later : forall c e c', step c e c' -> can_get_stuck c' -> can_get_stuck c.

Inductive can_ev_loop_silent : cfg -> Prop :=
| silent_now : forall c, can_loop_silent c -> can_ev_loop_silent c
| silent_later : forall c e c', step c e c' -> can_ev_loop_silent c' -> can_ev_loop_silent c.

Lemma not_can_get_stuck_not_stuck : forall c, ~ can_get_stuck c -> ~ stuck c.
Proof.
  intros c H. intros Hn. apply H. now constructor.
Qed.

Lemma can_get_stuck_steps' : forall c m c', steps' c m c' -> can_get_stuck c' -> can_get_stuck c.
Proof.
  intros c m c' H. induction H; intros.
  - eauto.
  - specialize (IHsteps' H2).
    apply stuck_later with (e := e) (c' := c'); eauto.
  - specialize (IHsteps' H2).
    apply stuck_later with (e := e) (c' := c'); eauto.
Qed.

Lemma not_can_get_stuck_steps' : forall c m c', steps' c m c' -> ~ can_get_stuck c -> ~ can_get_stuck c'.
  intros c m c' H.
  apply contra. rewrite <- dne. rewrite <- dne. eapply can_get_stuck_steps'; eassumption.
Qed.


Lemma not_can_ev_loop_silent : forall c, ~ can_ev_loop_silent c -> ~ can_loop_silent c.
Proof.
  intros c H. intros Hn. apply H. now constructor.
Qed.

Lemma can_ev_loop_silent_steps' : forall c m c', steps' c m c' -> can_ev_loop_silent c' ->
                                            can_ev_loop_silent c.
Proof.
  intros c m c' H. induction H; intros.
  - eauto.
  - specialize (IHsteps' H2).
    apply silent_later with (e := e) (c' := c'); eauto.
  - specialize (IHsteps' H2).
    apply silent_later with (e := e) (c' := c'); eauto.
Qed.

Lemma not_can_ev_loop_silent_steps' : forall c m c', steps' c m c' -> ~ can_ev_loop_silent c ->
                                                ~ can_ev_loop_silent c'.
  intros c m c' H.
  apply contra. rewrite <- dne. rewrite <- dne. eapply can_ev_loop_silent_steps'; eassumption.
Qed.

CoFixpoint stream_of (c : cfg) (H1 : ~ can_get_stuck c) (H2 : ~ can_ev_loop_silent c) : @stream event.
  assert (Hnstuck : ~ stuck c) by now apply not_can_get_stuck_not_stuck.
  do 2 setoid_rewrite not_forall_ex_not in Hnstuck.
  apply indefinite_description in Hnstuck. destruct Hnstuck as [e H].
  apply indefinite_description in H. destruct H as [c' H].
  apply NNPP in H.

  destruct (classicT (silent e)) as [He | He].
  - assert (Hnsilent : ~ can_loop_silent c) by now apply not_can_ev_loop_silent.
    apply not_can_loop_silent' in Hnsilent.
    unfold does_event_or_goes_wrong' in Hnsilent.
    apply indefinite_description in Hnsilent. destruct Hnsilent as [m Hnsilent].
    apply indefinite_description in Hnsilent. destruct Hnsilent as [c'' [Hc''1 Hc''2]].
    assert (Hm : exists e' p', m = e' :: p').
    { destruct m as [| e' p'].
      - destruct Hc''2. exfalso.
        apply H1. apply can_get_stuck_steps' with (m := []) (c' := c'').
        assumption. now constructor. congruence.
      - now (exists e', p'). }
    apply indefinite_description in Hm. destruct Hm as [e' Hm].
    apply indefinite_description in Hm. destruct Hm as [p' Heq]. subst.
    apply steps'_cons in Hc''1.
    apply indefinite_description in Hc''1. destruct Hc''1 as [c'0 Hc''1].
    destruct Hc''1 as [Hc''11 Hc''12].
    assert (H2' : ~ can_ev_loop_silent c'0)
      by now apply not_can_ev_loop_silent_steps' with (c := c) (m := [e']).
    assert (H1' : ~ can_get_stuck c'0)
      by now apply not_can_get_stuck_steps' with (c := c) (m := [e']).
    exact (app_list_stream [e'] (stream_of c'0 H1' H2')).
  - assert (H1' : ~ can_get_stuck c').
    apply not_can_get_stuck_steps' with (c := c) (m := [e]); eauto.
    assert (H2' : ~ can_ev_loop_silent c').
    apply not_can_ev_loop_silent_steps' with (c := c) (m := [e]); eauto.
    exact (app_list_stream [e] (stream_of c' H1' H2')).
Defined.

(* cf CPDT *)
Definition frob (s : @stream event) : stream :=
  match s with
  | scons e s' => scons e s'
  end.

Theorem frob_eq : forall s, s = frob s.
  destruct s; reflexivity.
Qed.

Lemma stream_of_eta : forall (c : cfg) (H1 : ~ can_get_stuck c) (H2 : ~ can_ev_loop_silent c),
    stream_of c H1 H2 = let Hnstuck : ~ stuck c := not_can_get_stuck_not_stuck c H1 in
  let Hnstuck0 :=
    indefinite_description event (fun n : event => exists n0 : cfg, ~ ~ step c n n0)
      (Morphisms.subrelation_proper Morphisms_Prop.ex_iff_morphism tt
         (Morphisms.subrelation_respectful
            (Morphisms.subrelation_refl (Morphisms.pointwise_relation event iff))
            Morphisms.iff_impl_subrelation) (fun n : event => ~ (forall c' : cfg, ~ step c n c'))
         (fun n : event => exists n0 : cfg, ~ (fun n1 : cfg => ~ step c n n1) n0)
         (fun n : event => not_forall_ex_not cfg (fun n0 : cfg => ~ step c n n0))
         (Morphisms.iff_impl_subrelation
            (~ (forall n : event, (fun n0 : event => forall c' : cfg, ~ step c n0 c') n))
            (exists n : event, ~ (fun n0 : event => forall c' : cfg, ~ step c n0 c') n)
            (not_forall_ex_not event (fun n : event => forall c' : cfg, ~ step c n c')) Hnstuck)) in
  let (e, H) := Hnstuck0 in
  let H0 := indefinite_description cfg (fun n : cfg => ~ ~ step c e n) H in
  let (c', H3) := H0 in
  let H4 : step c e c' := NNPP (step c e c') H3 in
  let s := classicT (silent e) in
  match s with
  | left _ =>
      let Hnsilent : ~ can_loop_silent c := not_can_ev_loop_silent c H2 in
      let Hnsilent0 : does_event_or_goes_wrong' c := not_can_loop_silent' c Hnsilent in
      let Hnsilent1 :=
        indefinite_description (list event)
          (fun m : list event => exists c'0 : cfg, steps' c m c'0 /\ (stuck c'0 \/ m <> [])) Hnsilent0
        in
      let (m, Hnsilent2) := Hnsilent1 in
      let Hnsilent3 :=
        indefinite_description cfg (fun c'0 : cfg => steps' c m c'0 /\ (stuck c'0 \/ m <> []))
          Hnsilent2 in
      let (c'', a) := Hnsilent3 in
      match a with
      | conj Hc''1 Hc''2 =>
          let Hm : exists (e' : event) (p' : list event), m = e' :: p' :=
            match
              m as l
              return
                (steps' c l c'' ->
                 stuck c'' \/ l <> [] -> exists (e' : event) (p' : list event), l = e' :: p')
            with
            | [] =>
                fun (Hc''3 : steps' c [] c'') (Hc''4 : stuck c'' \/ [] <> []) =>
                match Hc''4 with
                | or_introl H5 =>
                    False_ind (exists (e' : event) (p' : list event), [] = e' :: p')
                      (H1 (can_get_stuck_steps' c [] c'' Hc''3 (stuck_now c'' H5)))
                | or_intror H5 =>
                    let Heq : [] = [] := eq_refl in
                    False_ind (exists (e' : event) (p' : list event), [] = e' :: p') (H5 Heq)
                end
            | e' :: p' =>
                fun (_ : steps' c (e' :: p') c'') (_ : stuck c'' \/ e' :: p' <> []) =>
                ex_intro (fun e'0 : event => exists p'0 : list event, e' :: p' = e'0 :: p'0) e'
                  (ex_intro (fun p'0 : list event => e' :: p' = e' :: p'0) p' eq_refl)
            end Hc''1 Hc''2 in
          let Hm0 :=
            indefinite_description event (fun e' : event => exists p' : list event, m = e' :: p') Hm
            in
          let (e', Hm1) := Hm0 in
          let Hm2 := indefinite_description (list event) (fun p' : list event => m = e' :: p') Hm1 in
          let (p', Heq) := Hm2 in
          eq_rec_r (fun m0 : list event => steps' c m0 c'' -> stuck c'' \/ m0 <> [] -> stream)
            (fun (Hc''3 : steps' c (e' :: p') c'') (_ : stuck c'' \/ e' :: p' <> []) =>
             let Hc''5 : exists c''0 : cfg, steps' c [e'] c''0 /\ steps' c''0 p' c'' :=
               steps'_cons c c'' e' p' Hc''3 in
             let Hc''6 :=
               indefinite_description cfg (fun c''0 : cfg => steps' c [e'] c''0 /\ steps' c''0 p' c'')
                 Hc''5 in
             let (c'0, Hc''7) := Hc''6 in
             match Hc''7 with
             | conj Hc''11 _ =>
                 let H2' : ~ can_ev_loop_silent c'0 :=
                   not_can_ev_loop_silent_steps' c [e'] c'0 Hc''11 H2 in
                 let H1' : ~ can_get_stuck c'0 := not_can_get_stuck_steps' c [e'] c'0 Hc''11 H1 in
                 app_list_stream [e'] (stream_of c'0 H1' H2')
             end) Heq Hc''1 Hc''2
      end
  | right He =>
      let H1' : ~ can_get_stuck c' :=
        not_can_get_stuck_steps' c [e] c' (SSCons c e c' [] c' H4 He (steps'_refl c')) H1 in
      let H2' : ~ can_ev_loop_silent c' :=
        not_can_ev_loop_silent_steps' c [e] c' (SSCons c e c' [] c' H4 He (steps'_refl c')) H2 in
      app_list_stream [e] (stream_of c' H1' H2')
  end.
Proof.
  intros c H1 H2.
  rewrite (frob_eq (stream_of c H1 H2)).
  simpl.
  destruct (indefinite_description event (fun n : event => exists n0 : cfg, ~ ~ step c n n0)
         (Morphisms.subrelation_proper Morphisms_Prop.ex_iff_morphism tt
            (Morphisms.subrelation_respectful
               (Morphisms.subrelation_refl (Morphisms.pointwise_relation event iff))
               Morphisms.iff_impl_subrelation) (fun n : event => ~ (forall c' : cfg, ~ step c n c'))
            (fun n : event => exists n0 : cfg, ~ ~ step c n n0)
            (fun n : event => not_forall_ex_not cfg (fun n0 : cfg => ~ step c n n0))
            (Morphisms.iff_impl_subrelation (~ (forall (n : event) (c' : cfg), ~ step c n c'))
               (exists n : event, ~ (forall c' : cfg, ~ step c n c'))
               (not_forall_ex_not event (fun n : event => forall c' : cfg, ~ step c n c'))
               (not_can_get_stuck_not_stuck c H1)))).
  destruct (indefinite_description cfg (fun n : cfg => ~ ~ step c x n) e).
  destruct (classicT (silent x)).
  destruct (indefinite_description (list event)
         (fun m : list event => exists c'0 : cfg, steps' c m c'0 /\ (stuck c'0 \/ m <> []))
         (not_can_loop_silent' c (not_can_ev_loop_silent c H2))).
  destruct (indefinite_description cfg (fun c'0 : cfg => steps' c x1 c'0 /\ (stuck c'0 \/ x1 <> [])) e0).
  destruct a.
  destruct (indefinite_description event (fun e' : event => exists p' : list event, x1 = e' :: p')
         (match
            x1 as l
            return
              (steps' c l x2 ->
               stuck x2 \/ l <> [] -> exists (e' : event) (p' : list event), l = e' :: p')
          with
          | [] =>
              fun (Hc''3 : steps' c [] x2) (Hc''4 : stuck x2 \/ [] <> []) =>
              match Hc''4 with
              | or_introl H5 =>
                  False_ind (exists (e' : event) (p' : list event), [] = e' :: p')
                    (H1 (can_get_stuck_steps' c [] x2 Hc''3 (stuck_now x2 H5)))
              | or_intror H5 =>
                  False_ind (exists (e' : event) (p' : list event), [] = e' :: p') (H5 eq_refl)
              end
          | e' :: p' =>
              fun (_ : steps' c (e' :: p') x2) (_ : stuck x2 \/ e' :: p' <> []) =>
              ex_intro (fun e'0 : event => exists p'0 : list event, e' :: p' = e'0 :: p'0) e'
                (ex_intro (fun p'0 : list event => e' :: p' = e' :: p'0) p' eq_refl)
           end s0 o)).
  destruct (indefinite_description (list event) (fun p' : list event => x1 = x3 :: p') e1).
  unfold eq_rec_r. unfold eq_rec. unfold eq_rect. subst. simpl.
  destruct (indefinite_description cfg (fun c''0 : cfg => steps' c [x3] c''0 /\ steps' c''0 x4 x2)
                                   (steps'_cons c x2 x3 x4 s0)).
  destruct a.
  reflexivity. reflexivity.
Qed.


Definition trace_of (c : cfg) : exists (t : trace), sem' c t.
Proof.
  destruct (classicT (can_get_stuck c)) as [H | H].
  - induction H.
    + exists (tstop nil (es_of_cfg c H)).
      econstructor. econstructor.
    + destruct (classicT (silent e)); destruct IHcan_get_stuck as [t Ht].
      * exists t. inversion Ht; subst. destruct (order_inf a) as [a' Haa'].
        apply (sem'_cons a').
        apply SAppNilN with (a2 := a) (c' := c'); eauto.
      * exists (tapp (ftbd [e]) t). inversion Ht; subst.
        destruct (order_inf a) as [a' Haa'].
        apply (sem'_cons a').
        apply SAppN with (a2 := a) (c' := c'); eauto. congruence.
  - destruct (classicT (can_ev_loop_silent c)) as [Hc | Hc].
    + induction Hc.
      * exists (tsilent nil). econstructor; constructor; assumption.
      * assert (H': ~ can_get_stuck c') by (intros Hn; apply H; eapply stuck_later; eauto).
        destruct (IHHc H') as [t Ht].
        destruct (classicT (silent e)).
        -- inversion Ht; subst.
           destruct (order_inf a) as [a' Ha].
           exists t. econstructor. eapply SAppNilN with (c' := c').
           econstructor; eauto. apply Ha. assumption.
        -- inversion Ht; subst.
           exists (tapp (ftbd [e]) t).
           econstructor. eapply SAppN with (c' := c').
           congruence. eauto.  apply H1.
    + exists (tstream (stream_of c H Hc)).
      admit.
      Unshelve.
      exact an_A. exact an_A. exact an_A.
Admitted.


Lemma non_empty_sem : forall W, exists t, sem W t.
Proof. intro W. apply (trace_of (init W)).
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
  sem' c (tapp (ftbd [e]) t).
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
    sem'_N a c (tapp (ftbd [e]) t).
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
    induction H7; subst; try now eauto.
    + simpl in *. econstructor. now constructor.
    + specialize (IHsteps' H6).
      assert (steps c' (fstop m (es_of_cfg c'' H6)) c'').
      constructor. assumption.
      specialize (IHsteps' H4 H0 H6).
      inversion IHsteps'; subst; eauto.
      simpl in *. econstructor.
      assert (Hrewrite :
                (tstop (e :: m) (es_of_cfg c'' H6)) = tapp (ftbd [e]) (tstop m (es_of_cfg c'' H6))).
      { simpl. reflexivity. }
      rewrite Hrewrite.
      eapply SAppN with (m := [e]) (c' := c'); eauto.
      congruence.
  - inversion H0; subst; eauto.
    destruct (order_inf a) as [a' Ha'].
    apply sem'_cons with (a := a').
    destruct l as [| e' p'].
    inversion H; subst. econstructor; eauto. destruct t; eauto.
    eapply SAppN with (m := e' :: p'); eauto. congruence. inversion H; subst. assumption.
    Unshelve.
    assumption. exact an_A. exact an_A.
Qed.

Lemma steps_psem : forall P m c,
  steps (init P) m c ->
  @psem lang P m.
Proof.
  intros P m c Hsteps.
  unfold psem. simpl.
  destruct (trace_of c) as [t Ht].
  exists (tapp m t). split.
  - destruct m.
    + inversion Hsteps; subst.
      apply tapp_pref.
    + unfold sem.
      inversion Hsteps; subst.
      inversion H1; subst.
      ++ now destruct t.
      ++ apply tapp_pref.
      ++ apply tapp_pref.
  - unfold sem.
    eapply steps_sem'_app. eassumption.
    now apply Ht.
Qed.

Definition fstopped (m : finpref) :=
  match m with
  | fstop _ _ => true
  | _ => false
  end.

Lemma sem'_prefix : forall m c0 t,
  sem' c0 t ->
  prefix m t ->
  fstopped m = false ->
  exists c, steps c0 m c.
Proof.
  induction finpref m as e es p IHp; intros c0 t Hsem Hpref Hnstopped.
  - inversion Hnstopped.
  - inversion Hnstopped.
  - exists c0. constructor. apply SSTbd.
  - destruct t as [l es | l | s]; simpl in *.
    + destruct l as [| e' p']. inversion Hpref.
      destruct Hpref as [H Hpref]; subst.
      assert (Hre : tstop (e' :: p') es = tapp (ftbd [e']) (tstop p' es)) by reflexivity.
      rewrite Hre in Hsem.
      apply sem'_tapp in Hsem.
      destruct Hsem as [c' [H1 H2]].
      specialize (IHp c' (tstop p' es) H2 Hpref Hnstopped).
      destruct IHp as [c'' Hc''].
      exists c''. constructor.
      inversion Hc''; subst.
      apply steps'_trans with (m := [e']) (m' := p) (c2 := c'); eauto.
    + destruct l as [| e' p']. inversion Hpref.
      destruct Hpref as [H Hpref]; subst.
      assert (Hre : tsilent (e' :: p') = tapp (ftbd [e']) (tsilent p')) by reflexivity.
      rewrite Hre in Hsem.
      apply sem'_tapp in Hsem.
      destruct Hsem as [c' [H1 H2]].
      specialize (IHp c' (tsilent p') H2 Hpref Hnstopped).
      destruct IHp as [c'' Hc''].
      exists c''. constructor.
      inversion Hc''; subst.
      apply steps'_trans with (m := [e']) (m' := p) (c2 := c'); eauto.
    + destruct s as [ e' s']. destruct Hpref as [H Hpref]; subst.
      assert (Hre : tstream (scons e' s') = tapp (ftbd [e']) (tstream s')) by reflexivity.
      rewrite Hre in Hsem.
      apply sem'_tapp in Hsem.
      destruct Hsem as [c' [H1 H2]].
      specialize (IHp c' (tstream s') H2 Hpref Hnstopped).
      destruct IHp as [c'' Hc''].
      exists c''. constructor.
      inversion Hc''; subst.
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

Definition fsnoc (m : finpref) (e : event) : finpref :=
  match m with
  | fstop m' es => fstop (snoc m' e) es
  | ftbd m' => ftbd (snoc m' e)
  end.

Theorem finpref_ind_snoc :
  forall (P : finpref -> Prop),
    P (ftbd nil) ->
    (forall (m : list event) (es : endstate), P (fstop m es)) ->
    (forall (m : finpref) (e : event), P m -> P (fsnoc m e)) ->
    forall m, P m.
Proof.
  (* Proof similar to list_rev_ind in the Coq library *)
  intros P H H0 H1 m.
  destruct m; eauto.
  rewrite <- (@rev_involutive event l).
  induction (rev l).
  apply H.
  simpl.
  assert (forall l, l ++ [a] = snoc l a).
  { clear.
    induction l. now simpl.
    simpl in *. rewrite IHl. reflexivity. }
  specialize (H2 (rev l0)). rewrite H2.
  specialize (H1 (ftbd (rev l0)) a IHl0). assumption.
Qed.

(* Lemma not_diverges_cons : forall e t, ~ diverges (tcons e t) -> ~ diverges t. *)
(*   intros e t H Hn. *)
(*   apply H. now constructor. *)
(* Qed. *)

Definition configuration_determinacy := forall (c c1 c2 : cfg) (m : list event),
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

Definition rel_cfg_pref (c1 c2 : cfg) : Prop := forall (m : list event),
    (exists c1', steps' c1 m c1') <-> (exists c2', steps' c2 m c2').

Lemma steps'_to_sem'_N_pref : forall c c' m,
    steps' c m c' ->
    exists t a, prefix (ftbd m) t /\ sem'_N a c t.
Proof.
  intros c c' m H.
  induction H.
  - pose proof (trace_of c).
    destruct H as [t Ht].
    inversion Ht; subst.
    exists t, a.
    split; simpl; destruct t; eauto.
  - destruct IHsteps' as [t' [a [H2 H3]]].
    exists (tapp (ftbd [e]) t'). exists a. split. simpl. destruct t'; eauto.
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
    + destruct l; inversion H; subst.
      assert (Hre: tstop (e0 :: l) e = tapp (ftbd [e0]) (tstop l e)) by reflexivity.
      rewrite Hre in H0.
      apply sem'_N_tapp in H0.
      destruct H0 as [c' [a' [H0 H1]]].
      specialize (IHm c' (tstop l e) a' H2 H1).
      destruct IHm as [c'0 H3].
      exists c'0; eapply steps'_trans with (m := [e0]) (m' := m); eassumption.
    + destruct l; inversion H; subst.
      assert (Hre: tsilent (e :: l) = tapp (ftbd [e]) (tsilent l )) by reflexivity.
      rewrite Hre in H0.
      apply sem'_N_tapp in H0.
      destruct H0 as [c' [a' [H0 H1]]].
      specialize (IHm c' (tsilent l) a' H2 H1).
      destruct IHm as [c'0 H3].
      exists c'0; eapply steps'_trans with (m := [e]) (m' := m); eassumption.
    + destruct s; inversion H; subst.
      assert (Hre: tstream (scons e s) = tapp (ftbd [e]) (tstream s)) by reflexivity.
      rewrite Hre in H0.
      apply sem'_N_tapp in H0.
      destruct H0 as [c' [a' [H0 H1]]].
      specialize (IHm c' (tstream s) a' H2 H1).
      destruct IHm as [c'0 H3].
      exists c'0; eapply steps'_trans with (m := [e]) (m' := m); eassumption.
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

Definition weak_determinacy := forall (c1 c1' c2 c2' : cfg) (m : list event),
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

Definition stopped (t : trace) : Prop :=
  match t with
  | tstop _ _ => True
  | _ => False
  end.

Lemma ind_hyp (det : weak_determinacy) : forall t c,
    ~ diverges t -> ~ stopped t ->
    (forall m, prefix (ftbd m) t -> exists c', steps' c m c') ->
    sem' c t.
Proof.
  intros.
  apply sem'_cons with (a := an_A).
  generalize dependent an_A.
  generalize dependent t. generalize dependent c.
  cofix ind_hyp. intros c t Hndiv Hnstopped H a.
  destruct t as [| | [e s']].
  - apply False_ind. apply Hnstopped. now constructor.
  - apply False_ind. apply Hndiv. now constructor.
  - assert (Hsilent: ~silent e).
    { specialize (H [e]).
      assert (prefix (ftbd [e]) (tstream  (scons e s'))) by now simpl.
      specialize (H H0). destruct H as [c' Hc'].
      eapply steps'_not_silent; now eauto.
    }
    pose proof H as H'.
    assert (H1: prefix (ftbd [e]) (tstream (scons e s'))) by now split.
    specialize (H' [e] H1); clear H1. destruct H' as [c' Hc'].
    destruct (order_inf a) as [a1 Ha1].
    assert (Hre : tstream (scons e s') = tapp (ftbd [e]) (tstream s')) by reflexivity.
    rewrite Hre.
    apply SAppN with (c' := c') (m := [e]) (a2 := a1).
    congruence.
    (* apply steps'_sem'_N with (c' := c'). *)
    assumption.
    assert (Hndiv' : ~ diverges (tstream s')).
    { intros Hn; apply Hndiv; eauto. }
    assert (Hnstopped' : ~ stopped (tstream s')).
    { intros Hn; apply Hnstopped; eauto. }
    Guarded.
    apply ind_hyp; try now assumption.
    Guarded.
    intros m H0.
    assert (H': prefix (ftbd (e :: m)) (tstream (scons e s'))) by now split.
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
  destruct t as [| | s].
  - assert (Ht: e = e /\ l = l) by (split; reflexivity).
    specialize (H (fstop l e) Ht). unfold psem in H.
    destruct H as [t [H1 H2]].
    destruct t; simpl in *; subst; now eauto.
  - exfalso. apply Hndiv. now constructor.
  - (* remember (tcons e0 t0) as t. *)
    apply ind_hyp.
    apply det.
    apply Hndiv.
    apply Hnstopped.
    intros m H'.
    specialize (H (ftbd m) H').
    apply psem_steps in H; [| reflexivity].
    destruct H as [c2 H].
    simpl in H.
    exists c2.
    now inversion H.
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
    intros H. now assumption. }
  specialize (Hinf (Hstopinf Hstopped)). now contradiction.
  pose proof (semantics_safety_like_right det t P Hndiv Hnstopped).
  rewrite -> contra in H.
  specialize (H Hsem). apply not_all_ex_not in H.
  destruct H as [m Hm]. rewrite not_imp in Hm. destruct Hm as [Hm1 Hm2].
  generalize dependent Hm2. generalize dependent Hm1.
  destruct m as [p | p].
  - (* fstop *)
    intros Hm1 Hm2.
    assert (forall t m es, prefix (fstop m es) t -> fin t).
    { clear. intros t m. generalize dependent t. induction m; intros t es H.
      - destruct t; try now auto.
      - destruct t; try now auto. }
    unfold inf in Hinf. exfalso; apply Hinf. now apply (H t p es Hm1).
  - (* ftbd *)
    induction p as [| p' e' IH] using list_ind_snoc; intros Hm1 Hm2.
    + (* p = nil *)
      assert (Hm2' : @psem lang P (ftbd nil)).
      { clear. unfold psem. pose proof non_empty_sem P. destruct H as [t Ht].
        exists t; split. now destruct t. assumption. }
      now contradiction.
    + (* p = snoc p' e' *)
      pose proof (classic (@psem lang P (ftbd p'))) as [H | H].
      ++ exists p', e'. subst. split; try split; assumption.
      ++ apply IH.
         assert (H0: forall (p : list event) e t, prefix (ftbd (snoc p e)) t -> prefix (ftbd p) t).
         { clear. induction p.
           - intros. now destruct t.
           - intros. simpl in *. destruct t; try now auto.
             destruct l; try now auto.
             destruct H as [H1 H2].
             split. assumption.
             now specialize (IHp e (tstop l e0) H2).
             destruct l; try now auto.
             destruct H as [H1 H2].
             split. assumption.
             now specialize (IHp e (tsilent l) H2).
             destruct s; try now auto.
             destruct H as [H1 H2].
             split. assumption.
             now specialize (IHp e (tstream s) H2).
         }
         apply H0 in Hm1. assumption.
         assumption.
Qed.

End SmallSteps.
