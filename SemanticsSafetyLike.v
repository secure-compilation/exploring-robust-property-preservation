Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import ClassicalExtras.
Require Import List.
Import ListNotations.

Section Main.

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

Inductive steps' : cfg -> pref -> cfg -> Prop :=
| SSTbd : forall c, steps' c nil c
| SSCons : forall c e c' m c'', step c e c' -> ~silent e -> steps' c' m c'' ->
                                                            steps' c (cons e m) c''
| SSSilent : forall c e c' c'' m, step c e c' -> silent e -> steps' c' m c'' -> steps' c m c''.

Definition steps (c:cfg) (m:finpref) (c':cfg) : Prop :=
  match m with
  | ftbd m' => steps' c m' c'
  | fstop m' => steps' c m' c' /\ stuck c'
  end.

(* must terminate or cause non-silent event ... TODO: but that's not
   what we can easily write, folowing definition may termination *)
Definition cannot_loop_silent (c:cfg) : Prop :=
  forall c', steps' c nil c' -> exists e c'', steps' c' (cons e nil) c''.

Definition does_event_or_goes_wrong (c:cfg) :=
  {exists e c', steps' c (cons e nil) c'} + {exists c', steps' c nil c' /\ stuck c'}.

Lemma not_can_loop_silent : forall c, ~(can_loop_silent c) -> does_event_or_goes_wrong c.
Proof.
  (* intro c. rewrite contra. intro Hc. rewrite <- dne. cofix. -- no longer works with + *)
Admitted.

CoInductive sem' : cfg -> trace -> Prop :=
| SStop : forall c, stuck c -> sem' c tstop
| SCons : forall c e c' t, step c e c' -> ~silent e -> sem' c' t -> sem' c (tcons e t)
| SSilent : forall c e c' t, step c e c' -> silent e -> sem' c' t -> sem' c t
            (* TODO: Q: Do we need to prevent that this applies infinitely for an arbitrary t? Can we prevent it? *)
| SSilentDiv : forall c, can_loop_silent c -> sem' c tsilent.

Definition sem (p:program) : trace -> Prop := sem' (init p).

Axiom classicT : forall (P : Prop), {P} + {~ P}.
Axiom indefinite_description : forall (A : Type) (P : A->Prop),
   ex P -> sig P.

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
Admitted.

CoFixpoint sem'_trace_of (c:cfg) : sem' c (trace_of c).
  rewrite trace_of_eta. destruct (classicT (stuck c)) as [H | H].
  - now eapply SStop.
  - unfold stuck in H. (* rewrite not_forall_ex_not in H. -- strange error *)
    assert (exists (e : event), ~ (forall (c' : cfg), ~ step c e c'))
      as [e H1] by now apply not_forall_ex_not.
    assert (exists c', ~ ~ step c e c') as [c' H2] by now apply not_forall_ex_not.
    clear H1.
    apply NNPP in H2.
Admitted.

Lemma non_empty_sem : forall W, exists t, sem W t.
Proof. intro W. exists (trace_of (init W)). apply sem'_trace_of. Qed.

Definition lang : language := @Build_language partial
                                        program
                                        context
                                        plug
                                        sem
                                        non_empty_sem.


Lemma steps'_sem' : forall c e c' t,
  steps' c [e] c' ->
  sem' c' t ->
  sem' c (tcons e t).
Proof.
Admitted.

Lemma steps_sem' : forall c m c' t,
  steps c m c' ->
  sem' c' t ->
  sem' c (tapp m t).
Proof.
Admitted.

Lemma steps_psem : forall P m c,
  steps (init P) m c ->
  @psem lang P m.
Proof.
  intros P m c Hsteps.
  unfold psem. simpl. exists (tapp m (trace_of c)). split.
  -
Admitted. (* 2018-09-27 Broken when updating definitions
inversion Hsteps.
    + now simpl.
    + subst. apply tapp_pref.
  - unfold sem. eapply steps_sem'. eassumption. now apply sem'_trace_of.
Qed.
*)

Lemma sem'_prefix : forall m c0 t,
  sem' c0 t ->
  prefix m t ->
  fstopped m = false ->
  exists c, steps c0 m c.
Proof.
  destruct m as [m | m]; induction m; intros c0 t Hsem Hpref Hnot_stopped; try inversion Hnot_stopped.
  - exists c0. apply SSTbd.
  - destruct t as [| | e' t']. now inversion Hpref. now inversion Hpref.
    simpl in Hpref. destruct Hpref as [Heq Hpref]. subst e'.
    inversion Hsem. subst. simpl in Hnot_stopped.
    destruct (IHm c' t' H4 Hpref Hnot_stopped) as [c'' HH].
    exists c''. eapply SSCons; eassumption.
Admitted. (* 2018-09-27 Broken when updating definitions
Qed. *)

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

(* CH: ouch, this is actually trivial *)
Definition semantics_safety_like_reverse : forall t P m,
  sem P t ->
  prefix m t ->
  @psem lang P m.
Proof.
  intros t P m H H0. unfold psem. exists t. split; assumption.
Qed.
(* CH: old proof
  intros t P m Hsem Hpref.
  remember (fstopped m) as b. symmetry in Heqb. destruct b.
  - pose proof Heqb as H'.
    apply embed_eq in H'. unfold psem. exists (embedding m). simpl.
    split. apply embed_pref.
    assert (t = embedding m).
      eapply stop_sngle_continuation; eauto. apply embed_pref.
    subst t. assumption.
  - destruct (sem_prefix m P t Hsem Hpref Heqb) as [c Hsteps].
    eapply steps_psem. eassumption.
Qed.
 *)

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
Proof. Admitted.

Lemma not_diverges_cons : forall e t, ~ diverges (tcons e t) -> ~ diverges t.
Admitted.

Lemma steps'_trans : forall c1 c2 c3 m m',
  steps' c1 m c2 -> steps' c2 m' c3 -> steps' c1 (m ++ m') c3.
Admitted.

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
  now firstorder.
Qed.

Lemma rel_cfg_symmetry : forall (c1 c2 : cfg), rel_cfg c1 c2 -> rel_cfg c2 c1.
Proof.
  now firstorder.
Qed.

Definition weak_determinacy := forall (c1 c1' c2 c2' : cfg) (m : pref),
    rel_cfg c1 c1' -> steps' c1 m c2 -> steps' c1' m c2' -> rel_cfg c2 c2'.

(* TODO: Was forced into generalizing the induction hypothesis too much for semantics_safety_like_right:
         - the stronger hypothesis only works if the language is determinate
         - for the purposes of Carmine's proofs that's fine though!*)

Lemma steps'_cons_smaller : forall c1 c3 m e,
    steps' c1 (e :: m) c3 -> exists c2, steps' c1 [e] c2 /\ steps' c2 m c3.
Proof.
  intros c1 c3 m e H.
  remember (e :: m) as p.
  induction H.
  - inversion Heqp.
  - inversion Heqp; subst. clear Heqp.
    exists c'; split. apply SSCons with (c' := c'); auto. constructor. assumption.
  - inversion Heqp; subst. specialize (IHsteps' H2).
    destruct IHsteps' as [c2 [Hc2 Hc2']].
    exists c2. split.
    apply SSSilent with (e := e0) (c' := c'); auto.
    assumption.
Qed.

Inductive stopped : trace -> Prop :=
  | stopped_stop : stopped tstop
  | stopped_cons : forall (e : event) (t : trace), stopped t -> stopped (tcons e t).

Lemma less_general_coinduction_hypothesis (det : very_strong_determinacy) : forall t c,
    ~ diverges t -> ~ stopped t ->
    (forall e m, prefix (ftbd (cons e m)) t -> exists c' c'', steps' c [e] c' /\ steps' c' m c'') ->
    sem' c t.
Proof.
  cofix. intros t c Hndiv Hnstopped H.
  destruct t as [| | e t'].
  - apply False_ind. apply Hnstopped. now constructor.
  - apply False_ind. apply Hndiv. now constructor.
  - assert (~silent e) by admit.
    
    
    (* Try 3 -- Very strong determinacy.
       It works, but maybe too strong. Left to check if it is reasonnable *)
    pose proof H as H'.
    assert (H1: prefix (ftbd [e]) (tcons e t')) by now split.
    specialize (H e [] H1); clear H1; destruct H as [c' [c'' [Hc' Hc'']]].
    apply steps'_sem' with (c' := c').
    assumption.
    assert (Hndiv' : ~ diverges t') by admit.
    assert (Hnstopped' : ~ stopped t') by admit.
    apply less_general_coinduction_hypothesis.
    assumption. assumption.
    intros e0 m Hpref.
    assert (H: prefix (ftbd (e :: e0 :: m)) (tcons e t')) by now split.
    specialize (H' e (e0 :: m) H); clear H.
    destruct H' as [c1 [c2 [Hc1 Hc2]]].
    pose proof (det c c' c1 e e Hc' Hc1) as H.
    destruct H.
    + subst. apply steps'_cons_smaller in Hc2. destruct Hc2 as [c3 [H1 H2]].
      exists c3. exists c2. now split.
    + destruct H as [_ [_ H]]. now contradiction.
      (* Guarded *) (* it's still not guarded. but maybe this is ok, because here at least
                       I can convince myself that something is decreasing, which was not the case
                       in strong coinduction hypothesis *)
Admitted.


Lemma less_general_coinduction_hypothesis' (det : configuration_determinacy): forall t c,
    ~ diverges t -> ~ stopped t ->
    (forall e m, prefix (ftbd (cons e m)) t -> exists c' c'', steps' c [e] c' /\ steps' c' m c'') -> sem' c t.
Proof.
  cofix. intros t c Hndiv Hnstopped H.
  destruct t as [| | e t'].
  - apply False_ind. apply Hnstopped. now constructor.
  - apply False_ind. apply Hndiv. now constructor.
  - assert (~silent e) by admit.
    
    
    (* Try 2 -- configuration determinacy -- 
       Still not enough??? the configuration determinacy seems to be not strong
       enough to prove this... but maybe I missed something? *)
    pose proof H as H'.
    assert (H1: prefix (ftbd [e]) (tcons e t')) by now split.
    specialize (H e [] H1); clear H1; destruct H as [c' [c'' [Hc' Hc'']]].
    apply steps'_sem' with (c' := c').
    assumption.
    assert (Hndiv' : ~ diverges t') by admit.
    assert (Hnstopped' : ~ stopped t') by admit.
    apply less_general_coinduction_hypothesis'.
    assumption. assumption.
    intros e0 m Hpref.
    assert (H: prefix (ftbd (e :: e0 :: m)) (tcons e t')) by now split.
    specialize (H' e (e0 :: m) H); clear H.
    destruct H' as [c1 [c2 [Hc1 Hc2]]].
    pose proof (det c c' c1 [e] Hc' Hc1) as H.
    destruct H.
    + apply steps'_cons_smaller in Hc2. destruct Hc2 as [c3 [Hc1c3 Hc3c2]].
      exists c3. exists c2. split.
      apply steps'_trans with (c2 := c1) (m := []); assumption.
      assumption.
    + apply steps'_cons_smaller in Hc2. destruct Hc2 as [c3 [Hc1c3 Hc3C2]].
Admitted.



(* (* Try 1 -- Bad *) *)
(* pose proof H as H'. *)
(* specialize (H e []). *)
(* assert (Hpref: prefix (ftbd [e]) (tcons e t')) by now split. *)
(* specialize (H Hpref). *)
(* destruct H as [c' [c'' [H1 H2]]]. *)
(* assert (Hndiv' : ~ diverges t') by admit. *)
(* assert (Hnstopped' : ~ stopped t') by admit. *)
(* specialize (less_general_coinduction_hypothesis t' c'). (* need to apply to c' to make progress *) *)
(* specialize (less_general_coinduction_hypothesis Hndiv' Hnstopped'). *)
(* assert (forall (e : event) (m : list event), *)
(*            prefix (ftbd (e :: m)) t' -> *)
(*            exists c1 c2 : cfg, steps' c' [e] c1 /\ steps' c1 m c2). *)
(* { *)
(*   intros e0 m He0m. *)
(*   specialize (H' e (e0 :: m)). *)
(*   assert (forall m t e, prefix (ftbd m) t -> prefix (ftbd (e :: m)) (tcons e t)). *)
(*   { clear. *)
(*     intros m t e H. *)
(*     now split. } *)
(*   specialize (H' (H (e0 :: m) t' e He0m)). *)
(*   clear H. *)
(*   destruct H' as [c1 [c2 [Hc1 Hc2]]]. *)
(*   apply steps'_cons_smaller in Hc2. *)
(*   destruct Hc2 as [c3 [Hc31 Hc32]]. *)
(*   pose proof (det c c' c1 [e] H1 Hc1). *)
(*   destruct H as [H | H]. *)
(*   - exists c3, c2. split. apply steps'_trans with (c2 := c1) (m := []) (m' := [e0]). *)
(*     assumption. assumption. assumption. *)
(*   - exists  *)
(*   (* steps c [e] c1, steps c [e] c', but no steps c' [e0] c3 *) *)
(*   (* can't prove that :( *) *)
(*   admit. *)
(* } *)
(* admit. *)

(* The original semantics_safety_like_right can only be obtained if we assume determinacy *)
Lemma semantics_safety_like_right (det : very_strong_determinacy): forall t P,
  ~ diverges t -> ~ stopped t -> 
  (forall m, prefix m t -> @psem lang P m) -> sem P t.
Proof.
  (* intros t P Hndiv H. apply too_general_coinduction_hypothesis. apply Hndiv. *)
  (* intros m1 m2 c H0 H1. specialize (H (ftbd (m1++m2)) H0). *)
  (* apply psem_steps in H; [| reflexivity]. destruct H as [c' H]. exists c'. *)
  intros t P Hndiv Hnstopped H.
  destruct t as [| | e0 t0].
  - specialize (H (fstop nil) I). unfold psem in H.
    destruct H as [t [H1 H2]].
    now destruct t.
  - exfalso. apply Hndiv. now constructor.
  - remember (tcons e0 t0) as t.
    apply less_general_coinduction_hypothesis.
    apply det.
    apply Hndiv.
    apply Hnstopped.
    intros e m H'.
    specialize (H (ftbd (e :: m)) H').
    apply psem_steps in H; [| reflexivity].
    destruct H as [c2 H].
    simpl in H.
    apply (steps'_cons_smaller (init P) c2 m e) in H.
    destruct H as [c3 [Hc3 Hc3']].
    exists c3, c2. split; assumption.
Qed.

Lemma tgt_sem (det : very_strong_determinacy) :semantics_safety_like lang.
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

End Main.
