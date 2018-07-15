Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.

Section Main.

Variable partial : Set.
Variable program : Set.
Variable context : Set.
Variable plug : partial -> context -> program.
  
Variable cfg : Set.
Variable init : program -> cfg. 
Variable step : cfg -> event -> cfg -> Prop.

Definition stuck (c:cfg) : Prop :=  forall e c', ~step c e c'.

CoInductive sem' : cfg -> trace -> Prop :=
| SStop : forall c, stuck c -> sem' c tstop
| SCons : forall c e c' t, step c e c' -> sem' c' t -> sem' c (tcons e t).

Definition sem (p:program) : trace -> Prop := sem' (init p).

Require Import ClassicalExtras.

Axiom classicT : forall (P : Prop), {P} + {~ P}.
Axiom indefinite_description : forall (A : Type) (P : A->Prop),
   ex P -> sig P.

CoFixpoint trace_of (c:cfg) : trace.
  destruct (classicT (stuck c)) as [H | H]. exact tstop.
  unfold stuck in H. do 2 setoid_rewrite not_forall_ex_not in H.
  apply indefinite_description in H. destruct H as [e H].
  apply indefinite_description in H. destruct H as [c' H].
  apply NNPP in H. eapply (tcons e). apply (trace_of c').
Defined.

(* The usual hack to unfold CoFixpoints, but it ain't pretty and
   it still doesn't compute because of all the axioms *)
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

Definition lang : level := @Build_level partial
                                        program
                                        context
                                        plug
                                        sem
                                        non_empty_sem.

Inductive steps : cfg -> finpref -> cfg -> Prop :=
| SSTbd : forall c, steps c (ftbd nil) c
| SSCons : forall c e c' m c'', step c e c' ->
                                steps c' (ftbd m) c'' ->
                                steps c (ftbd (cons e m)) c''.

Axiom tapp : finpref -> trace -> trace. (* Where have all the flowers gone? *)

Lemma steps_sem' : forall c m c' t,
  steps c m c' ->
  sem' c' t ->
  sem' c (tapp m t).
Admitted.

Lemma steps_psem : forall P m c,
  steps (init P) m c ->
  @psem lang P m.
Proof.
  intros P m c Hsteps.
  unfold psem. simpl. exists (tapp m (trace_of c)). split.
  - admit. (* trivial with a real tapp *)
  - unfold sem. eapply steps_sem'. eassumption. now apply sem'_trace_of.
Admitted.

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
    destruct (IHm c' t' H3 Hpref Hnot_stopped) as [c'' HH].
    exists c''. eapply SSCons; eassumption.
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

Definition semantics_safety_like_right : forall t P,
  (forall m, prefix m t -> @psem lang P m) -> sem P t.
Admitted.

Lemma tgt_sem : semantics_safety_like lang.
Proof.
  unfold semantics_safety_like. simpl.
  intros t P Hsem Hinf.
  (* unfold psem. simpl. *)
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
Admitted.

End Main.
