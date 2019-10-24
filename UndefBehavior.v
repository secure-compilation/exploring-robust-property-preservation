Require Import ClassicalExtras.

Require Import TraceModel.
Require Import Stream.
Require Import Properties.
Require Import Galois.

Require Import FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".


Section UndefBehavior.
  Variable event : Events.

  Variable endstate : Endstates.

  Definition endstateT : Endstates := endstate.

  Definition undef := unit.
  Definition endstateS : Endstates :=
    {| es := (es endstate + undef);
       an_es := inr tt
    |}.
  Definition UB : es endstateS := inr tt.
  Hint Unfold UB.

  Definition traceS := @trace event endstateS.
  Definition traceT := @trace event endstateT.
  Definition finprefS := @finpref event endstateS.
  Definition finprefT := @finpref event endstateT.

  Definition propS := @prop traceS.
  Definition propT := @prop traceT.
  Definition fpropS := @fprop event endstateS.
  Definition fpropT := @fprop event endstateT.

  Inductive syntactic_eq : traceS -> traceT -> Prop :=
  | syntactic_eq_tstop : forall l e,
      syntactic_eq (tstop l (inl e : es endstateS)) (tstop l e)
  | syntactic_eq_tsilent : forall l,
      syntactic_eq (tsilent l) (tsilent l)
  | syntactic_eq_tstream : forall s,
      syntactic_eq (tstream s) (tstream s)
  .
  Notation "t__s '≡' t__t" := (syntactic_eq t__s t__t) (no associativity, at level 10).
  Hint Constructors syntactic_eq.

  Definition prefixST (m__s : finprefS) (t__t : traceT) : Prop :=
    match m__s with
    | fstop l__t (inl e__t) =>
      match t__t with
      | tstop l__s e__s => e__t = e__s /\ l__t = l__s
      | _ => False
      end
    | fstop _ (inr _) => False
    | ftbd l__t =>
      match t__t with
      | tstop l__s _ | tsilent l__s => Stream.list_list_prefix l__t l__s
      | tstream s__s => Stream.list_stream_prefix l__t s__s
      end
    end.

  Definition rel : traceS -> traceT -> Prop :=
    fun t__s t__t => t__s ≡ t__t \/ exists m, (t__s = tstop m UB /\ prefixST (ftbd m) t__t).
  Hint Unfold rel.

  Inductive syntactic_eq_finpref : finprefS -> finprefT -> Prop :=
  | syntactic_eq_fstop : forall l e,
      syntactic_eq_finpref (fstop l (inl e : es endstateS)) (fstop l e)
  | syntactic_eq_ftbd : forall l,
      syntactic_eq_finpref (ftbd l) (ftbd l)
  .

  (* Definition rel_finpref : finprefS -> finprefT -> Prop := *)
  (*   fun m__s m__t => syntactic_eq_finpref m__s m__t \/ exists l, (m__t = fstop l OOM /\ prefix_finpref (ftbd l) m__s). *)

  Definition GC_traceT_traceS : Galois_Connection traceT traceS :=
    induced_connection rel.

  Definition τ : propS -> propT := α GC_traceT_traceS.
  Lemma τ_def : forall πS t__t,
      (τ πS) t__t <-> (exists t__s, t__s ≡ t__t /\ πS t__s) \/ (exists m, prefixST (ftbd m) t__t /\ πS (tstop m UB)).
  Proof.
    intros πS t__t.
    unfold τ, GC_traceT_traceS, induced_connection, low_rel; simpl.
    split.
    - intros H.
      destruct H as [t__s [H1 H2]].
      destruct H2 as [H2 | H2].
      + left; eexists; split; eauto.
      + destruct H2 as [m [H2 H3]]; subst.
        right.
        eexists; split; try split; eauto.
    - intros H.
      destruct H as [[t__s [H1 H2]] | [m [H2 H3]]].
      + eexists; split; eauto.
      + eexists; split; eauto.
  Qed.

  Definition σ : propT -> propS := γ GC_traceT_traceS.

  Lemma σ_def : forall πT t__s,
      (σ πT) t__s <-> (forall t__t, t__s ≡ t__t -> πT t__t) /\ (forall t__t m, t__s = tstop m UB -> (prefixST (ftbd m) t__t -> πT t__t)).
  Proof.
    intros πT t__s.
    unfold σ, GC_traceT_traceS, induced_connection, up_rel; simpl.
    split.
    - intros H.
      split.
      + eauto.
      + intros t__t m H0 H1; subst.
        apply H.
        right.
        exists m. split; auto.
    - intros H x Hrel.
      destruct H as [H1 H2].
      inversion Hrel.
      + eauto.
      + destruct H as [m [Hm1 Hm2]].
        subst.
        eauto.
  Qed.

  Lemma σ_def' : forall πT t__s,
      (σ πT) t__s <-> (exists t__t, t__s ≡ t__t /\ πT t__t) \/ (exists m, t__s = tstop m UB /\ (forall t__t, prefixST (ftbd m) t__t -> πT t__t)).
  Proof.
    intros πT t__s.
    rewrite σ_def.
    split.
    - intros H. destruct H.
      destruct t__s as [l [e | []] | l | s]; eauto.
    - intros H. destruct H.
      + destruct H as [t__t [Heq H]].
        split.
        * intros t__t0 Heq'.
          assert (t__t = t__t0)
            by now destruct t__s as [l [e | []] | l | s];
            inversion Heq; inversion Heq'.
          now subst.
        * intros t__t0 m H0 H1.
          subst; inversion Heq.
      + destruct H as [m H].
        split.
        * intros t__t Heq.
          destruct H; subst; now inversion Heq.
        * intros t__t m0 H0 H1.
          destruct H; subst; inversion H0; subst.
          now apply H2.
  Qed.

  Lemma τ_preserves_dense : forall (π : propS),
      Dense π -> Dense (τ π).
  Proof.
    unfold Dense, τ, GC_traceT_traceS, induced_connection, low_rel; simpl.
    intros π HDense.
    intros t__t Hfin.
    destruct t__t as [l e | l | s].
    - exists (tstop l (inl e : es endstateS)). split.
      apply HDense. econstructor; eexists; eauto.
      left; eauto.
    - destruct Hfin as [l' [e' Hn]].
      inversion Hn.
    - destruct Hfin as [l' [e' Hn]].
      inversion Hn.
  Qed.

  Lemma σ_does_not_preserve_dense : exists (π : propT),
      Dense π /\ not (Dense (σ π)).
  Proof.
    exists (fun t__t => exists m e, t__t = tstop m e).
    split.
    - unfold Dense.
      intros t Hfin.
      inversion Hfin; now auto.
    - unfold Dense, σ, GC_traceT_traceS, induced_connection, up_rel; simpl.
      intros Hn.
      specialize (Hn (tstop nil UB)).
      assert (finite (tstop (nil : list (ev event)) UB)) by (econstructor; now eauto).
      specialize (Hn H (tsilent nil)).
      assert (rel (tstop nil UB) (tsilent nil)) by (right; eexists; now eauto).
      specialize (Hn H0).
      destruct Hn as [? [? Hn]].
      inversion Hn.
  Qed.

End UndefBehavior.
