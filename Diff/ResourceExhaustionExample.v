Require Import LanguageModel.
Require Import ChainModel.
Require Import NonRobustTraceCriterion.
Require Import TypeRelationExample.
Require Import ResourceExhaustion.
Require Import TraceModel.
Require Import NonRobustTraceCriterion.
(* Careful: we should make sure to not mix the definition between TypeRelationExample and this file *)


Set Bullet Behavior "Strict Subproofs".

Section Traces.
  Definition event : TraceModel.Events.
   exists HTrace (HTBool true) (HTNat 0).
   congruence.
   intros e1 e2. destruct e1, e2; try (left; congruence); try (right; congruence).
   destruct b, b0; try (left; congruence); try (right; congruence).
   pose proof Coq.Arith.Peano_dec.eq_nat_dec n n0.
   destruct H. left; now subst.
   right; congruence.
  Defined.

  Definition endstate : TraceModel.Endstates.
    exists unit. exact tt.
  Defined.


  Definition trace := @TraceModel.trace event endstate.

End Traces.

Section Source.

  Definition sprg := {e : HExp | exists τ, typing e τ }.
  Definition spar := sprg.
  Definition sctx := unit.
  Definition splug (p : spar) (c : sctx) := p.

  Definition source := {| prg := sprg; par := spar; ctx := sctx; plug := splug |}.

  Definition traceS := trace.

  Definition semS : sprg -> traceS -> Prop :=
    fun p t =>
      match t with
      | TraceModel.tstop (t :: nil) tt => hsem (proj1_sig p) = t
      | _ => False
      end.
  Lemma non_empty_semS : forall W, exists t, semS W t.
  Proof.
    destruct W as [e [[|] Hty]].
    - destruct (type_correct_nat _ Hty) as [n Hn].
      now (exists (TraceModel.tstop ((HTNat n : ev event) :: nil) (tt : es endstate) : traceS)).
    - destruct (type_correct_bool _ Hty) as [b Hb].
      now (exists (TraceModel.tstop ((HTBool b : ev event) :: nil) (tt : es endstate) : traceS)).
  Qed.

  Definition semanticsS : Semantics source traceS :=
    {| sem := semS : prg source -> traceS -> Prop;
       non_empty_sem := non_empty_semS |}.

End Source.

Section Target.
  Definition tprg := {e : HExp | exists τ, typing e τ}.
  Definition tpar := tprg.
  Definition tctx := unit.
  Definition tplug (p : tpar) (c : tctx) := p.

  Definition target := {| prg := tprg; par := tpar; ctx := tctx; plug := tplug |}.

  Definition endstateT := ResourceExhaustion.endstateT endstate.
  Definition traceT := ResourceExhaustion.traceT event endstate.

  Fixpoint size (e : HExp) :=
    match e with
    | HNat n => 1
    | HBool _ => 1
    | HPlus e1 e2 => 1 + size e1 + size e2
    | HTimes e1 e2 => 1 + size e1 + size e2
    | HIte e1 e2 e3 => 1 + size e1 + size e2 + size e3
    | HLe e1 e2 => 1 + size e1 + size e2
    end.

  Definition semT' (n : nat) : tprg -> traceT :=
    fun p => if Nat.leb (size (proj1_sig p)) n then (tstop ((hsem (proj1_sig p) : ev event):: nil) (inl tt : es endstateT))
          else tstop nil (OOM endstate ).
  Definition semT : tprg -> traceT -> Prop := fun p t => exists n, semT' n p = t.
  Lemma non_empty_semT : forall W, exists t, semT W t.
  Proof.
    destruct W as [e ?].
    exists (tstop nil (OOM endstate)).
    exists 0.
    unfold semT'.
    simpl. assert (H: Nat.leb (size e) 0 = false) by now induction e.
    now rewrite H.
  Qed.

  Definition semanticsT : Semantics target traceT :=
    {| sem := semT : prg target -> traceT -> Prop;
       non_empty_sem := non_empty_semT |}.
End Target.

Section CompilationChain.
  Definition compile_w : prg source -> prg target :=
    id.

  Definition compiler : CompilationChain source target :=
    {| compile_whole := compile_w;
       compile_par := compile_w;
       compile_ctx := id |}.

End CompilationChain.

Definition rel := ResourceExhaustion.rel event endstate.
Definition rel_TC := rel_TC compiler semanticsS semanticsT rel.

Lemma no_silent : forall e tt l,
    semT e tt -> tt <> tsilent l.
Proof.
  intros e tt l Hsem.
  destruct tt.
  - congruence.
  - unfold semT in Hsem.
    destruct Hsem as [n Hsem].
    unfold semT' in Hsem.
    destruct (Nat.leb (size (proj1_sig e)));
      now inversion Hsem.
  - congruence.
Qed.

Lemma no_stream : forall e tt s,
    semT e tt -> tt <> tstream s.
Proof.
  intros e tt s Hsem.
  destruct tt.
  - congruence.
  - congruence.
  - unfold semT in Hsem.
    destruct Hsem as [n Hsem].
    unfold semT' in Hsem.
    destruct (Nat.leb (size (proj1_sig e)));
      now inversion Hsem.
Qed.

Lemma correctness : rel_TC.
Proof.
  unfold rel_TC.
  unfold NonRobustTraceCriterion.rel_TC.
  intros [e Hty] tt Hsem.
  inversion Hty as [τ Hty'].
  destruct tt; simpl in Hsem.
  - (* the interesting case *)
    destruct Hsem as [n Hsem].
    unfold semT' in Hsem.
    destruct (Nat.leb
             (size
                (proj1_sig
                   (compile_w
                      (exist (fun e : HExp => exists τ : type, typing e τ)
                         e Hty)))) n) eqn:Heq.
    + simpl in *.
      inversion Hsem; subst; clear Hsem.
      exists (tstop ((hsem e : ev event) :: nil) (tt : es endstate)).
      split.
      * now repeat constructor.
      * reflexivity.
    + simpl in *.
      inversion Hsem; subst; clear Hsem.
      exists (tstop ((hsem e : ev event) :: nil) (tt : es endstate)).
      split.
      right; eexists; split; constructor.
      reflexivity.
  - exfalso.
    now eapply no_silent; eauto.
  - exfalso.
    now eapply no_stream; eauto.
Qed.

