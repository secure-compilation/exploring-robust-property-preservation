Require Import CommonST.
Require Import Events.
Require Import TraceModel.
Require Import Criteria.
Require Import ClassicalExtras.

Section Quick.

(* Very strange thing: This doesn't use RTEP at all! *)
(* - Any chance that going beyond RTC will fix this? *)

(* Less strange thing: this doesn't use compiler correctness any more *)

Definition valid_trace P t := exists Cs, sem src (Cs[P]) t.

Definition valid_finpref P m := exists Cs, @psem src (Cs[P]) m.

Definition err := esbad. (* This esbad thing is not general enough *)

Hypothesis fsb : forall P t,
  (exists Ct, sem tgt (Ct[P↓]) t /\ ~valid_trace P t) ->
  (exists m, t = tapp m (tstop err) /\ valid_finpref P m).

Lemma rtc_informative : forall P Ct t,
  sem tgt (Ct[P↓]) t ->
  exists Cs,
    (valid_trace P t -> sem src (Cs[P]) t) /\
    (~valid_trace P t -> exists m, psem (Cs[P]) m /\ t = (tapp m (tstop err))).
Proof.
  intros P Ct t H. destruct (classic (valid_trace P t)) as [Hv | Hnv].
  - destruct Hv as [Cs Hv]. exists Cs. split.
    + intros _. exact Hv.
    + intro Hnv. apply False_ind. apply Hnv. exists Cs. exact Hv.
  - assert(H':exists Ct, sem tgt (Ct [P ↓]) t /\ ~ valid_trace P t) by eauto.
    specialize (fsb P t H'). clear H'.
    destruct fsb as [m [H1 H2]]. clear fsb. subst. destruct H2 as [Cs H2].
    exists Cs. split.
    + intro Hv. apply False_ind. tauto.
    + intros _. exists m. split. assumption. reflexivity.
Qed.

(* If we can do the final `err` in the source then we can prove the original rtc
   - but there are still concerns about fsb and valid needing to be amended
     in this case to say that err is not in t *)

Variable err_ctx : ctx src -> ctx src.

Hypothesis err_ctx_correct : forall C P m,
  @psem src (C[P]) m ->
  sem src ((err_ctx C)[P]) (tapp m (tstop err)).

Lemma rtc : RTC.
Proof.
  rewrite RTC'.
  intros P Ct t H. destruct (classic (valid_trace P t)) as [Hv | Hnv].
  - destruct Hv as [Cs Hv]. exists Cs. exact Hv.
  - assert(H':exists Ct, sem tgt (Ct [P ↓]) t /\ ~ valid_trace P t) by eauto.
    specialize (fsb P t H'). clear H'.
    destruct fsb as [m [H1 H2]]. clear fsb. subst. destruct H2 as [Cs H2].
    exists (err_ctx Cs). now apply err_ctx_correct.
Qed.

End Quick.
