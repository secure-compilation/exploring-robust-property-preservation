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
     in this case to say that err is not in t
   - and more importantly the err_ctx_correct assumption seems too strong;
     context would be able to preempt program at any point and produce any action
*)

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


Section Stefan.

  Definition question_mark := forall P1 P2 Ct,
    beh (Ct [P1 ↓]) ⊆ beh (Ct [P2 ↓]) -> 
    exists Cs, beh (Cs [P1 ]) ⊆ beh (Cs [P2 ]).

  Variable Wt : trace -> par src.
 
  Hypothesis only_t:  forall Ct t t', sem tgt (Ct [(Wt t)↓]) t' -> t = t'. 
  Hypothesis t_src : forall Cs t, sem src (Cs [(Wt t)]) t. (* CC for Wt *)  
  
  Lemma question_mark_RTC : question_mark -> RTC.
  Proof.
    rewrite RTC'. intros Hqm P Ct t Ht. 
    destruct (classic (valid_trace P t)).
    - exact H.
    - unfold valid_trace in H. rewrite not_ex_forall_not in H.
      destruct (Hqm (Wt t) P Ct) as [Cs HCs].
      + intros b Hb. apply only_t in Hb. rewrite <- Hb. auto.
      + exfalso. apply ((H Cs)). apply HCs. apply t_src.
  Qed.       

  (* CA: 
     
     only_t + t_src => ((~ valid P t) -> False)

  *)
  
End Stefan. 