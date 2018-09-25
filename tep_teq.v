Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Setoid.
Require Import ClassicalExtras.
Require Import Logic.ClassicalFacts.


(** *our assumptions *)
(**********************************************************)
Hypothesis input_totality_tgt : input_totality tgt.
Hypothesis determinacy_src    : determinacy src.
Hypothesis tgt_sem            : forall W t, ~ sem tgt W t ->
                                       (exists m, prefix m t /\ psem W m /\
                                       (forall m', prefix m' t -> psem W m' -> fpr m' m)).  
(**********************************************************)

       
Theorem r2RPP_teq : r2RPP -> teq_preservation.
Proof.
  intros r2rpp. unfold teq_preservation. apply NNPP.
  intros hf. rewrite not_forall_ex_not in hf. destruct hf as [P1 hf].
   rewrite not_forall_ex_not in hf. destruct hf as [P2 hf].
   rewrite not_imp in hf. destruct hf as [H1 hf].
   rewrite not_forall_ex_not in hf. destruct hf as [Ct hf].
   rewrite not_forall_ex_not in hf. destruct hf as [t1 hf].
   rewrite not_equiv in hf. destruct hf as [K | K]; destruct K as [k1 k2].
   + specialize (r2rpp P1 P2 traces_match).
     assert (Hsat : rsat2 P1 P2 traces_match).
     { intros C b1 b2 Hb1 Hb2. rewrite (H1 C b1) in Hb1. 
       now apply (determinacy_src (C [P2])). } 
     specialize (r2rpp Hsat Ct t1); clear Hsat.
    assert (H : forall t2, sem tgt (Ct [P2 ↓]) t2 -> traces_match t1 t2). 
    { intros t2 H. now apply r2rpp. } clear r2rpp H1.
    destruct (tgt_sem (Ct [P2 ↓]) t1 k2) as [m [Hmt1 [Hpsem_m Hmax_m]]].
    destruct Hpsem_m as [t2 [Hmt2 Hsem_t2]].
    specialize (H t2 Hsem_t2). destruct H; try now subst.
    destruct H as [m' [i1 [i2 [Hi1 [Hi2 [Hdiffi [Hstop' [Hpref1 Hpref2]]]]]]]].
    assert (psem (Ct [P2 ↓]) (fsnoc m' i1)).
    { apply (input_totality_tgt (Ct [P2 ↓]) m' i2 i1); auto. now exists t2. }
    assert (fpr (fsnoc m' i1) m) by now apply Hmax_m.
    apply (fpr_pref_pref _ _ t2) in H0; auto.  
    destruct (same_ext (fsnoc m' i1) (fsnoc m' i2) t2); auto;
    apply snoc_m_event_equal in H1; congruence. 
  + admit. (*symmetric case *)
Admitted.
  