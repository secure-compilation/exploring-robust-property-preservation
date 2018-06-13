Require Import Events.
Require Import TraceModel.
Require Import Properties.
Require Import CommonST.
Require Import Robustdef.
Require Import Setoid.
Require Import ClassicalExtras.
Require Import Logic.ClassicalFacts.

Definition two_rRSC : Prop :=
  forall (r : finpref -> finpref -> Prop) P1 P2 ,
    ((forall Cs m1 m2, psem (Cs [P1]) m1 ->
                  psem (Cs [P2]) m2 ->
                   r m1 m2) ->
     (forall Ct m1 m2, psem (Ct [P1 ↓]) m1 ->
                  psem (Ct [P2 ↓]) m2 ->
                  r m1 m2)).

Print teq_preservation.

(** *our assumptions *)
(**********************************************************)
Hypothesis input_totality_tgt : @input_totality tgt.
Hypothesis determinacy_src    : @determinacy src.
Hypothesis tgt_sem            : @semantic_safety_like tgt.
(**********************************************************)


Theorem two_rRSC_teq : two_rRSC -> teq_preservation.
Admitted.