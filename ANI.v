From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Require Import ClassicalExtras.
Require Import MyNotation.
Require Import Setoid.
Require Import FunctionalExtensionality.
Require Import Setoid.

Require Import Galois.
Require Import LanguageModel.
Require Import TraceModel.
Require Import Properties.
Require Import ChainModel.
Require Import Def.
Require Import TraceCriterion. 

Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

Section ANI.

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  Variable trace__S trace__T : Set.

  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.

  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition beh__S := beh Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition beh__T := beh Target_Semantics.
  Local Definition prg__S := prg Source.
  Local Definition prg__T := prg Target.
  Local Definition sat__S := sat Source_Semantics.
  Local Definition sat__T := sat Target_Semantics.
  Local Definition hsat__S := hsat Source_Semantics.
  Local Definition hsat__T := hsat Target_Semantics.

  Local Definition cmp := compile_whole Source Target compilation_chain.

  Local Notation "W ↓" := (cmp W) (at level 50).

  Variable rel : trace__S -> trace__T -> Prop.
  Variable H_rel : more_obs_rel rel. 

  Local Definition ins : Galois_Insertion trace__S trace__T :=
    induced_insertion_swap H_rel.

  Lemma swap_low_t_single (s : trace__S) (t : trace__T) (rel_s_t : rel s t) :
    (swap_low rel) (single t) = single s.
  Proof.
    apply: functional_extensionality => s'.
    apply: prop_extensionality. rewrite /single /α__i /= /swap_low /low_rel /swap_rel.
    split.
    + move => [t' [Heq rel_s_t']]. subst.
      destruct H_rel as [Hrel1 Hrel2].
      destruct (Hrel1 t) as [ss [Hss Hunique]].
      by rewrite -(Hunique s' rel_s_t') -(Hunique s rel_s_t).
    + move => H. rewrite H. now exists t.
  Qed.

  Local Notation "U ♯" :=  (uco_sharp U ins) (at level 60).

  Lemma ϕ_sharp_ϕ {ϕ : @Uco trace__S} {s1 s2 : trace__S} {t1 t2 : trace__T}
                   (rel1  : rel s1 t1)
                   (rel2  : rel s2 t2) :
  (uco (ϕ ♯)) (single t1) = (uco (ϕ ♯)) (single t2) -> (uco ϕ) (single s1) = (uco ϕ) (single s2).
  Proof.
    rewrite /uco_sharp /best_approximation /= (swap_low_t_single rel1) (swap_low_t_single rel2) =>
    sharp_eq.
    have Hfoo: (swap_low rel) (swap_up rel (uco ϕ (single s1))) =
               (swap_low rel) (swap_up rel (uco ϕ (single s2))) by rewrite sharp_eq.
    move: Hfoo.
    have Hfoo1 : α__i ins = swap_low rel by [].
    have Hfoo2 : γ__i ins = swap_up rel by []. by rewrite -Hfoo1 -Hfoo2 !(I2 ins).
  Qed.

  Lemma ρ_ρ_sharp  {ρ : @Uco trace__S} {s1 s2 : trace__S} {t1 t2 : trace__T}
                   (rel1  : rel s1 t1)
                   (rel2  : rel s2 t2) :
    (uco ρ) (single s1) = (uco ρ) (single s2) -> (uco (ρ ♯)) (single t1) = (uco (ρ ♯)) (single t2).
  Proof.
    move => Heq.
    by rewrite /uco_sharp /best_approximation /=
               (swap_low_t_single rel1) (swap_low_t_single rel2) Heq.
  Qed.


  Local Definition rel_TC := rel_TC compilation_chain
                                    Source_Semantics Target_Semantics
                                    rel.

  Definition ANI {X : Set} (ϕ ρ : @Uco X) : (X -> Prop) -> Prop :=
    fun π : X -> Prop =>
      forall x1 x2, π x1 -> π x2 ->
                (uco ϕ) (single x1) = (uco ϕ) (single x2) ->
                (uco ρ) (single x1) = (uco ρ) (single x2).

  Theorem compiling_ANI (W : prg__S) (ϕ ρ : @Uco trace__S):
    rel_TC ->
    hsat__S W (ANI ϕ ρ) ->
    hsat__T (W ↓) (ANI (ϕ ♯) (ρ ♯)).
  Proof.
    move => CCtilde Hsrc t1 t2 semWcmp1 semWcmp2 H_ϕ_sharp. 
    destruct H_rel as [Hfun Htot].
    destruct (Hfun t1) as [s1 [Hrel1 Hunique1]]. (* *) 
    destruct (Hfun t2) as [s2 [Hrel2 Hunique2]].
    destruct (CCtilde W t1 semWcmp1) as [ss1 [relss1t1 Wsem1]]. 
    destruct (CCtilde W t2 semWcmp2) as [ss2 [relss2t2 Wsem2]].
    move: (Hunique1 ss1 relss1t1) => Heq1.
    move: (Hunique2 ss2 relss2t2) => Heq2. subst.  
    move: (ϕ_sharp_ϕ Hrel1 Hrel2 H_ϕ_sharp) => Hϕ.
    move: (Hsrc ss1 ss2 Wsem1 Wsem2 Hϕ). exact (ρ_ρ_sharp Hrel1 Hrel2).
  Qed.

  (* CA: notice that ϕ_sharp_ϕ and  ρ_ρ_sharp together provide an equivalence
         that we do not really need.

       CA: I think it is possible to weaken our assumptions,
           what I think is strictly necessary is the folllwing

           let f := swap_low rel
               g := swap_up  rel

           (for an arbitrary uco in the src and π_s)

            + [to show ϕ♯ is idempotent]
                ϕ (f (g π_s)) = π_s
                that is much weaker than asking swap_low ∘ swap_up = id,
                and can be reprhased as a condition on ϕ like,
                "ϕ maps elements of the same fg-level to the same property"

            +   rel s t -> ϕ(s) = ϕ (f t).
                CA: this last requirement seems to imply the condition we imposed on rel.

   *)

End ANI.
