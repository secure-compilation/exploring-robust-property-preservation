From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Require Import ClassicalExtras.
Require Import Coq.Logic.ClassicalFacts.
Require Import MyNotation.
Require Import Setoid.
Require Import FunctionalExtensionality.
Require Import Setoid.

Require Import Galois.
Require Import LanguageModel.
Require Import TraceModel.
Require Import Properties.
Require Import ChainModel.
Require Import NonRobustDef.
Require Import NonRobustTraceCriterion.

Section Conjunction.

  Axiom prop_ext : prop_extensionality. 

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  (*CA: we don't need a particular structure of traces to define preservation
        e.g. traces = values or our defn of traces both make sense
   *)
  Variable trace__S trace__T : Type.

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

  Local Definition cmp := compile_whole Source Target compilation_chain.

  Local Notation "W ↓" := (cmp W) (at level 50).

  
  (* the two relations and their conjunction *)
  Variable rel1 rel2 : trace__S -> trace__T -> Prop.
  Definition rel_cap : trace__S -> trace__T -> Prop :=
    fun s t => rel1 s t /\ rel2 s t.

  (* the induced connections *)
  Local Definition adjunction1 :=  induced_connection rel1.
  Local Definition adjunction2 :=  induced_connection rel2.
  
  Local Definition τ1 : prop__S -> prop__T := α adjunction1.
  Local Definition σ1 : prop__T -> prop__S := γ adjunction1.
  Local Definition τ2 : prop__S -> prop__T := α adjunction2.
  Local Definition σ2 : prop__T -> prop__S := γ adjunction2.

  Definition τ : prop__S -> prop__T := fun π__S => (fun t => τ1 π__S t /\ τ2 π__S t). 

  Definition rel : trace__S -> trace__T -> Prop :=
    fun s t => (τ (fun x => x = s) t).

  Lemma rel_is_relcap : rel = rel_cap. 
  Proof.
    apply: functional_extensionality => s.
    apply: functional_extensionality => t.
    apply: prop_ext. 
    rewrite /rel /rel_cap /τ /τ1 /τ2 /α /= /low_rel. split.
    - move => [[s1 [Heq1 Hrel1]] [s2 [Heq2 Hrel2]]]. by subst. 
    - by firstorder.  
  Qed.

  (* Local Definition adjunction :=  induced_connection rel. *)

  (* Lemma τ_induced_by_rel : τ = α adjunction. *)
  (* Proof. *)
  (*   apply: functional_extensionality => π__S. *)
  (*   apply: functional_extensionality => t. *)
  (*   apply: prop_ext. *)
  (*   rewrite /α /τ  /τ1 /τ2 /= /low_rel. *)
    
  
  Local Definition CCtilde1 := rel_TC compilation_chain Source_Semantics Target_Semantics rel1. 
  Local Definition τTP1     := τTP compilation_chain Source_Semantics Target_Semantics τ1.
  Local Definition trinity1 := rel_TC_τTP compilation_chain Source_Semantics Target_Semantics rel1.  

  
  Local Definition CCtilde2 := rel_TC compilation_chain Source_Semantics Target_Semantics rel2.
  Local Definition τTP2     := τTP compilation_chain Source_Semantics Target_Semantics τ2.
  Local Definition trinity2 := rel_TC_τTP compilation_chain Source_Semantics Target_Semantics rel2. 

  
  Local Definition CCtilde_cap := rel_TC compilation_chain Source_Semantics Target_Semantics rel_cap.
  Local Definition τTP        := τTP compilation_chain Source_Semantics Target_Semantics τ.      
  
  Lemma CCtilde_cap_τTP : CCtilde_cap <-> τTP.
  Proof.
    rewrite /CCtilde_cap -rel_is_relcap. 
     setoid_rewrite contra_τTP. split.
    - move => Htilde W π [t [Hsemt Hτ]].
      destruct (Htilde W t Hsemt) as [s [Hrel_s_t Hsems]].
      exists s. split; auto. move => s_in_π. apply: Hτ.
      move: Hrel_s_t. rewrite /rel /τ /τ1 /τ2 /α /= /low_rel => Hrel.
      move: Hrel => [[y1 [Heq1 Hrel1]] [y2 [Heq2 Hrel2]]]. subst. 
      split; by exists s. 
    - move => Hτ W t HsemWt.
      have H : (forall s1 s2, sem__S W s1 -> sem__S W s2 -> rel1 s1 t -> rel2 s2 t -> s1 <> s2) \/
               (exists s1 s2, sem__S W s1 /\ sem__S W s2 /\ rel1 s1 t /\ rel2 s2 t /\ s1 = s2) by admit. 
      (* just classical reasoning *)
      case: H. 
      move => H. exfalso.
      have cc1 : CCtilde1 by admit. have cc2 : CCtilde2 by admit. 
      destruct (cc1 W t HsemWt) as [s1 [HsemWs1 Hrel1]].
      destruct (cc2 W t HsemWt) as [s2 [HsemWs2 Hrel2]].
      case: (Hτ W (fun s => ~ rel s t /\ sem__S W s)).
      { admit. (* W↓ does not satisfies τ{π__S} = ∅! *) }
      move => s [HsemWs K]. move /de_morgan1: K. rewrite -dne.
      rewrite rel_is_relcap /rel_cap. move  => [[k11 k12]| k2]; try now auto. 
      by apply: (H s s).      
      (* 2nd case *)
      by firstorder. 
   Admitted.    
  
  Theorem TPtau_for_conjunction :
    CCtilde1 /\ CCtilde2 -> τTP.
  Proof.
    move => [H1 H2].
    have Hτ1 : τTP1 by move /trinity1 : H1.
    have Hτ2 : τTP2 by move /trinity2 : H2.
    move => W π__S sat_src. rewrite /τ. split.
      by apply: (Hτ1 W). by apply: (Hτ2 W).
  Qed.     
 
  
  Theorem conjunction_intersection : CCtilde1 /\ CCtilde2 <->  CCtilde_cap.
  Proof.
    rewrite CCtilde_cap_τTP. split.
    - exact TPtau_for_conjunction.  
    - setoid_rewrite trinity1. setoid_rewrite trinity2.
      by firstorder.
   Qed.                                   

End Conjunction.