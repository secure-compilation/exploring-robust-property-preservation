From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Require Import ClassicalExtras.
Require Import MyNotation.
Require Import Setoid.
Require Import FunctionalExtensionality.

Require Import Galois.
Require Import LanguageModel.
Require Import TraceModel.
Require Import Properties.
Require Import ChainModel.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.

Section Robust2relSSCHPreservation.

  Variable Source Target: Language.
  Variable compilation_chain : CompilationChain Source Target.

  (*CA: we don't need a particular structure of traces to define preservation
        e.g. traces = values or our defn of traces both make sense
   *)
  Variable trace__S trace__T : Set.

  Local Definition prop__S := prop trace__S.
  Local Definition prop__T := prop trace__T.

  Variable Source_Semantics : Semantics Source trace__S.
  Variable Target_Semantics : Semantics Target trace__T.

  Local Definition sem__S := sem Source_Semantics.
  Local Definition sem__T := sem Target_Semantics.
  Local Definition beh__S := beh Source_Semantics.
  Local Definition beh__T := beh Target_Semantics. 
  Local Definition par__S := par Source.
  Local Definition par__T := par Target.
  Local Definition ctx__S := ctx Source.
  Local Definition ctx__T := ctx Target. 
  Local Definition rsat__S := rhsat2 Source_Semantics.
  Local Definition rsat__T := rhsat2 Target_Semantics.
  
  Local Definition cmp := compile_par Source Target compilation_chain.

  Local Notation "P ↓" := (cmp P) (at level 50).
 (* CA: don't understand why this does not work 

   Local Notation " C [ P ] " := (plug _  P C) (at level 50).
  *)
  Local Definition plug__S:= plug Source.
  Local Definition plug__T := plug Target.

  (* still mappings on trace properties *)
  Variable σ__π : (trace__T -> Prop) -> (trace__S -> Prop).
  Variable τ__π : (trace__S -> Prop) -> (trace__T -> Prop).

  Definition σ : (prop__T * prop__T -> Prop) -> (prop__S * prop__S -> Prop) :=
    fun T =>
      fun Π => exists π__T π__T', fst Π = σ__π π__T /\
                        snd Π = σ__π π__T' /\
                        T (π__T, π__T').

  Definition τ : (prop__S * prop__S -> Prop) -> (prop__T * prop__T -> Prop) :=
    fun S =>
      fun Π => exists π__S π__S', fst Π = τ__π π__S /\
                        snd Π = τ__π π__S' /\
                        S (π__S, π__S').
  
  Definition sCl_σ :  ((trace__T -> Prop) * (trace__T -> Prop) -> Prop) ->
                      ((trace__S -> Prop) * (trace__S -> Prop) -> Prop) :=
   sCl2  ∘ σ.
  
  Definition sCl_τ : ((trace__S -> Prop) * (trace__S -> Prop) -> Prop) ->
                     ((trace__T -> Prop) * (trace__T -> Prop) -> Prop) :=
   sCl2  ∘ τ.

  Definition sCl_σR2rhP (P1 P2 : par__S) (T : prop__T * prop__T -> Prop) :=
    rsat__S P1 P2 (sCl_σ T) -> rsat__T (P1 ↓) (P2 ↓) T.   

  (* Lemma contra_σR2rhP (P1 P2 : par__S) (T : prop__T * prop__T -> Prop) : *)
  (*   (σR2rhP P1 P2 T) <-> ((exists C__T, ~ T (beh__T (plug__T (P1 ↓) C__T), *)
  (*                                     beh__T (plug__T (P2 ↓) C__T))) -> *)
  (*                       (exists C__S, ~ (σ T) (beh__S (plug__S P1 C__S), *)
  (*                                        beh__S (plug__S P2 C__S)))). *)
  (* Proof. *)
  (*   rewrite /sClσR2rhP. by rewrite [_ -> _] contra !neg_rhsat2. *)
  (* Qed. *)

  (* Lemma contra_σR2rHP : *)
  (*   σR2rHP <-> (forall P1 P2 T, (exists C__T, ~ T (beh__T (plug__T (P1 ↓) C__T), *)
  (*                                     beh__T (plug__T (P2 ↓) C__T))) -> *)
  (*                         (exists C__S, ~ (σ T) (beh__S (plug__S P1 C__S), *)
  (*                                        beh__S (plug__S P2 C__S)))). *)
  (* Proof. *)
  (*   rewrite /σR2rHP. *)
  (*   split => H P1 P2 T; by move/contra_σR2rhP: (H P1 P2 T). *)
  (* Qed. *)

  Definition sCl_τR2rhP (P1 P2 : par__S) (S : prop__S * prop__S -> Prop) :=
    rsat__S P1 P2 S -> rsat__T (P1 ↓) (P2 ↓) (sCl_τ S).
  

  (* Lemma contra_τR2rhP (P1 P2 : par__S) (S : prop__S * prop__S -> Prop) : *)
  (*   (τR2rhP P1 P2 S) <-> ((exists C__T,  ~ (τ S) (beh__T (plug__T (P1 ↓) C__T), *)
  (*                                         beh__T (plug__T (P2 ↓) C__T ))) -> *)
  (*                     (exists C__S, ~ S (beh__S (plug__S P1 C__S), beh__S (plug__S P2 C__S)))). *)
  (* Proof. *)
  (*   rewrite /τR2rhP. by rewrite [_ -> _] contra !neg_rhsat2. *)
  (* Qed. *)

  (* Lemma contra_τR2rHP : *)
  (*   τR2rHP <-> (forall P1 P2 S, ((exists C__T,  ~ (τ S) (beh__T (plug__T (P1 ↓) C__T), *)
  (*                                         beh__T (plug__T (P2 ↓) C__T ))) -> *)
  (*                     (exists C__S, ~ S (beh__S (plug__S P1 C__S), beh__S (plug__S P2 C__S))))). *)
  (* Proof. *)
  (*   rewrite /τR2rHP. *)
  (*   split => H P1 P2 S; by move/contra_τR2rhP: (H P1 P2 S). *)
  (* Qed. *)

  Lemma Galois_fst_lift (Hadj : Adjunction_law τ__π σ__π) :
    forall T, SCH2 T ->
       (sCl_τ (sCl_σ (T)) ⊆ T).
  Proof. 
    move => T SCH2T [b__T1 b__T2] [b__t1 [b__t2 [Hτ [H1 H2]]]].
    move: Hτ. move => [b__s1 [b__s2 [H11 [H22 Hσ]]]].
    destruct Hσ as [b__s1' [b__s2' [Hσ' [H1' H2']]]].
    destruct Hσ' as [bt1'[ bt2' [H11' [H22' HT]]]].
    simpl in *. subst. 
    apply: SCH2T.  
    exact HT. 
    apply: subset_trans. exact H1. by rewrite Hadj.  
    apply: subset_trans. exact H2. by rewrite Hadj. 
  Qed.
  
  Lemma Galois_snd_lift (Hadj : Adjunction_law τ__π σ__π) :
    forall S, SCH2 S ->
         S ⊆ (sCl_σ (sCl_τ S)).
  Proof.
    move => S SCH2S [bs1 bs2] HS.
    exists (σ__π (τ__π bs1)), (σ__π (τ__π bs2)). split.
    + exists (τ__π bs1), (τ__π bs2). repeat (split; auto).  
      ++ exists (τ__π bs1), (τ__π bs2). repeat (split; auto). 
         +++ now exists bs1, bs2. 
    rewrite /=. by repeat rewrite -Hadj.           
  Qed.              
    
  Theorem Adj_sCl_σR2rSCHP_iff_sCl_τR2rSCHP :
     Adjunction_law τ__π σ__π ->
    (forall P1 P2 T, SCH2 T -> sCl_σR2rhP P1 P2 T) <->
    (forall P1 P2 S, SCH2 S -> sCl_τR2rhP P1 P2 S).
  Proof.
    move => H_adj. split.
    - move => Hσ P1 P2 S S_ssc Hrsat_src. 
      have Hfoo: SCH2 (sCl_τ S) by apply: sCl2_SCH2.
      have Hfoo': rsat__S P1 P2 (sCl_σ (sCl_τ S)). 
      { apply: rhsat2_upper_closed.
        exact Hrsat_src.
        by apply: Galois_snd_lift. }         
      by move: (Hσ P1 P2 (sCl_τ S) Hfoo Hfoo') => Hsat__T.  
    - move => Hτ P1 P2 T T_ssc Hrrsat_tgt.
      have H : rsat__T (P1 ↓) (P2 ↓) (sCl_τ (sCl_σ T)).
      { apply: Hτ. apply: sCl2_SCH2. assumption. }
      apply: rhsat2_upper_closed. exact H.
      by apply: Galois_fst_lift.  
  Qed.

End Robust2relSSCHPreservation.
