From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.  

Require Import DiffEvents.
Require Import DiffTraceModel.
Require Import ClassicalExtras.
Require Import Setoid.
Require Import List.

Record language {k : level} :=
  {
    par  : Set;  (* partial programs *)
    prg  : Set;  (* whole programs *)
    ctx  : Set;  (* context *)
    plug : par -> ctx -> prg;
    sem  : prg -> @prop k;
    non_empty_sem : forall W, exists t, sem W t
  }.


Axiom src : @language source.
Axiom tgt : @language target.
Axiom compile_par : (par src) -> (par tgt).
Axiom compile_ctx : (ctx src) -> (ctx tgt).
Axiom compile_prg : (prg src) -> (ctx tgt).

(*TODO: fix notation *)
Notation "C [ P ]" := (plug P C) (at level 50).

Notation "P ↓" := (compile_par P) (at level 50).

Definition sat {k : level}
               {K : language}
               (P : prg K)
               (π : @prop k) : Prop :=
  forall t, sem P t -> π t.

Definition rsat {k : level}
                {K : language}
                (P : par K)
                (π : @prop k) : Prop :=
  forall C, sat (plug P C) π.

Lemma neg_rsat {k : level} {K : @language k} :
  forall (P : @par k K) (π : @prop k),
    (~ rsat P π <->
           (exists C t, sem (plug P C) t /\ ~ π t)).
Proof.
Admitted. (* TODO: port this proof in ssreflect style *)


Definition σRTP (σ : @prop target -> @prop source) :=
  forall (P : par src) (π : @prop target),
  rsat P (σ π) -> rsat (P↓) π.

Definition τRTP (τ : @prop source -> @prop target) :=
  forall (P : par src) (π : @prop source),
    rsat P  π -> rsat (P↓) (τ π).

Lemma contra_τRTP (τ : @prop source -> @prop target) :
  τRTP τ <-> ( forall (P : par src) (π : @prop source),
               (exists Ct t, sem (plug (P↓) Ct) t /\ ~ (τ π) t) ->
               (exists Cs s, sem (plug P Cs) s /\ ~ π s)).
Admitted. 

Variable rel : @trace source -> @trace target -> Prop. 

Definition tilde_RTC := forall P Ct (t : @trace target),
    sem (plug (P ↓) Ct) t ->
    (exists Cs s, rel s t /\ sem (plug P Cs) s).

Definition τ' : @prop source -> @prop target :=
  fun π => (fun t => exists s, π s /\ rel s t).  

Definition σ' : @prop target -> @prop source :=
  fun π => (fun s => exists t, π t /\ rel s t). 


Theorem tilde_RTC_τRTP : tilde_RTC <-> τRTP (τ').
Proof.
  rewrite contra_τRTP. split.    
  - move => Htilde P π [Ct [t [Hsemt Hτ]]].
    destruct (Htilde P Ct t Hsemt) as [Cs [s [Hrel_s_t Hsems]]].   
    exists Cs, s. split; auto. move => s_in_π. apply: Hτ. by exists s.
 - move => Hτ P Ct t Hsemt. specialize (Hτ P (fun s => ~ rel s t)).
   case: Hτ.
   { exists Ct, t. split; auto. unfold τ'. move => [s [Hc Hcc]] //=. }
   move  => Cs [s [Hsems H]]. exists Cs, s. split; auto; by apply: NNPP.                                  
Qed.


Notation "π1 ⊆ π2" := (forall t, π1 t -> π2 t) (at level 50).

Lemma rsat_upper_closed {k : level} {K : @language k}:
  forall (P : par K) (π1 π2 : @prop k), rsat P π1 -> π1 ⊆ π2 -> rsat P π2.  
Proof.  
  move => P π1 π2 Hrsat1 Hsuper C t Hsem. apply: Hsuper.
  by apply: (Hrsat1 C t).  
Qed. 

(*CA: I never use the monotonicity but suspect it is for free *)
Definition Galois_fst (σ : @prop target -> @prop source)
                      (τ : @prop source -> @prop target) : Prop :=

  (forall (πs : @prop source), πs ⊆ σ (τ πs)).

Definition Galois_snd (σ : @prop target -> @prop source)
                      (τ : @prop source -> @prop target) : Prop :=
  (forall (πt : @prop target), τ (σ πt) ⊆ πt).

Definition Galois_cp  (σ : @prop target -> @prop source)
                      (τ : @prop source -> @prop target) : Prop :=
  Galois_fst σ τ /\ Galois_snd σ τ. 

Theorem σ_τ_equiv (σ : @prop target -> @prop source)
                  (τ : @prop source -> @prop target) :
  (Galois_cp σ τ) -> (σRTP σ) <-> (τRTP τ).
Proof.
  move => [G1 G2]. split. 
  - move => Hσ P πs Hrsat_src. apply: (Hσ P (τ πs)).
    apply: (rsat_upper_closed Hrsat_src). by apply: G1. 
  - move => Hτ P πt Hrsat_tgt.
    have H : rsat (P ↓) (τ (σ πt)) by apply: Hτ. 
    apply: (rsat_upper_closed H). by apply: G2.
Qed.

Corollary all_equivalent : (Galois_cp σ' τ') ->
                                   σRTP (σ') <-> tilde_RTC.
Proof. move => G. by rewrite tilde_RTC_τRTP (σ_τ_equiv G). Qed. 

(* We actually need need only Galois_snd to have the equivalence *)

Lemma Galois_fst_holds : (forall s, exists t, rel s t) -> Galois_fst σ' τ'.
Proof.
  move => Hrel πs s Hπs. unfold σ', τ'.
  destruct (Hrel s) as [t Hrel_s].  
  exists t. split; auto. now exists s.
Qed.


Lemma Galois_implies_total_rel :
  Galois_cp σ' τ' -> (forall s, exists t, rel s t).
Proof.
  move => [G1 G2] s.
  have Hs: (σ' (τ' (fun s' => s' = s))) s by apply: G1.   
  destruct Hs as [t Hs]. now exists t.
Qed. 