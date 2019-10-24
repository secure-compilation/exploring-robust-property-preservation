From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import ClassicalExtras.
Require Import MyNotation.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Definition prop_extensionality := propositional_extensionality.

Definition monotone {X Y : Type} (f : (X -> Prop) -> (Y -> Prop)) : Prop :=
  forall (π1 π2: X -> Prop), (π1 ⊆ π2) -> (f π1 ⊆ f π2).

Definition idempotent {X : Type} (f : (X -> Prop) -> (X -> Prop)) : Prop :=
  forall π: X -> Prop, f (f π) = f π.

Definition extensive {X : Type} (f : (X -> Prop) -> (X -> Prop)) : Prop :=
  forall π: X -> Prop, π ⊆ (f π).


Definition lift {X Y : Type} (f :(X -> Prop) -> (Y -> Prop))
                            (H : (X -> Prop) -> Prop) : ((Y -> Prop) -> Prop) :=
  fun (b1 : Y -> Prop) => exists b2, (H b2) /\ b1 = f b2.

(* Definition of the adjunction law *)

Definition Adjunction_law {A C : Type}
           (α : (C -> Prop) -> (A -> Prop))
           (γ : (A -> Prop) -> (C -> Prop)) :=
  forall (a: A -> Prop) (c: C -> Prop),  (α c) ⊆ a <-> c ⊆ (γ a).


(* We define Galois connection between powersets ordered by set inclusion:
     (2^X, ⊆) ⇆ (2^Y, ⊆)
   *)
Structure Galois_Connection (A C : Type) := {
    α : (C -> Prop) -> (A -> Prop);
    γ : (A -> Prop) -> (C -> Prop);
    adjunction_law : Adjunction_law α γ
  }.


Definition Galois_fst {A C : Type}
           (α: (C -> Prop) -> (A -> Prop))
           (γ: (A -> Prop) -> (C -> Prop)) :=
  forall (c: C -> Prop),  c ⊆ (γ (α c)).

Definition Galois_snd {A C : Type}
           (α: (C -> Prop) -> (A -> Prop))
           (γ: (A -> Prop) -> (C -> Prop)) :=
  forall (a : A -> Prop), (α (γ a)) ⊆ a.

Lemma Galois_equiv {A C: Type}
      (α: (C -> Prop) -> (A -> Prop))
      (γ: (A -> Prop) -> (C -> Prop)) :
  Adjunction_law α γ <-> ( monotone α /\ monotone γ /\ Galois_fst α γ  /\ Galois_snd α γ).
Proof.
  split.
  - move => H_adj. split.
    + move => c1 c2 H_sub. rewrite H_adj.
      apply: (subset_trans H_sub). by rewrite -H_adj.
    + split.
      ++ move => a1 a2 H_sub. rewrite -H_adj.
         apply: subset_trans. rewrite H_adj. by apply: subset_ref.
         assumption.
      ++ split; move => x; [by rewrite -H_adj | by rewrite H_adj].
  - move => [mono_α [mono_γ [G1 G2]]] a c. split => H.
    + apply: subset_trans. apply: (G1 c). by apply: mono_γ.
      apply: subset_trans. apply: mono_α. exact H. by apply: G2.
Qed.

(* Galois Insertion (α (γ a)) = a *)
Definition Insertion_snd {A C : Type}
           (α: (C -> Prop) -> (A -> Prop))
           (γ: (A -> Prop) -> (C -> Prop)) :=
  forall (a : A -> Prop), (α (γ a)) = a.

Structure Galois_Insertion (A C : Type) := {
            α__i : (C -> Prop) -> (A -> Prop);
            γ__i : (A -> Prop) -> (C -> Prop);
            mono_α : monotone α__i;
            mono_γ : monotone γ__i;
            G1 : Galois_fst α__i γ__i;
            I2 : Insertion_snd α__i γ__i
          }.


Lemma Insertion_coercion_Connection {A C : Type} :
  Galois_Insertion A C -> Galois_Connection A C.
Proof.
  move => [α γ mono_alpha mono_gamma H1 H2].
  have H_adj: Adjunction_law α γ.
  rewrite Galois_equiv. repeat split; auto.
  move => a. rewrite (H2 a). now apply: subset_ref.
  exact (Build_Galois_Connection H_adj).
Qed.

Coercion Insertion_coercion_Connection  : Galois_Insertion >-> Galois_Connection.

(* Galois Reflection (γ (α c)) = c *)

Definition Reflection_fst {A C : Type}
           (α: (C -> Prop) -> (A -> Prop))
           (γ: (A -> Prop) -> (C -> Prop)) :=
  forall (c : C -> Prop), (γ (α c)) = c.

Structure Galois_Reflection (A C : Type) := {
            α__r : (C -> Prop) -> (A -> Prop);
            γ__r : (A -> Prop) -> (C -> Prop);
            mono_α__r : monotone α__r;
            mono_γ__r: monotone γ__r;
            R1 : Reflection_fst α__r γ__r;
            G2 : Galois_snd α__r γ__r
          }.

Lemma Reflection_coercion_Connection {A C : Type} :
  Galois_Reflection A C -> Galois_Connection A C.
Proof.
  move => [α γ mono_alpha mono_gamma H1 H2].
  have H_adj: Adjunction_law α γ.
  rewrite Galois_equiv. repeat split; auto.
  move => a. rewrite (H1 a). now apply: subset_ref.
  exact (Build_Galois_Connection H_adj).
Qed.

Coercion Reflection_coercion_Connection  : Galois_Reflection >-> Galois_Connection.


  (* Given ∼ ⊆ 2^C × 2^A there is a pair of maps
     α : 2^C -> 2^A,  γ : 2^A -> 2^C, that is a Galois connection
     between (2^C, ⊆) and (2^A, ⊆).
   *)

Definition low_rel  {A C : Type} (rel : C -> A -> Prop) : (C -> Prop) -> (A -> Prop) :=
  fun (c : C -> Prop) =>
    (fun (x : A) => exists (y : C), (c y) /\ rel y x).

Definition up_rel {A C : Type} (rel : C -> A -> Prop) : (A -> Prop) -> (C -> Prop) :=
  fun (a : A -> Prop) =>
    (fun (y : C) => forall (x : A), (rel y x -> a x)).

Lemma induced_adj_law {A C : Type} (rel : C -> A -> Prop) :
  Adjunction_law (low_rel rel) (up_rel rel).
Proof.
  move => a c. rewrite /low_rel /up_rel. split.
  + move => H t h_t t' rel_t_t'. apply: H. by exists t.
                                               + move => H x [y [c_y rel_y_x]]. by apply: (H y).
Qed.

Definition induced_connection {A C : Type} (rel : C -> A -> Prop) : Galois_Connection A C :=
  Build_Galois_Connection (induced_adj_law rel).

 (*
    We can also build a connection such that C is the abstract domain and A the concrete one

  *)

Definition swap_rel {A C : Set} (rel : C -> A -> Prop) : A -> C -> Prop := fun a c => rel c a.

Definition induced_connection_swap {A C : Set} (rel : C -> A -> Prop) : Galois_Connection C A :=
  Build_Galois_Connection (induced_adj_law (swap_rel rel)).


(*
  motivation:
    we have in mind a scenario in which more observations are possible in the
    target language, but no really "new" computations happen.
    So that we relate a source trace with all the target traces that insert
    extra observations between source events.
 *)

Definition total_fun_A_C {A C : Set} (rel : C -> A -> Prop) : Prop :=
  forall a, exists! c, rel c a.

Definition total {A C : Type} (rel : C -> A -> Prop) : Prop :=
  forall c, exists a, rel c a.

Definition more_obs_rel {A C : Set} (rel : C -> A -> Prop) :=
  total_fun_A_C rel /\ total rel.


Definition swap_low {A C : Set} (rel : C -> A -> Prop) : (A -> Prop) -> (C -> Prop) :=
  low_rel (swap_rel rel).

Definition swap_up {A C : Set} (rel : C -> A -> Prop) : (C -> Prop) -> (A -> Prop) :=
  up_rel (swap_rel rel).

Lemma monotone_swap_low {A C : Set} (rel : C -> A -> Prop) :
  @monotone A C (swap_low rel).
Proof.
   have: Adjunction_law (swap_low rel) (swap_up rel)
    by apply: adjunction_law (induced_connection (swap_rel rel)).
   rewrite Galois_equiv. by move => [H1 [H2 [G1 G2]]].
Qed.

Lemma monotone_swap_up {A C : Set} (rel : C -> A -> Prop) :
  @monotone C A (swap_up rel).
Proof.
   have: Adjunction_law (swap_low rel) (swap_up rel)
    by apply: adjunction_law (induced_connection (swap_rel rel)).
   rewrite Galois_equiv. by move => [H1 [H2 [G1 G2]]].
Qed.

Lemma G1_swap_up_low_leq {A C : Set} (rel : C -> A -> Prop):
  Galois_fst (swap_low rel) (swap_up rel).
Proof.
  have: Adjunction_law (swap_low rel) (swap_up rel)
    by apply: adjunction_law (induced_connection (swap_rel rel)).
  rewrite Galois_equiv. by move => [H1 [H2 [G1 G2]]].
Qed.

Lemma I2_swap_low_up_id {A C : Set} (rel : C -> A -> Prop):
  more_obs_rel rel ->
  Insertion_snd (swap_low rel) (swap_up rel).
Proof.
  move => [rel_fun rel_total].
  rewrite /Insertion_snd /swap_low /swap_up /low_rel /up_rel /swap_rel /=.
  move => π__a. apply: functional_extensionality => c.
  apply: prop_extensionality. split.
  + move => [a [Ha rel_c_a]]. by apply: Ha.
  + move => π_c. destruct (rel_total c) as [a rel_c_a].
    exists a. split; auto.
    move => c' rel_c'_a. destruct (rel_fun a) as [c_unique [rel_cunique Hunique]].
    have H1: c_unique = c by apply: Hunique.
    have H2: c_unique = c' by apply: Hunique.
    by subst.
Qed.

Definition induced_insertion_swap {A C : Set}
                                  (rel : C -> A -> Prop)
                                  (H_obs_rel : more_obs_rel rel) : Galois_Insertion C A :=
  @Build_Galois_Insertion C A (swap_low rel) (swap_up rel)
                              (@monotone_swap_low A C rel)
                              (@monotone_swap_up A C rel)
                              (@G1_swap_up_low_leq A C rel)
                              (@I2_swap_low_up_id A C rel H_obs_rel).


(** *upper closure operator  \cite{giacobazzi2018abstract} (pag 7) *)
Record Uco {X: Type} :=
  {
    uco: (X -> Prop) -> (X -> Prop);
    mono: monotone uco;
    idmp: idempotent uco;
    ext : extensive uco
  }.

(* for simplicity defined only on insertions *)
Definition best_approximation {A C : Set} (gal : Galois_Insertion C A)
                                          (f : (C -> Prop) -> (C -> Prop)) : (A -> Prop) -> (A -> Prop) :=
  (γ__i gal) ∘ f ∘ (α__i gal).


Lemma composition_mono {A B C : Set} (f : (A -> Prop) -> (B -> Prop)) (g : (B -> Prop) -> (C -> Prop))
      (mono_f : monotone f) (mono_g : monotone g) : monotone (g ∘ f).
Proof.
  move => π1 π2 H_sub. apply: mono_g. by apply: mono_f.
Qed.


Lemma best_approximation_mono {A C : Set} (ins : Galois_Insertion C A)
                                          (ϕ : @Uco C) :
                                          monotone (best_approximation ins (uco ϕ)).
Proof.
  rewrite /best_approximation.
  apply: composition_mono.
   apply: composition_mono.
   exact (@mono_α C A ins). exact (@mono C ϕ).
  exact (@mono_γ C A ins).
Qed.

Lemma best_approximation_idmp {A C : Set} (ins : Galois_Insertion C A)
                                          (ϕ : @Uco C) :
                                          idempotent (best_approximation ins (uco ϕ)).
Proof.
  rewrite /best_approximation /idempotent => π.
    by rewrite (@I2 C A) (@idmp C ϕ).
Qed.

Lemma best_approximation_ext {A C : Set}  (ins : Galois_Insertion C A)
                                          (ϕ : @Uco C) :
                                          extensive (best_approximation ins (uco ϕ)).
Proof.
  rewrite /best_approximation /extensive => π.
  apply: subset_trans.
  exact: (@G1 C A). apply: (@mono_γ C A).
  exact: (@ext C ϕ).
Qed.


Definition uco_sharp {A C : Set} (ϕ : @Uco C)
                                 (ins : Galois_Insertion C A) : @Uco A :=

  @Build_Uco A (@best_approximation A C ins (uco ϕ))
               (@best_approximation_mono A C ins ϕ)
               (@best_approximation_idmp A C ins ϕ)
               (@best_approximation_ext A C ins ϕ).


(************************************)
(*  for relational properties       *)
(************************************)

Definition low_rel_prod  {A C : Set} (rel : C -> A -> Prop) : (C * C -> Prop) -> (A * A -> Prop) :=
  fun c =>
    fun a : A * A => exists x : C * C, c x /\ rel (fst x) (fst a) /\ rel (snd x) (snd a).

Definition up_rel_prod {A C : Set} (rel : C -> A -> Prop) : (A * A -> Prop) -> (C * C -> Prop) :=
  fun a =>
    fun c : C * C => forall y : A * A, rel (fst c) (fst y) -> rel (snd c) (snd y) -> a y.

Lemma induced_adj_law_prod {A C : Set} (rel : C -> A -> Prop) :
  @Adjunction_law (A * A) (C * C) (low_rel_prod rel) (up_rel_prod rel).
Proof.
  move => a c. rewrite /low_rel_prod /up_rel_prod. split.
  + move => H t h_t t' rel_t_t'_fst rel_t_t'_snd.
    apply: H.
    by exists t.
  + move => H x [y [c_y [rel_y_x_1 rel_y_x_2]]]. by apply: (H y).
Qed.

Definition induced_connection_prod {A C : Set} (rel : C -> A -> Prop)
  : Galois_Connection (A * A) (C * C) :=
  Build_Galois_Connection (induced_adj_law_prod rel).


Lemma rel_total_surjective {A C : Set} (rel : C -> A -> Prop):
  more_obs_rel (swap_rel rel) -> (* total and surjective map from A to C *)
  γ (induced_connection rel) = fun (a : A -> Prop) => (fun x : C => exists y : A, rel x y /\ a y).
Proof.
  move => [Hrel1 Hrel2].
  rewrite /γ /= /up_rel. 
  apply: functional_extensionality => a.
  apply: functional_extensionality => x.
  apply: prop_extensionality.
  split.
  + firstorder.
  + move => [y [rel_x_y a_y]] y0 rel_x_y0.    
    move : (Hrel2 y) => [x0 rel_x0_y].
    move : (Hrel1 x) => [y_u rel_x_yu].
    move: rel_x_yu. rewrite /unique. move => [rel_yu_x Hunique].
    have hfoo0 : (swap_rel rel) y0 x by [].
    move: (Hunique y0 hfoo0) => Heq0. subst.  
    have hfoo  : (swap_rel rel) y x by [].
    move: (Hunique y hfoo) => Heq. by subst.
Qed.

Lemma equal_pointwise {X : Set} (π1 π2 : X -> Prop) :
  π1 = π2 -> (forall x : X, π1 x = π2 x).
Proof. move => Heq x. by rewrite Heq. Qed. 

Lemma rel_total_surjective_up_inj {A C : Set} (rel : C -> A -> Prop):
  more_obs_rel (swap_rel rel) -> (* total and surjective map from A to C *)
  (forall π1 π2, π1 <> π2 -> 
   (γ (induced_connection rel) π1) <> (γ (induced_connection rel) π2)).
Proof.
  move => Hrel π1 π2 Hdiff. rewrite (rel_total_surjective Hrel) => Hf.
  apply: Hdiff.
  apply: functional_extensionality => a.
  apply: prop_extensionality.
  move: Hrel. rewrite /swap_rel /=. move =>  [Hrel1 Hrel2]. 
  move: (Hrel2 a) => [c rel_a_c]. move: (Hrel1 c) => [unique_a [rel_unique_c Hunique]].
  split => Hπi.
  have [a' [rel_c_a' π2_a']] : exists a': A, rel c a'  /\ (π2 a').
  { move: (equal_pointwise Hf c) => Heq. rewrite -Heq.
    by exists a. } 
  move: (Hunique a rel_a_c) (Hunique a' rel_c_a') => Heq1 Heq2. by subst.
  (* symmetric case *)
  have [a' [rel_c_a' π2_a']] : exists a': A, rel c a'  /\ (π1 a').
  { move: (equal_pointwise Hf c) => Heq. rewrite Heq.
    by exists a. } 
  move: (Hunique a rel_a_c) (Hunique a' rel_c_a') => Heq1 Heq2. by subst.
Qed. 
