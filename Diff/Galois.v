From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import ClassicalExtras.
Require Import MyNotation.

Definition monotone {X Y : Set} (f : (X -> Prop) -> (Y -> Prop)) : Prop :=
  forall (π1 π2: X -> Prop), (π1 ⊆ π2) -> (f π1 ⊆ f π2).

Definition idempotent {X : Set} (f : (X -> Prop) -> (X -> Prop)) : Prop :=
  forall π: X -> Prop, f (f π) = f π.

Definition extensive {X : Set} (f : (X -> Prop) -> (X -> Prop)) : Prop :=
  forall π: X -> Prop, π ⊆ (f π).


Definition lift {X Y : Set} (f :(X -> Prop) -> (Y -> Prop))
                            (H : (X -> Prop) -> Prop) : ((Y -> Prop) -> Prop) :=
  fun (b1 : Y -> Prop) => exists b2, (H b2) /\ b1 = f b2.

(* Definition of the adjunction law *)

Definition Adjunction_law {A C : Set}
           (α : (C -> Prop) -> (A -> Prop))
           (γ : (A -> Prop) -> (C -> Prop)) :=
  forall (a: A -> Prop) (c: C -> Prop),  (α c) ⊆ a <-> c ⊆ (γ a).


(* We define Galois connection between powersets ordered by set inclusion:
     (2^X, ⊆) ⇆ (2^Y, ⊆)
   *)
Structure Galois_Connection (A C : Set) := {
    α : (C -> Prop) -> (A -> Prop);
    γ : (A -> Prop) -> (C -> Prop);
    adjunction_law : Adjunction_law α γ
  }.


Definition Galois_fst {A C : Set}
           (α: (C -> Prop) -> (A -> Prop))
           (γ: (A -> Prop) -> (C -> Prop)) :=
  forall (c: C -> Prop),  c ⊆ (γ (α c)).

Definition Galois_snd {A C : Set}
           (α: (C -> Prop) -> (A -> Prop))
           (γ: (A -> Prop) -> (C -> Prop)) :=
  forall (a : A -> Prop), (α (γ a)) ⊆ a.

Lemma Galois_equiv {A C: Set}
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


Definition Insertion_snd {A C : Set}
           (α: (C -> Prop) -> (A -> Prop))
           (γ: (A -> Prop) -> (C -> Prop)) :=
  forall (a : A -> Prop), (α (γ a)) = a.

Structure Galois_Insertion (A C : Set) := {
            α__i : (C -> Prop) -> (A -> Prop);
            γ__i : (A -> Prop) -> (C -> Prop);
            mono_α : monotone α__i;
            mono_γ : monotone γ__i;
            G1 : Galois_fst α__i γ__i;
            I2 : Insertion_snd α__i γ__i
          }.


Lemma Insertion_coercion_Connection {A C : Set} :
  Galois_Insertion A C -> Galois_Connection A C.
Proof.
  move => [α γ mono_alpha mono_gamma H1 H2].
  have H_adj: Adjunction_law α γ.
  rewrite Galois_equiv. repeat split; auto.
  move => a. rewrite (H2 a). now apply: subset_ref.
  exact (Build_Galois_Connection H_adj).
Qed.

Coercion Insertion_coercion_Connection  : Galois_Insertion >-> Galois_Connection.

  (* Given ∼ ⊆ 2^C × 2^A there is a pair of maps
     α : 2^C -> 2^A,  γ : 2^A -> 2^C, that is a Galois connection
     between (2^C, ⊆) and (2^A, ⊆).
   *)

Definition low_rel  {A C : Set} (rel : C -> A -> Prop) : (C -> Prop) -> (A -> Prop) :=
  fun (c : C -> Prop) =>
    (fun (x : A) => exists (y : C), (c y) /\ rel y x).

Definition up_rel {A C : Set} (rel : C -> A -> Prop) : (A -> Prop) -> (C -> Prop) :=
  fun (a : A -> Prop) =>
    (fun (y : C) => forall (x : A), (rel y x -> a x)).

Lemma induced_adj_law {A C : Set} (rel : C -> A -> Prop) :
  Adjunction_law (low_rel rel) (up_rel rel).
Proof.
  move => a c. rewrite /low_rel /up_rel. split.
  + move => H t h_t t' rel_t_t'. apply: H. by exists t.
                                               + move => H x [y [c_y rel_y_x]]. by apply: (H y).
Qed.

Definition induced_connection {A C : Set} (rel : C -> A -> Prop) : Galois_Connection A C :=
  Build_Galois_Connection (induced_adj_law rel).


(** *upper closure operator  \cite{giacobazzi2018abstract} (pag 7) *)
Record Uco {X: Set} :=
  {
    uco: (X -> Prop) -> (X -> Prop);
    mono: monotone uco;
    idmp: idempotent uco;
    ext : extensive uco
  }.
