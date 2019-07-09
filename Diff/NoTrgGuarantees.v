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
Require Import NonRobustDef.
Require Import NonRobustTraceCriterion.
Require Import Relation4Correctness.

Hypothesis prop_extensionality : forall A B : Prop, (A <-> B) -> A = B.


(* CA:
  If a progam W__nd has a completely non-detrministic behavior,
  the identity compiler is rel_TC for rel being the cheating relation but
  every target guarantee is lost for all programs.
  In particular if we assume W__good to be s.t. beh(W__good) = {s},
  by compiling with the identity W__good (to itself!)
  the only guarantee is that  "W__good sat ⊤".
 *)

Section Example.

  Variable language: Language.

  Local Definition id_compiler : CompilationChain language language :=
    {| compile_whole := fun x => x ;
       compile_par := fun x => x;
       compile_ctx := fun x => x|}.

  Variable trace : Set.

  Local Definition prop := prop trace.

  Variable Semantics : Semantics language trace.

  Local Definition sem := sem Semantics.
  Local Definition beh := beh Semantics.
  Local Definition prg := prg language.
  Local Definition sat := sat Semantics.

  Local Definition cmp := compile_whole language language id_compiler.

  Local Notation "W ↓" := (cmp W) (at level 50).

  Variable W__nd : prg.
  Hypothesis random_beh : forall s, sem W__nd s.

  Local Definition cheat_rel : trace -> trace -> Prop := rel id_compiler Semantics Semantics.

  Local Definition adjunction := induced_connection cheat_rel.

  Local Definition τ' : prop -> prop := α adjunction.
  Local Definition σ' : prop -> prop := γ adjunction.

  Local Definition τTP := τTP id_compiler
                              Semantics Semantics
                              τ'.


  Local Definition σTP := σTP id_compiler
                              Semantics Semantics
                              σ'.


  Local Definition rel_TC := rel_TC id_compiler
                                    Semantics Semantics
                                    cheat_rel.

  Lemma id_is_rel_TC : rel_TC.
  Proof. by apply: cmp_is_rel_TC. Qed.

  (* under this assumption the image of the abstraction τ' becomes trivial,
       has only two points, ⊥ and ⊤.
   *)
  Lemma abstraction_lemma (π__S : prop):
   (exists s, π__S s) -> (τ' (π__S) = fun _ => True).
  Proof.
    move => [s π_s].
    apply: functional_extensionality => t.
    apply: prop_extensionality. split; auto.
    rewrite /τ' /α /= /low_rel => hfoo.
    destruct (non_empty_sem Semantics W__nd) as [s' behWs'].
    exists s. split.
     - assumption.
     - exists W__nd. split.
       -- apply: random_beh.
       -- rewrite /id_compiler /=. apply: random_beh.
  Qed.

    (* the cheating relation gives no target guarantee *)
    Theorem no_trg_guarantee (W : prg) (π__S : prop):
        (exists s, π__S s) -> sat (W ↓) (τ' π__S).
    Proof.
      move => non_empty_π.
      by rewrite abstraction_lemma.
    Qed.

End Example.