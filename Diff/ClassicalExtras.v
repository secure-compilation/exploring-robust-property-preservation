Require Export Classical.
Require Export Classical_Pred_Type.

(** This file provides several lemmas
    that we use to facilitate handling classical
    reasonning *)

Lemma dne : forall P : Prop, P <-> ~ ~ P.
Proof.
 intros P. split.
 - intros p np. apply (np p).
 - apply (NNPP P).
Qed.

Lemma imp_equiv : forall P Q : Prop,
    (P -> Q) <-> ~P \/ Q.
Proof.
 intros P Q. split.
- apply imply_to_or.
- intros H p. destruct H.
  + exfalso. apply (H p). + apply H.
Qed.

Lemma not_imp : forall P Q : Prop,
    ~(P -> Q) <-> P /\ ~ Q.
Proof.
  intros P Q. split.
  - apply imply_to_and.
  - intros [p nq] i. apply (nq (i p)).
Qed.

Lemma contra : forall P Q : Prop,
    (P -> Q) <-> (~Q -> ~P).
Proof.
  intros P Q. split.
  - intros H nq p. apply (nq (H p)).
  - intros H p. rewrite -> (dne Q).
    intros nq. apply (H nq p).
Qed.

Lemma de_morgan1 : forall P Q : Prop,
    ~ (P /\ Q) <-> ~P \/ ~Q.
Proof.
  intros P Q. split.
  - apply not_and_or.
  - intros [] [p q]. apply (H p). apply (H q).
Qed.

Lemma de_morgan2 : forall P Q : Prop,
    ~ (P \/ Q) <-> ~P /\ ~Q.
Proof.
  intros P Q. split.
  - apply not_or_and.
  - intros [np nq] []. apply np. assumption. apply (nq H).
Qed.

Lemma not_forall_ex_not : forall (U : Type) (P : U -> Prop),
    ~ (forall n : U, P n) <-> exists n : U, ~ P n.
Proof.
  intros U P. split.
  - apply (not_all_ex_not U P).
  - apply (ex_not_not_all U P).
Qed.

Lemma not_ex_forall_not : forall (U :Type) (P : U -> Prop),
    (~ exists n : U, P n) <-> forall n : U, ~ P n.
Proof.
 intros U P. split.
 - apply not_ex_all_not.
 - intros H [n p]. apply (H n p).
Qed.

Lemma and_implies_or : forall P Q : Prop, P /\ Q -> P \/ Q.
Proof.
  intros P Q [p q]. apply (or_introl p).
Qed.

Lemma not_iff : forall P Q : Prop, ~(P <-> Q) <-> ((P /\ ~Q) \/ (~P /\ Q)).
Proof. intros P Q. tauto. Qed.

Lemma neq_equiv : forall P Q : Prop,
    (P <-> Q) <-> (~P <-> ~Q).
Proof.
  intros P Q. split.
  - intros H. split; intros K ff;
    [ rewrite H in K| rewrite <- H in K ]; now auto.
  - intros H. split; intros K; apply NNPP;
    intros ff; [ rewrite <- H in ff| rewrite H in ff ]; now auto.
Qed.

Lemma not_equiv : forall P Q : Prop,
    ~ (P <-> Q) <-> (P /\ ~ Q) \/ (Q /\ ~ P).
Proof.
  intros P Q. split.
  - intros H. assert (cP : P \/ ~ P) by now apply classic.
    destruct cP as [k | k]; [left | right];
    split; auto; [intros q | apply NNPP; intros q; rewrite neq_equiv in H];
     apply (H (conj (fun _ => q) (fun x : _ => k))).
 - intros [[p q] | [p q]] H; [rewrite H in p | rewrite H in q]; now auto.
Qed.
