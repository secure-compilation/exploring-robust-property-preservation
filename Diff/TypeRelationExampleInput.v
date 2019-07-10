(* Add LoadPath ".". *)

Inductive SExp :=
  SNat : nat -> SExp
| SBool : bool -> SExp
| SPlus : SExp -> SExp -> SExp
| STimes : SExp -> SExp -> SExp
| SIte : SExp -> SExp -> SExp -> SExp
| SLe : SExp -> SExp -> SExp
| SInBool : SExp
| SInNat : SExp.

Inductive TExp :=
  TNat : nat -> TExp
| TPlus : TExp -> TExp -> TExp
| TTimes : TExp -> TExp -> TExp
| TIte : TExp -> TExp -> TExp -> TExp -> TExp
| TIn : TExp.

Fixpoint compile (se : SExp) : TExp :=
  match se with
    SNat n => TNat n
  | SBool true => TNat 1
  | SBool false => TNat 0
  | SPlus se1 se2 => TPlus (compile se1) (compile se2)
  | STimes se1 se2 => TTimes (compile se1) (compile se2)
  | SLe se1 se2 => TIte (compile se1) (compile se2) (TNat 1) (TNat 0)
  | SIte se1 se2 se3 => TIte (compile se1) (TNat 0) (compile se3) (compile se2)
  | SInBool => TIn
  | SInNat => TIn
  end.

Require Import List.

(* source traces *)

Inductive SResult :=
| SRBool : bool -> SResult
| SRNat : nat -> SResult
| SRError : SResult.

Inductive SInput :=
| SIBoo : bool -> SInput
| SINat : nat -> SInput.

Definition STrace := (list SInput * SResult)%type.

(* target traces *)
Inductive TResult :=
| TRNat : nat -> TResult.

Inductive TInput :=
| TINat : nat -> TInput.

Definition TTrace := (list TInput * TResult)%type.

Import ListNotations.

(* source semantics *)

Inductive ssem : SExp -> STrace -> Prop :=
(* constants *)
| SSNat : forall n,
    ssem (SNat n) (nil, SRNat n)
| SSBool : forall b,
    ssem (SBool b) (nil, SRBool b)
(* source plus *)
| SSPlusSuccess : forall se1 sl1 n1,
    forall se2 sl2 n2,
      ssem se1 (sl1, SRNat n1) ->
      ssem se2 (sl2, SRNat n2) ->
      ssem (SPlus se1 se2) (app sl1 sl2, SRNat (n1 + n2))
| SSPlusLeftBool : forall se1 sl1 b1 se2,
    ssem se1 (sl1, SRBool b1) ->
    ssem (SPlus se1 se2) (sl1, SRError)
| SSPlusLeftError : forall se1 sl1 se2,
    ssem se1 (sl1, SRError) ->
    ssem (SPlus se1 se2) (sl1, SRError)
| SSPlusRightBool : forall se1 sl1 n1,
    forall se2 sl2 b2,
      ssem se1 (sl1, SRNat n1) ->
      ssem se2 (sl2, SRBool b2) ->
      ssem (SPlus se1 se2) (app sl1 sl2, SRError)
| SSPlusRightError : forall se1 sl1 n1,
    forall se2 sl2,
      ssem se1 (sl1, SRNat n1) ->
      ssem se2 (sl2, SRError) ->
      ssem (SPlus se1 se2) (app sl1 sl2, SRError)
(* source times *)
| SSTimesSuccess : forall se1 sl1 n1,
    forall se2 sl2 n2,
      ssem se1 (sl1, SRNat n1) ->
      ssem se2 (sl2, SRNat n2) ->
      ssem (STimes se1 se2) (app sl1 sl2, SRNat (n1 * n2))
| SSTimesLeftBool : forall se1 sl1 b1 se2,
    ssem se1 (sl1, SRBool b1) ->
    ssem (STimes se1 se2) (sl1, SRError)
| SSTimesLeftError : forall se1 sl1 se2,
    ssem se1 (sl1, SRError) ->
    ssem (STimes se1 se2) (sl1, SRError)
| SSTimesRightBool : forall se1 sl1 n1,
    forall se2 sl2 b2,
      ssem se1 (sl1, SRNat n1) ->
      ssem se2 (sl2, SRBool b2) ->
      ssem (STimes se1 se2) (app sl1 sl2, SRError)
| SSTimesRightError : forall se1 sl1 n1,
    forall se2 sl2,
      ssem se1 (sl1, SRNat n1) ->
      ssem se2 (sl2, SRError) ->
      ssem (STimes se1 se2) (app sl1 sl2, SRError)
(* if-then-else *)
| SSIteLeft : forall se1 se2 se3 sl1 sl2 r2,
    ssem se1 (sl1, SRBool true) ->
    ssem se2 (sl2, r2) ->
    ssem (SIte se1 se2 se3) (app sl1 sl2, r2)
| SSIteRight : forall se1 se2 se3 sl1 sl3 r3,
    ssem se1 (sl1, SRBool false) ->
    ssem se3 (sl3, r3) ->
    ssem (SIte se1 se2 se3) (app sl1 sl3, r3)
| SSIteNat : forall se1 se2 se3 sl1 n1,
    ssem se1 (sl1, SRNat n1) ->
    ssem (SIte se1 se2 se3) (sl1, SRError)
| SSIteError : forall se1 se2 se3 sl1,
    ssem se1 (sl1, SRError) ->
    ssem (SIte se1 se2 se3) (sl1, SRError)
(* less-than-or-equal *)
| SSLeSuccess : forall se1 sl1 n1,
    forall se2 sl2 n2,
      ssem se1 (sl1, SRNat n1) ->
      ssem se2 (sl2, SRNat n2) ->
      ssem (SLe se1 se2) (app sl1 sl2, SRBool (Nat.leb n1 n2))
| SSLeLeftBool : forall se1 sl1 b1 se2,
    ssem se1 (sl1, SRBool b1) ->
    ssem (SLe se1 se2) (sl1, SRError)
| SSLeLeftError : forall se1 sl1 se2,
    ssem se1 (sl1, SRError) ->
    ssem (SLe se1 se2) (sl1, SRError)
| SSLeRightBool : forall se1 sl1 n1,
    forall se2 sl2 b2,
      ssem se1 (sl1, SRNat n1) ->
      ssem se2 (sl2, SRBool b2) ->
      ssem (SLe se1 se2) (app sl1 sl2, SRError)
| SSLeRightError : forall se1 sl1 n1,
    forall se2 sl2,
      ssem se1 (sl1, SRNat n1) ->
      ssem se2 (sl2, SRError) ->
      ssem (SLe se1 se2) (app sl1 sl2, SRError)
(* nat input *)
| SSInNatSuccess : forall n,
    ssem SInNat ([SINat n], SRNat n)
(* | SSInNatError : forall b, *)
(*     ssem SInNat ([SIBoo b], SRError) *)
| SSInBoolSuccess : forall b,
    ssem SInBool ([SIBoo b], SRBool b)
(* | SSInBoolError : forall n, *)
(*     ssem SInBool ([SINat n], SRError) *)
.

Inductive tsem : TExp -> TTrace -> Prop :=
| TSNat : forall n,
    tsem (TNat n) (nil, TRNat n)

| TSPlusSuccess : forall le1 ll1 n1,
    forall le2 ll2 n2,
      tsem le1 (ll1, TRNat n1) ->
      tsem le2 (ll2, TRNat n2) ->
      tsem (TPlus le1 le2) (app ll1 ll2, TRNat (n1 + n2))

| TSTimesSuccess : forall le1 ll1 n1,
    forall le2 ll2 n2,
      tsem le1 (ll1, TRNat n1) ->
      tsem le2 (ll2, TRNat n2) ->
      tsem (TTimes le1 le2) (app ll1 ll2, TRNat (n1 * n2))
| TSIteLeft : forall le1 le2 le3 le4 ll1 ll2 ll3 n1 n2 n3,
    tsem le1 (ll1, TRNat n1) ->
    tsem le2 (ll2, TRNat n2) ->
    le n1 n2 ->
    tsem le3 (ll3, TRNat n3) ->
    tsem (TIte le1 le2 le3 le4) (app ll1 (app ll2 ll3), TRNat n3)
| TSIteRight : forall le1 le2 le3 le4 ll1 ll2 ll4 n1 n2 n4,
    tsem le1 (ll1, TRNat n1) ->
    tsem le2 (ll2, TRNat n2) ->
    not (le n1 n2) ->
    tsem le4 (ll4, TRNat n4) ->
    tsem (TIte le1 le2 le3 le4) (app ll1 (app ll2 ll4), TRNat n4)
| TSInput : forall n,
    tsem TIn ([TINat n], TRNat n).

Definition tildeInput (si : SInput) (ti : TInput) : bool :=
  match (si, ti) with
  | (SINat n, TINat m) => PeanoNat.Nat.eqb n m
  | (SIBoo true, TINat (S m)) => true
  | (SIBoo false, TINat 0) => true
  | _ => false
  end.

Fixpoint tildeInputs (sl : list SInput) (tl : list TInput) : bool :=
  match (sl, tl) with
  | ([], []) => true
  | (x :: sl', y :: tl') => andb (tildeInput x y) (tildeInputs sl' tl')
  | _ => false
  end.

Definition tildeResult (sr : SResult) (tr : TResult) :=
  match (sr, tr) with
  | (SRNat n, TRNat m) => PeanoNat.Nat.eqb n m
  | (SRBool true, TRNat (S m)) => true
  | (SRBool false, TRNat 0) => true
  | _ => false
  end.

Definition tilde (st : STrace) (tt : TTrace) : bool :=
  match st, tt with
  | (l1, SRNat n), (l2, TRNat m) => andb (tildeInputs l1 l2) (PeanoNat.Nat.eqb n m)
  | (l1, SRBool true), (l2, TRNat (S m)) => tildeInputs l1 l2
  | (l1, SRBool false), (l2, TRNat 0) => tildeInputs l1 l2
  | _, _ => false
  end.

Inductive type :=
  TyNat
| TyBool.

Inductive typing : SExp -> type -> Prop :=
| type_nat : forall n, typing (SNat n) TyNat
| type_bool : forall b, typing (SBool b) TyBool
| type_plus : forall se1 se2,
    typing se1 TyNat ->
    typing se2 TyNat ->
    typing (SPlus se1 se2) TyNat
| type_times : forall se1 se2,
    typing se1 TyNat ->
    typing se2 TyNat ->
    typing (STimes se1 se2) TyNat
| type_hite : forall se1 se2 se3 t,
    typing se1 TyBool ->
    typing se2 t ->
    typing se3 t ->
    typing (SIte se1 se2 se3) t
| type_hle : forall se1 se2,
    typing se1 TyNat ->
    typing se2 TyNat ->
    typing (SLe se1 se2) TyBool
| type_hinnat :
    typing SInNat TyNat
| type_hinbool :
    typing SInBool TyBool.

Theorem type_correct :
  forall se : SExp,
  forall t : type,
    typing se t ->
    forall l hr,
      ssem se (l, hr) ->
      (t = TyNat -> exists n, hr = SRNat n) /\
      (t = TyBool -> exists b, hr = SRBool b).
Proof.
  induction se; intros; split; intros; subst.
  - exists n. inversion H0. subst. reflexivity.
  - inversion H.
  - inversion H.
  - exists b. inversion H0. subst. reflexivity.
  - (* SPlus *) inversion H0. subst.
    + inversion H. subst.
      specialize (IHse1 TyNat H3 sl1 (SRNat n1)).
      specialize (IHse2 TyNat H5 sl2 (SRNat n2)).
      destruct IHse1 as [ IHse1' IHse1'' ].
      destruct IHse2 as [ IHse2' IHse2'' ].
      assumption.
      assumption.
      exists (plus n1 n2).
      simpl. reflexivity.
    + inversion H. subst.
      specialize (IHse1 TyNat H8 l (SRBool b1) H2).
      destruct IHse1.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHse1 TyNat H8 l SRError H2).
      destruct IHse1.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHse2 TyNat H10 sl2 (SRBool b2) H6).
      destruct IHse2.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHse2 TyNat H10 sl2 SRError H6).
      destruct IHse2.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
  - (* SPlus Bool *) inversion H.
  - (* STimes *) inversion H0. subst.
    + inversion H. subst.
      specialize (IHse1 TyNat H3 sl1 (SRNat n1)).
      specialize (IHse2 TyNat H5 sl2 (SRNat n2)).
      destruct IHse1 as [ IHse1' IHse1'' ].
      destruct IHse2 as [ IHse2' IHse2'' ].
      assumption.
      assumption.
      exists (mult n1 n2).
      simpl. reflexivity.
    + inversion H. subst.
      specialize (IHse1 TyNat H8 l (SRBool b1) H2).
      destruct IHse1.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHse1 TyNat H8 l SRError H2).
      destruct IHse1.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHse2 TyNat H10 sl2 (SRBool b2) H6).
      destruct IHse2.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHse2 TyNat H10 sl2 SRError H6).
      destruct IHse2.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
  - inversion H.
  - (* ite return TyNat *) inversion H. subst. clear H.
    specialize (IHse1 TyBool H4).
    specialize (IHse2 TyNat H6).
    specialize (IHse3 TyNat H7).
    inversion H0; subst.
    + specialize (IHse2 sl2 hr H9).
      destruct IHse2 as [ IHse2 IHse2useless ].
      clear IHse2useless.
      specialize (IHse2 eq_refl).
      assumption.
    + specialize (IHse3 sl3 hr H9).
      destruct IHse3 as [ IHse3 IHse3useless ].
      clear IHse3useless.
      specialize (IHse3 eq_refl).
      assumption.
    + specialize (IHse1 l (SRNat n1) H1).
      destruct IHse1 as [ IHse1useless IHse1 ].
      clear IHse1useless.
      specialize (IHse1 eq_refl).
      destruct IHse1. inversion H.
    + specialize (IHse1 l SRError H1).
      destruct IHse1 as [ IHse1useless IHse1 ].
      clear IHse1useless.
      specialize (IHse1 eq_refl).
      destruct IHse1. inversion H.
  - (* ite return Bool *)
     inversion H. subst. clear H.
    specialize (IHse1 TyBool H4).
    specialize (IHse2 TyBool H6).
    specialize (IHse3 TyBool H7).
    inversion H0; subst.
    + specialize (IHse2 sl2 hr H9).
      destruct IHse2 as [ IHse2useless IHse2 ].
      clear IHse2useless.
      specialize (IHse2 eq_refl).
      assumption.
    + specialize (IHse3 sl3 hr H9).
      destruct IHse3 as [ IHse3useless IHse3 ].
      clear IHse3useless.
      specialize (IHse3 eq_refl).
      assumption.
    + specialize (IHse1 l (SRNat n1) H1).
      destruct IHse1 as [ IHse1useless IHse1 ].
      clear IHse1useless.
      specialize (IHse1 eq_refl).
      destruct IHse1. inversion H.
    + specialize (IHse1 l SRError H1).
      destruct IHse1 as [ IHse1useless IHse1 ].
      clear IHse1useless.
      specialize (IHse1 eq_refl).
      destruct IHse1. inversion H.
  - (* SLe returning nat *)
    inversion H.
  - (* SLe returning bool *)
    inversion H; subst.
    specialize (IHse1 TyNat H3).
    clear H3.
    specialize (IHse2 TyNat H4).
    clear H4.
    inversion H0; subst.
    + exists (Nat.leb n1 n2).
      reflexivity.
    + specialize (IHse1 l (SRBool b1) H2).
      destruct IHse1 as [ IHse1 IHse1useless ].
      clear IHse1useless.
      specialize (IHse1 eq_refl).
      destruct IHse1. inversion H1.
    + specialize (IHse1 l SRError H2).
      destruct IHse1 as [ IHse1 IHse1useless ].
      clear IHse1useless.
      specialize (IHse1 eq_refl).
      destruct IHse1. inversion H1.
    + specialize (IHse2 sl2 (SRBool b2) H6).
      destruct IHse2 as [ IHse2 IHse2useless ].
      clear IHse2useless.
      specialize (IHse2 eq_refl).
      destruct IHse2. inversion H1.
    + specialize (IHse2 sl2 SRError H6).
      destruct IHse2 as [ IHse2 IHse2useless ].
      clear IHse2useless.
      specialize (IHse2 eq_refl).
      destruct IHse2. inversion H1.
  - inversion H.
  - inversion H0.
    exists b. reflexivity.
  - inversion H0.
    exists n. reflexivity.
  - inversion H.
Qed.

Lemma type_correct_nat :
  forall se : SExp,
    typing se TyNat ->
    forall sl sr,
      ssem se (sl, sr) ->
      exists n, sr = SRNat n.
Proof.
  intros.
  assert (Hn :
            ssem se (sl, sr) ->
            (TyNat = TyNat -> exists n, sr = SRNat n) /\
            (TyNat = TyBool -> exists b, sr = SRBool b)).
  apply type_correct; trivial.
  destruct Hn as [ H1 H2 ].
  assumption.
  apply H1.
  reflexivity.
Qed.

Lemma type_correct_bool :
  forall se : SExp,
    typing se TyBool ->
    forall sl sr,
      ssem se (sl, sr) ->
    exists b, sr = SRBool b.
Proof.
  intros.
  assert (Hb :
            ssem se (sl, sr) ->
            (TyBool = TyNat -> exists n, sr = SRNat n) /\
            (TyBool = TyBool -> exists b, sr = SRBool b)).
  apply type_correct; trivial.
  destruct Hb as [ H1 H2 ].
  assumption.
  apply H2.
  reflexivity.
Qed.

Definition translateResult (sr : SResult) : TResult :=
  match sr with
  | SRNat n => TRNat n
  | SRBool true => TRNat 1
  | SRBool false => TRNat 0
  | SRError => TRNat 0
  end.

Fixpoint translateInputs (sl : list SInput) : list TInput :=
  match sl with
  | [] => []
  | SINat n :: sl' => TINat n :: translateInputs sl'
  | SIBoo true :: sl' => TINat 1 :: translateInputs sl'
  | SIBoo false :: sl'  => TINat 0 :: translateInputs sl'
  end.

Theorem tildeInputs_translate :
  forall sl,
    tildeInputs sl (translateInputs sl) = true.
Proof.
  induction sl.
  - reflexivity.
  - destruct a.
    + destruct b.
      * simpl. assumption.
      * simpl. assumption.
    + simpl. unfold tildeInput.
      rewrite PeanoNat.Nat.eqb_refl.
      simpl.
      assumption.
Qed.

Theorem tilde_translate :
  forall st sr,
    not (sr = SRError) ->
    tilde (st, sr) (translateInputs st, translateResult sr) = true.
Proof.
  intros st sr.
  intros Hsr.
  destruct sr.
  - destruct b.
    + unfold translateResult.
      unfold tilde.
      apply tildeInputs_translate.
    + unfold translateResult.
      unfold tilde.
      apply tildeInputs_translate.
  - unfold translateResult.
    unfold tilde.
    rewrite tildeInputs_translate.
    simpl.
    apply PeanoNat.Nat.eqb_refl.
  -

    exfalso. apply Hsr. reflexivity.
Qed.

Theorem type_soundness :
  forall se sl sr ty,
    typing se ty ->
    ssem se (sl, sr) ->
    sr <> SRError.
Proof.
  intros.
  destruct ty.
  - assert (exists n : nat, sr = SRNat n).
    { eapply type_correct_nat.
      apply H.
      apply H0. }
    destruct H1.
    subst.
    intro Hcontra.
    inversion Hcontra.
  - assert (exists b : bool, sr = SRBool b).
    { eapply type_correct_bool.
      apply H.
      apply H0. }
    destruct H1.
    subst.
    intro Hcontra.
    inversion Hcontra.
Qed.

Lemma translateInputs_distr :
  forall sl1 sl2,
    translateInputs (sl1 ++ sl2) =
    (translateInputs sl1) ++ (translateInputs sl2).
Proof.
  intros.
  induction sl1.
  - simpl.
    reflexivity.
  - simpl.
    destruct a.
    + destruct b.
      * simpl.
        rewrite IHsl1.
        reflexivity.
      * simpl.
        rewrite IHsl1.
        reflexivity.
    + simpl.
      rewrite IHsl1.
      reflexivity.
Qed.

Theorem correct_compiler : forall se : SExp, forall ty : type,
      typing se ty ->
      forall sl sr,
        ssem se (sl, sr) ->
        tilde (sl, sr) (translateInputs sl, translateResult sr) = true /\
        tsem (compile se) (translateInputs sl, translateResult sr).
Proof.
  induction se; intros t Ht sl sr HS; inversion Ht; subst; inversion HS; subst.
  - split.
    + simpl. apply PeanoNat.Nat.eqb_refl.
    + constructor.
  - destruct b.
    + split.
      * split; reflexivity.
      * constructor.
    + split.
      * split; reflexivity.
      * constructor.
  - (* SPlus *)
    specialize (IHse1 TyNat H1 sl1 (SRNat n1) H4).
    specialize (IHse2 TyNat H3 sl2 (SRNat n2) H6).
    destruct IHse1 as [ IHse1tilde IHse1tsem ].
    destruct IHse2 as [ IHse2tilde IHse2tsem ].
    split.
    + simpl.
      rewrite tildeInputs_translate.
      rewrite PeanoNat.Nat.eqb_refl.
      reflexivity.
    + simpl. rewrite translateInputs_distr. constructor.
      * assumption.
      * assumption.
  - (* SPlus error *)
    exfalso.
    assert (Hcontra : exists n, SRError = SRNat n).
    { apply (type_correct_nat (SPlus se1 se2) (type_plus se1 se2 H1 H3) sl).
      assumption. }
    inversion Hcontra. inversion H.
  - (* SPlus error left *)
    assert (Hcontra : exists n, SRError = SRNat n).
    { apply (type_correct_nat se1 H1 sl).
      assumption. }
    inversion Hcontra. inversion H.
  - (* SPlus bool right *)
    assert (Hcontra : exists n, SRBool b2 = SRNat n).
    { apply (type_correct_nat se2 H3 sl2).
      assumption. }
    inversion Hcontra. inversion H.
  - (* SPlus error right *)
    assert (Hcontra : exists n, SRError = SRNat n).
    { apply (type_correct_nat se2 H3 sl2).
      assumption. }
    inversion Hcontra. inversion H.
  - (* SRTimes *)
    specialize (IHse1 TyNat H1 sl1 (SRNat n1) H4).
    specialize (IHse2 TyNat H3 sl2 (SRNat n2) H6).
    destruct IHse1 as [ IHse1tilde IHse1tsem ].
    destruct IHse2 as [ IHse2tilde IHse2tsem ].
    split.
    + simpl.
      rewrite tildeInputs_translate.
      rewrite PeanoNat.Nat.eqb_refl.
      reflexivity.
    + simpl. rewrite translateInputs_distr. constructor.
      * assumption.
      * assumption.
  - (* STimes error *)
    exfalso.
    assert (Hcontra : exists n, SRError = SRNat n).
    { apply (type_correct_nat (STimes se1 se2) (type_times se1 se2 H1 H3) sl).
      assumption. }
    inversion Hcontra. inversion H.
  - (* STimes error left *)
    assert (Hcontra : exists n, SRError = SRNat n).
    { apply (type_correct_nat se1 H1 sl).
      assumption. }
    inversion Hcontra. inversion H.
  - (* STimes bool right *)
    assert (Hcontra : exists n, SRBool b2 = SRNat n).
    { apply (type_correct_nat se2 H3 sl2).
      assumption. }
    inversion Hcontra. inversion H.
  - (* STimes error right *)
    assert (Hcontra : exists n, SRError = SRNat n).
    { apply (type_correct_nat se2 H3 sl2).
      assumption. }
    inversion Hcontra. inversion H.
  - (* SIte true *)
    specialize (IHse1 TyBool H2 sl1 (SRBool true) H1).
    specialize (IHse2 t H4 sl2 sr H8).
    destruct IHse1 as [ IHse1tilde IHse1tsem ].
    destruct IHse2 as [ IHse2tilde IHse2tsem ].
    clear IHse3.
    split.
    + rewrite tilde_translate.
      reflexivity.
      eapply type_soundness.
      apply Ht.
      apply HS.
    + simpl.
      rewrite translateInputs_distr.
      replace sl2 with (nil ++ sl2).
      rewrite translateInputs_distr.
      remember (translateResult sr) as tsr.
      destruct tsr.
      eapply TSIteRight.
      * apply IHse1tsem.
      * constructor.
      * intro Hcontra. inversion Hcontra.
      * apply IHse2tsem.
      * simpl. reflexivity.
  - (* SIte false *)
    specialize (IHse1 TyBool H2 sl1 (SRBool false) H1).
    specialize (IHse3 t H5 sl3 sr H8).
    destruct IHse1 as [ IHse1tilde IHse1tsem ].
    destruct IHse3 as [ IHse3tilde IHse3tsem ].
    clear IHse2.
    split.
    + rewrite tilde_translate.
      reflexivity.
      eapply type_soundness.
      apply Ht.
      apply HS.
    + simpl.
      rewrite translateInputs_distr.
      replace sl3 with (nil ++ sl3).
      rewrite translateInputs_distr.
      remember (translateResult sr) as tsr.
      destruct tsr.
      eapply TSIteLeft.
      * apply IHse1tsem.
      * constructor.
      * apply le_n.
      * apply IHse3tsem.
      * simpl. reflexivity.
  - (* SIte error *)
    assert (SRError <> SRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* SIte error *)
    assert (SRError <> SRError).
    eapply type_soundness.
    apply H2.
    apply H0.
    contradiction H. reflexivity.
  - (* SLe *)
    specialize (IHse1 TyNat H1 sl1 (SRNat n1) H4).
    specialize (IHse2 TyNat H3 sl2 (SRNat n2) H6).
    destruct IHse1 as [ IHse1tilde IHse1tsem ].
    destruct IHse2 as [ IHse2tilde IHse2tsem ].
    remember (Nat.leb n1 n2) as b.
    destruct b.
    + split.
      * simpl.
        rewrite tildeInputs_translate.
        reflexivity.
      * simpl.
        rewrite translateInputs_distr.
        replace sl2 with (sl2 ++ []).
        ** rewrite translateInputs_distr.
           eapply TSIteLeft.
           *** apply IHse1tsem.
           *** apply IHse2tsem.
           *** apply PeanoNat.Nat.leb_le.
               rewrite <- Heqb.
               reflexivity.
           *** constructor.
        ** rewrite app_nil_end.
           reflexivity.
    + split.
      * simpl.
        rewrite tildeInputs_translate.
        reflexivity.
      * simpl.
        rewrite translateInputs_distr.
        replace sl2 with (sl2 ++ []).
        ** rewrite translateInputs_distr.
           eapply TSIteRight.
           *** apply IHse1tsem.
           *** apply IHse2tsem.
           *** apply PeanoNat.Nat.leb_nle.
               rewrite <- Heqb.
               reflexivity.
           *** constructor.
        ** rewrite app_nil_end.
           reflexivity.
  - (* SLe error *)
    assert (SRError <> SRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* SLe error *)
    assert (SRError <> SRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* SLe error *)
    assert (SRError <> SRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* SLe error *)
    assert (SRError <> SRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* SInBool *)
    split.
    + unfold translateInputs.
      unfold translateResult.
      destruct b.
      * reflexivity.
      * reflexivity.
    + unfold translateResult.
      unfold translateInputs.
      destruct b.
      * constructor.
      * constructor.
  - (* SInNat *)
    split.
    + unfold translateInputs.
      unfold translateResult.
      simpl.
      rewrite PeanoNat.Nat.eqb_refl.
      unfold tildeInput.
      rewrite PeanoNat.Nat.eqb_refl.
      reflexivity.
    + unfold translateResult.
      unfold translateInputs.
      simpl.
      constructor.
Qed.

Definition sr_is_not_nat (sr : SResult) :=
  sr = SRError \/ sr = SRBool true \/ sr = SRBool false.

Definition sr_is_not_bool (sr : SResult) :=
  forall b, sr <> SRBool b.

Theorem type_soundness_nat :
  forall se sl sr,
    typing se TyNat ->
    ssem se (sl, sr) ->
    sr_is_not_nat sr ->
    False.
Proof.
  intros se sl sr Ht HS Sr.
  inversion Sr; subst.
  - assert (Hcontra : SRError <> SRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    exfalso.
    apply Hcontra.
    reflexivity.
  - destruct H.
    + assert (Hcontra : exists n, sr = SRNat n).
      eapply type_correct_nat.
      apply Ht.
      apply HS.
      subst.
      destruct Hcontra.
      inversion H.
    + assert (Hcontra : exists n, sr = SRNat n).
      eapply type_correct_nat.
      apply Ht.
      apply HS.
      subst.
      destruct Hcontra.
      inversion H.
Qed.

Theorem type_soundness_nat' :
  forall se sl sr,
    typing se TyNat ->
    ssem se (sl, sr) ->
    exists n,
      sr = SRNat n.
Proof.
  intros se sl sr Ht Hssem.
  destruct sr.
  - eapply type_soundness_nat in Ht.
    exfalso.
    assumption.
    apply Hssem.
    unfold sr_is_not_nat.
    right.
    destruct b.
    left. reflexivity.
    right. reflexivity.
  - exists n.
    reflexivity.
  - eapply type_soundness_nat in Ht.
    exfalso.
    assumption.
    apply Hssem.
    unfold sr_is_not_nat.
    left.
    reflexivity.
Qed.

Theorem type_soundness_bool :
  forall se sl sr,
    typing se TyBool ->
    ssem se (sl, sr) ->
    sr_is_not_bool sr ->
    False.
Proof.
  intros se sl sr Ht HS Sr.
  assert (Srtrue : sr <> SRBool true).
  apply Sr.
  assert (Srfalse : sr <> SRBool false).
  apply Sr.
  assert (H : exists b, sr = SRBool b).
  eapply type_correct_bool.
  apply Ht.
  apply HS.
  destruct H.
  destruct x; subst.
  - apply Srtrue. reflexivity.
  - apply Srfalse. reflexivity.
Qed.

Theorem type_soundness_bool' :
  forall se sl sr,
    typing se TyBool ->
    ssem se (sl, sr) ->
    exists n,
      sr = SRBool n.
Proof.
  intros se sl sr Ht Hssem.
  destruct sr.
  - exists b.
    reflexivity.
  - eapply type_soundness_bool in Ht.
    exfalso.
    assumption.
    apply Hssem.
    unfold sr_is_not_bool.
    intros.
    intro Hcontra.
    inversion Hcontra.
  - eapply type_soundness_bool in Ht.
    exfalso.
    assumption.
    apply Hssem.
    unfold sr_is_not_bool.
    intros b Hcontra.
    inversion Hcontra.
Qed.

Theorem at_least_one_trace:
  forall se ty,
    typing se ty ->
    exists sl sr,
      ssem se (sl, sr).
Proof.
  intros se. induction se; intros ty Hty.
  - exists [].
    exists (SRNat n).
    constructor.
  - exists [].
    exists (SRBool b).
    constructor.
  - (* SPlus *)
    inversion Hty; subst.
    specialize (IHse2 TyNat H3).
    specialize (IHse1 TyNat H1).
    destruct IHse2 as [ sl2 IHse2 ].
    destruct IHse2 as [ sr2 IHse2 ].
    destruct IHse1 as [ sl1 IHse1 ].
    destruct IHse1 as [ sr1 IHse1 ].
    destruct sr1.
    + exfalso.
      eapply type_soundness_nat.
      apply H1.
      apply IHse1.
      compute.
      right.
      destruct b.
      * left; reflexivity.
      * right; reflexivity.
    + destruct sr2.
      * exfalso.
        eapply type_soundness_nat.
        apply H3.
        apply IHse2.
        compute.
        right.
        destruct b.
        ** left; reflexivity.
        ** right; reflexivity.
      * exists (sl1 ++ sl2).
        exists (SRNat (n + n0)).
        constructor; assumption.
      * exfalso.
        eapply type_soundness_nat.
        apply H3.
        apply IHse2.
        compute.
        left.
        reflexivity.
    + exfalso.
      eapply type_soundness_nat.
      apply H1.
      apply IHse1.
      compute.
      left.
      reflexivity.
  - (* Times *)
    inversion Hty; subst.
    specialize (IHse2 TyNat H3).
    specialize (IHse1 TyNat H1).
    destruct IHse2 as [ sl2 IHse2 ].
    destruct IHse2 as [ sr2 IHse2 ].
    destruct IHse1 as [ sl1 IHse1 ].
    destruct IHse1 as [ sr1 IHse1 ].
    destruct sr1.
    + exfalso.
      eapply type_soundness_nat.
      apply H1.
      apply IHse1.
      compute.
      right.
      destruct b.
      * left; reflexivity.
      * right; reflexivity.
    + destruct sr2.
      * exfalso.
        eapply type_soundness_nat.
        apply H3.
        apply IHse2.
        compute.
        right.
        destruct b.
        ** left; reflexivity.
        ** right; reflexivity.
      * exists (sl1 ++ sl2).
        exists (SRNat (n * n0)).
        constructor; assumption.
      * exfalso.
        eapply type_soundness_nat.
        apply H3.
        apply IHse2.
        compute.
        left.
        reflexivity.
    + exfalso.
      eapply type_soundness_nat.
      apply H1.
      apply IHse1.
      compute.
      left.
      reflexivity.
  - (* SIte *)
    inversion Hty; subst.
    specialize (IHse1 TyBool H2).
    specialize (IHse2 ty H4).
    specialize (IHse3 ty H5).
    destruct IHse2 as [ sl2 IHse2 ].
    destruct IHse2 as [ sr2 IHse2 ].
    destruct IHse1 as [ sl1 IHse1 ].
    destruct IHse1 as [ sr1 IHse1 ].
    destruct IHse3 as [ sl3 IHse3 ].
    destruct IHse3 as [ sr3 IHse3 ].
    destruct sr1.
    + destruct b.
      * exists (sl1 ++ sl2).
        exists (sr2).
        apply SSIteLeft; assumption.
      * exists (sl1 ++ sl3).
        exists (sr3).
        apply SSIteRight; assumption.
    + exfalso.
      eapply type_soundness_bool.
      apply H2.
      apply IHse1.
      intro.
      intro Hcontra.
      inversion Hcontra.
    + exfalso.
      eapply type_soundness_bool.
      apply H2.
      apply IHse1.
      intro.
      intro Hcontra.
      inversion Hcontra.
  - (* SLe *)
    inversion Hty; subst.
    specialize (IHse2 TyNat H3).
    specialize (IHse1 TyNat H1).
    destruct IHse2 as [ sl2 IHse2 ].
    destruct IHse2 as [ sr2 IHse2 ].
    destruct IHse1 as [ sl1 IHse1 ].
    destruct IHse1 as [ sr1 IHse1 ].
    destruct sr1.
    + exfalso.
      eapply type_soundness_nat.
      apply H1.
      apply IHse1.
      compute.
      right.
      destruct b.
      * left; reflexivity.
      * right; reflexivity.
    + destruct sr2.
      * exfalso.
        eapply type_soundness_nat.
        apply H3.
        apply IHse2.
        compute.
        right.
        destruct b.
        ** left; reflexivity.
        ** right; reflexivity.
      * exists (sl1 ++ sl2).
        exists (SRBool (Nat.leb n n0)).
        constructor; assumption.
      * exfalso.
        eapply type_soundness_nat.
        apply H3.
        apply IHse2.
        compute.
        left.
        reflexivity.
    + exfalso.
      eapply type_soundness_nat.
      apply H1.
      apply IHse1.
      compute.
      left.
      reflexivity.
  - (* SInBool *)
    exists [SIBoo true].
    exists (SRBool true).
    constructor.
  - (* SInNat *)
    exists [SINat 0].
    exists (SRNat 0).
    constructor.
Qed.

Require Import LanguageModel.
Require Import ChainModel.
Require Import NonRobustTraceCriterion.

Set Bullet Behavior "Strict Subproofs".

Section Source.

  Definition sprg := {e : SExp | exists τ, typing e τ }.
  Definition spar := sprg.
  Definition sctx := unit.
  Definition splug (p : spar) (c : sctx) := p.

  Definition source := {| prg := sprg; par := spar; ctx := sctx; plug := splug |}.

  Definition traceS := STrace.

  Definition semS : sprg -> traceS -> Prop := fun p t => ssem (proj1_sig p) t.

  Definition semanticsS : Semantics source traceS.
  Proof.
    exists semS.
    destruct W as [e [[|] Hty]].
    - assert (H : exists sl sr, ssem e (sl, sr)).
      eapply at_least_one_trace.
      apply Hty.
      destruct H as [ sl H ].
      destruct H as [ sr H ].
      exists (sl, sr).
      unfold semS.
      simpl.
      assumption.
    - assert (H : exists sl sr, ssem e (sl, sr)).
      eapply at_least_one_trace.
      apply Hty.
      destruct H as [ sl H ].
      destruct H as [ sr H ].
      exists (sl, sr).
      unfold semS.
      simpl.
      assumption.
  Defined.

End Source.

Section Target.
  Definition tprg := TExp.
  Definition tpar := tprg.
  Definition tctx := unit.
  Definition tplug (p : tpar) (c : tctx) := p.

  Definition target := {| prg := tprg; par := tpar; ctx := tctx; plug := tplug |}.

  Definition traceT := TTrace.

  Definition semT : tprg -> traceT -> Prop := fun p t => tsem p t.
  Definition semanticsT : Semantics target traceT.
  Proof.
    exists semT.
    induction W.
    - { eexists.
      constructor. }
    - { destruct IHW1.
      destruct IHW2.
      unfold semT in *.
      destruct x.
      destruct x0.
      destruct t.
      destruct t0.
      eexists.
      constructor.
      apply H.
      apply H0.
      }
    - { simpl.
      destruct IHW1.
      destruct IHW2.
      unfold semT in *.
      destruct x.
      destruct x0.
      destruct t.
      destruct t0.
      eexists.
      constructor.
      apply H.
      apply H0. }
    - { destruct IHW1.
      destruct IHW2.
      destruct IHW3.
      destruct IHW4.
      unfold semT in *.
      destruct x.
      destruct x0.
      destruct x1.
      destruct x2.
      destruct t.
      destruct t0.
      destruct t1.
      destruct t2.
      remember (Nat.leb n n0) as b.
      destruct b.
      * eexists.
        eapply TSIteLeft.
        apply H.
        apply H0.
        apply PeanoNat.Nat.leb_le.
        symmetry.
        apply Heqb.
        apply H1.
      * eexists.
        eapply TSIteRight.
        apply H.
        apply H0.
        apply PeanoNat.Nat.leb_nle.
        symmetry.
        apply Heqb.
        apply H2. }
    - { eexists.
      unfold semT.
      apply (TSInput 0). }
  Defined.

End Target.

Section CompilationChain.
  Definition compile_w : prg source -> prg target :=
    fun (p : prg source) => compile (proj1_sig p).

  Definition compiler : CompilationChain source target :=
    {| compile_whole := compile_w; compile_par := compile_w; compile_ctx := id |}.

End CompilationChain.

Definition rel_TC := rel_TC compiler semanticsS semanticsT (fun h l => tilde h l = true).

Lemma tildeInputs_rest :
  forall si li sl ll,
    tildeInputs (si :: sl) (li :: ll) = true ->
    tildeInputs sl ll = true.
Proof.
  induction sl.
  {
    simpl.
    intros.
    destruct ll.
    {
      reflexivity.
    }
    {
      rewrite Bool.andb_false_r in *.
      inversion H.
    }
  }
  {
    destruct ll.
    {
      intros.
      unfold tildeInputs in H.
      rewrite Bool.andb_false_r in *.
      inversion H.
    }
    {
      intros.
      inversion H.
      apply andb_prop in H1.
      destruct H1.
      apply andb_prop in H1.
      destruct H1.
      rewrite H0.
      rewrite H1.
      rewrite H2.
      simpl.
      rewrite H1.
      rewrite H2.
      reflexivity.
    }
  }
Qed.

Lemma tildeInputs_app :
  forall sl1 sl2 ll1 ll2,
    tildeInputs sl1 ll1 = true ->
    tildeInputs sl2 ll2 = true ->
    tildeInputs (sl1 ++ sl2) (ll1 ++ ll2) = true.
Proof.
  induction sl1.
  {
    intros sl2 ll1 ll2.
    intros H1.
    intros H2.
    inversion H1.
    destruct ll1.
    {
      simpl.
      assumption.
    }
    {
      inversion H0.
    }
  }
  {
    intros sl2 ll1 ll2.
    intros H1.
    intros H2.
    destruct ll1.
    {
      unfold tildeInputs in H1.
      inversion H1.
    }
    {
      specialize (IHsl1 sl2 ll1 ll2).
      inversion H1.
      apply andb_prop in H0.
      destruct H0.
      rewrite H.
      rewrite H0.
      simpl in *.
      rewrite H.
      simpl.
      apply IHsl1.
      assumption.
      assumption.
    }
  }
Qed.

Lemma tilde_tildeInputs :
  forall sl1 sr1 ll1 lr1,
    tilde (sl1, sr1) (ll1, lr1) = true ->
    tildeInputs sl1 ll1 = true.
Proof.
  intros.
  destruct sr1.
  {
    destruct b.
    destruct lr1.
    destruct n.
    inversion H.
    assumption.
    destruct lr1.
    inversion H.
    destruct n.
    reflexivity.
    inversion H1.
  }
  {
    destruct lr1.
    inversion H.
    apply andb_prop in H1.
    destruct H1.
    rewrite H0.
    simpl.
    symmetry.
    assumption.
  }
  {
    inversion H.
  }
Qed.

Lemma tilde_tildeResult :
  forall sl1 sr1 ll1 lr1,
    tilde (sl1, sr1) (ll1, lr1) = true ->
    tildeResult sr1 lr1 = true.
Proof.
  intros.
  unfold tilde in *.
  destruct sr1.
  {
    destruct b.
    {
      destruct lr1.
      {
        destruct n.
        {
          inversion H.
        }
        {
          reflexivity.
        }
      }
    }
    {
      destruct lr1.
      {
        destruct n.
        {
          reflexivity.
        }
        {
          inversion H.
        }
      }
    }
  }
  {
    destruct lr1.
    apply andb_prop in H.
    destruct H.
    unfold tildeResult.
    assumption.
  }
  {
    inversion H.
  }
Qed.

Lemma ti_tr_tilde :
  forall sl1 sr1 ll1 lr1,
    tildeInputs sl1 ll1 = true ->
    tildeResult sr1 lr1 = true ->
    tilde (sl1, sr1) (ll1, lr1) = true.
Proof.
  intros sl1 sr1 ll1 lr1.
  intros SI.
  intros SR.
  destruct sr1; destruct lr1; inversion SI; inversion SR.
  destruct b; destruct n; inversion H0; inversion H1.
  simpl.
  remember (tildeInputs sl1 ll1) as x.
  destruct x; reflexivity.
  unfold tildeResult in SR.
  simpl.
  reflexivity.
  simpl.
  rewrite SI.
  unfold tildeResult in H1.
  rewrite H1.
  reflexivity.
Qed.

Lemma andb_proj2 :
  forall b1 b2,
    andb b1 b2 = true ->
    b2 = true.
Proof.
  intros; destruct b1; destruct b2; destruct H; reflexivity.
Qed.

Theorem correctness : rel_TC.
Proof.
  unfold rel_TC.
  unfold NonRobustTraceCriterion.rel_TC.
  unfold NonRobustTraceCriterion.cmp.
  unfold compile_whole.
  unfold compiler.
  unfold compile_w.
  unfold NonRobustTraceCriterion.sem__T.
  unfold sem. unfold semanticsT.
  unfold prg.
  simpl.
  unfold sprg.
  simpl.
  unfold semT.
  unfold proj1_sig.
  simpl.
  intros W.
  intros t.
  destruct W as [ se Ht ].
  destruct Ht as [ ty Ht ].
  unfold semS.
  unfold proj1_sig.
  intro H.

  (* eapply correct_compiler in Ht.
  destruct Ht as [ Htilde Htsem ]. *)
  generalize dependent Ht.
  generalize dependent t.
  generalize dependent ty.
  induction se.
  - (* SNat *)
    {
      simpl.
      intros ty.
      intros t.
      intros Htsem.
      intros Ht.
      destruct t as [ li lr ].
      inversion Htsem; subst.
      exists ([], SRNat n).
      split.
      + simpl. apply PeanoNat.Nat.eqb_refl.
      + constructor.
    }
  - (* SBool *) simpl.
    intros ty.
    intros t.
    intros Htsem.
    intros Ht.
    destruct t as [ li lr ].
    destruct b.
    + inversion Htsem; subst.
      exists ([], SRBool true).
      split.
      * simpl. reflexivity.
      * simpl. constructor.
    + inversion Htsem; subst.
      exists ([], SRBool false).
      split.
      * simpl. reflexivity.
      * simpl. constructor.
  - (* SPlus *)
    intros ty.
    intros t Htsem Ht.
    simpl in Htsem.
    inversion Htsem; subst.
    inversion Ht; subst.
    specialize (IHse1 TyNat (ll1, TRNat n1) H1 H2).
    specialize (IHse2 TyNat (ll2, TRNat n2) H3 H5).
    destruct IHse1 as [ s1 IHse1 ].
    destruct IHse2 as [ s2 IHse2 ].
    destruct IHse1 as [ IHse1tilde IHse1ssem ].
    destruct IHse2 as [ IHse2tilde IHse2ssem ].
    destruct s1 as [ sl1 sr1 ].
    destruct s2 as [ sl2 sr2 ].
    apply type_soundness_nat' with (sl := sl1) (sr := sr1) in H2.
    Focus 2.
    apply IHse1ssem.
    destruct H2 as [ n1' H2 ]. subst.
    apply type_soundness_nat' with (sl := sl2) (sr := sr2) in H5.
    Focus 2.
    apply IHse2ssem.
    assert (Hn1 : n1' = n1).
    { inversion IHse1tilde. apply PeanoNat.Nat.eqb_eq.
      eapply andb_proj2. apply H0. }
    destruct H5 as [ n2' H5 ]. subst.
    assert (Hn2 : n2' = n2).
    { inversion IHse2tilde. apply PeanoNat.Nat.eqb_eq.
      eapply andb_proj2. apply H0. }
    subst.
    eexists (sl1 ++ sl2, SRNat (n1 + n2)).
    split.
    unfold tilde.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite tildeInputs_app.
    reflexivity.
    eapply tilde_tildeInputs.
    apply IHse1tilde.
    eapply tilde_tildeInputs.
    apply IHse2tilde.
    constructor.
    apply IHse1ssem.
    apply IHse2ssem.
  - (* STimes *)
    intros ty.
    intros t Htsem Ht.
    simpl in Htsem.
    inversion Htsem; subst.
    inversion Ht; subst.
    specialize (IHse1 TyNat (ll1, TRNat n1) H1 H2).
    specialize (IHse2 TyNat (ll2, TRNat n2) H3 H5).
    destruct IHse1 as [ s1 IHse1 ].
    destruct IHse2 as [ s2 IHse2 ].
    destruct IHse1 as [ IHse1tilde IHse1ssem ].
    destruct IHse2 as [ IHse2tilde IHse2ssem ].
    destruct s1 as [ sl1 sr1 ].
    destruct s2 as [ sl2 sr2 ].
    apply type_soundness_nat' with (sl := sl1) (sr := sr1) in H2.
    Focus 2.
    apply IHse1ssem.
    destruct H2 as [ n1' H2 ]. subst.
    apply type_soundness_nat' with (sl := sl2) (sr := sr2) in H5.
    Focus 2.
    apply IHse2ssem.
    assert (Hn1 : n1' = n1).
    { inversion IHse1tilde. apply PeanoNat.Nat.eqb_eq.
      eapply andb_proj2. apply H0. }
    destruct H5 as [ n2' H5 ]. subst.
    assert (Hn2 : n2' = n2).
    { inversion IHse2tilde. apply PeanoNat.Nat.eqb_eq.
      eapply andb_proj2. apply H0. }
    subst.
    eexists (sl1 ++ sl2, SRNat (n1 * n2)).
    split.
    unfold tilde.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite tildeInputs_app.
    reflexivity.
    eapply tilde_tildeInputs.
    apply IHse1tilde.
    eapply tilde_tildeInputs.
    apply IHse2tilde.
    constructor.
    apply IHse1ssem.
    apply IHse2ssem.
  - (* SIte *)
    intros ty.
    intros t Htsem Ht.
    simpl in Htsem.
    (*
| TSIteLeft : forall le1 le2 le3 le4 ll1 ll2 ll3 n1 n2 n3,
    tsem le1 (ll1, TRNat n1) ->
    tsem le2 (ll2, TRNat n2) ->
    le n1 n2 ->
    tsem le3 (ll3, TRNat n3) ->
    tsem (TIte le1 le2 le3 le4) (app ll1 (app ll2 ll3), TRNat n3)
| TSIteRight : forall le1 le2 le3 le4 ll1 ll2 ll4 n1 n2 n4,
    tsem le1 (ll1, TRNat n1) ->
    tsem le2 (ll2, TRNat n2) ->
    not (le n1 n2) ->
    tsem le4 (ll4, TRNat n4) ->
    tsem (TIte le1 le2 le3 le4) (app ll1 (app ll2 ll4), TRNat n4)
*)
    inversion Htsem as [ | | | le1' le2' le3' le4' ll1 ll2 ll3 n1 n2 n3 Sle1 Sle2 Sle Sle3 | le1' le2' le3' le4' ll1 ll2 ll4 n1 n2 n4 Sle1 Sle2 Sle Sle4 | ]; subst.
    + (* true branch *)
      inversion Ht as [ | | | | se1' se2' se3' t' Ht1 Ht2 Ht3  | | | ]; subst.
      clear Ht.
      specialize (IHse1 TyBool (ll1, TRNat n1) Sle1 Ht1).
      specialize (IHse3 ty (ll3, TRNat n3) Sle3 Ht3).
      destruct IHse1 as [ s1 IHse1 ].
      destruct IHse3 as [ s3 IHse3 ].
      destruct IHse1 as [ IHse1tilde IHse1ssem ].
      destruct IHse3 as [ IHse3tilde IHse3ssem ].
      destruct s1 as [ sl1 sr1 ].
      destruct s3 as [ sl3 sr3 ].
      inversion Sle2. subst.
      inversion Sle; subst.
      clear Sle.
      destruct ty.
      * (* ty = TNat *)
        exists (sl1 ++ [] ++ sl3, SRNat n3).
        split.
        ** apply ti_tr_tilde.
           *** apply tildeInputs_app.
               eapply tilde_tildeInputs.
               apply IHse1tilde.
               apply tildeInputs_app.
               reflexivity.
               eapply tilde_tildeInputs.
               apply IHse3tilde.
           *** unfold tildeResult. apply PeanoNat.Nat.eqb_refl.
        **
           apply SSIteRight.

           {
             destruct sr1.
             *** (* sr1 = SRBool b *)
               destruct b.
               **** (* b = true *)
                 apply tilde_tildeResult in IHse1tilde.
                 unfold tildeResult in IHse1tilde.
                 inversion IHse1tilde.
               **** (* b = false *)
                 assumption.
             *** (* sr1 = SRNat n *)
               (* impossible *)
               assert (Hcontra : exists b : bool, SRNat n = SRBool b).
               eapply type_soundness_bool'.
               apply Ht1.
               apply IHse1ssem.
               destruct Hcontra.
               inversion H.
             *** (* sr1 = SRerror *)
               (* impossible *)
               assert (Hcontra : exists b : bool, SRError = SRBool b).
               eapply type_soundness_bool'.
               apply Ht1.
               apply IHse1ssem.
               destruct Hcontra.
               inversion H.
           }
           {
             simpl.
             destruct sr3.
             *** (* sr3 = SRBool b *)
               (* impossible *)
               assert (Hcontra : exists n' : nat, SRBool b = SRNat n').
               eapply type_soundness_nat'.
               apply Ht3.
               apply IHse3ssem.
               destruct Hcontra.
               inversion H.
             *** (* sr3 = SRNat n *)
                 apply tilde_tildeResult in IHse3tilde.
                 unfold tildeResult in IHse3tilde.
                 apply PeanoNat.Nat.eqb_eq in IHse3tilde.
                 subst.
                 assumption.
             *** (* sr3 = SRerror *)
               (* impossible *)
               assert (Hcontra : exists n' : nat, SRError = SRNat n').
               eapply type_soundness_nat'.
               apply Ht3.
               apply IHse3ssem.
               destruct Hcontra.
               inversion H.
           }
      * (* ty = TBool *)
          destruct sr3.
          {
            (* sr3 = SRBool b *)
            exists (sl1 ++ [] ++ sl3, SRBool b).
            split.
            {
              apply ti_tr_tilde.
              {
                apply tildeInputs_app.
                apply tilde_tildeInputs in IHse1tilde.
                assumption.
                apply tildeInputs_app.
                reflexivity.
                apply tilde_tildeInputs in IHse3tilde.
                assumption.
              }
              {
                apply tilde_tildeResult in IHse3tilde.
                assumption.
              }
            }
            {
              apply SSIteRight.

              {
                destruct sr1.
                *** (* sr1 = SRBool b0 *)
                  destruct b0.
                  **** (* b = true *)
                    apply tilde_tildeResult in IHse1tilde.
                    unfold tildeResult in IHse1tilde.
                    inversion IHse1tilde.
                  **** (* b = false *)
                    assumption.
                *** (* sr1 = SRNat n *)
                  (* impossible *)
                  assert (Hcontra : exists b : bool, SRNat n = SRBool b).
                  eapply type_soundness_bool'.
                  apply Ht1.
                  apply IHse1ssem.
                  destruct Hcontra.
                  inversion H.
                *** (* sr1 = SRerror *)
                  (* impossible *)
                  assert (Hcontra : exists b : bool, SRError = SRBool b).
                  eapply type_soundness_bool'.
                  apply Ht1.
                  apply IHse1ssem.
                  destruct Hcontra.
                  inversion H.
              }
              {
                simpl.
                assumption.
              }
            }
          }
          {
            (* sr3 = SRNat n *)
            (* impossible *)
            assert (Hcontra : exists b : bool, SRNat n = SRBool b).
            eapply type_soundness_bool'.
            apply Ht3.
            apply IHse3ssem.
            destruct Hcontra.
            inversion H.
          }
          {
            (* sr3 = SRError *)
            (* impossible *)
            assert (Hcontra : exists b : bool, SRError = SRBool b).
            eapply type_soundness_bool'.
            apply Ht3.
            apply IHse3ssem.
            destruct Hcontra.
            inversion H.
          }
    +
      inversion Ht as [ | | | | se1' se2' se3' t' Ht1 Ht2 Ht3  | | | ]; subst.
      clear Ht.
      specialize (IHse1 TyBool (ll1, TRNat n1) Sle1 Ht1).
      specialize (IHse2 ty (ll4, TRNat n4) Sle4 Ht2).
      destruct IHse1 as [ s1 IHse1 ].
      destruct IHse2 as [ s2 IHse2 ].
      destruct IHse1 as [ IHse1tilde IHse1ssem ].
      destruct IHse2 as [ IHse2tilde IHse2ssem ].
      destruct s1 as [ sl1 sr1 ].
      destruct s2 as [ sl2 sr2 ].
      inversion Sle2. subst.
      destruct n1 as [ | n1' ].
      {
        exfalso. apply Sle. constructor.
      }
      clear Sle.
      destruct ty.
      * (* ty = TNat *)
        exists (sl1 ++ [] ++ sl2, SRNat n4).
        split.
        ** apply ti_tr_tilde.
           *** apply tildeInputs_app.
               eapply tilde_tildeInputs.
               apply IHse1tilde.
               apply tildeInputs_app.
               reflexivity.
               eapply tilde_tildeInputs.
               apply IHse2tilde.
           *** unfold tildeResult. apply PeanoNat.Nat.eqb_refl.
        **
           apply SSIteLeft.

           {
             destruct sr1.
             *** (* sr1 = SRBool b *)
               destruct b.
               **** (* b = true *)
                 assumption.
               **** (* b = false *)
                 apply tilde_tildeResult in IHse1tilde.
                 unfold tildeResult in IHse1tilde.
                 inversion IHse1tilde.
             *** (* sr1 = SRNat n *)
               (* impossible *)
               assert (Hcontra : exists b : bool, SRNat n = SRBool b).
               eapply type_soundness_bool'.
               apply Ht1.
               apply IHse1ssem.
               destruct Hcontra.
               inversion H.
             *** (* sr1 = SRerror *)
               (* impossible *)
               assert (Hcontra : exists b : bool, SRError = SRBool b).
               eapply type_soundness_bool'.
               apply Ht1.
               apply IHse1ssem.
               destruct Hcontra.
               inversion H.
           }
           {
             simpl.
             destruct sr2.
             *** (* sr2 = SRBool b *)
               (* impossible *)
               assert (Hcontra : exists n' : nat, SRBool b = SRNat n').
               eapply type_soundness_nat'.
               apply Ht2.
               apply IHse2ssem.
               destruct Hcontra.
               inversion H.
             *** (* sr2 = SRNat n *)
                 apply tilde_tildeResult in IHse2tilde.
                 unfold tildeResult in IHse2tilde.
                 apply PeanoNat.Nat.eqb_eq in IHse2tilde.
                 subst.
                 assumption.
             *** (* sr2 = SRerror *)
               (* impossible *)
               assert (Hcontra : exists n' : nat, SRError = SRNat n').
               eapply type_soundness_nat'.
               apply Ht2.
               apply IHse2ssem.
               destruct Hcontra.
               inversion H.
           }
      * (* ty = TBool *)
          destruct sr2.
          {
            (* sr3 = SRBool b *)
            exists (sl1 ++ [] ++ sl2, SRBool b).
            split.
            {
              apply ti_tr_tilde.
              {
                apply tildeInputs_app.
                apply tilde_tildeInputs in IHse1tilde.
                assumption.
                apply tildeInputs_app.
                reflexivity.
                apply tilde_tildeInputs in IHse2tilde.
                assumption.
              }
              {
                apply tilde_tildeResult in IHse2tilde.
                assumption.
              }
            }
            {
              apply SSIteLeft.

              {
                destruct sr1.
                *** (* sr1 = SRBool b0 *)
                  destruct b0.
                  **** (* b = true *)
                    assumption.
                  **** (* b = false *)
                    apply tilde_tildeResult in IHse1tilde.
                    unfold tildeResult in IHse1tilde.
                    inversion IHse1tilde.
                *** (* sr1 = SRNat n *)
                  (* impossible *)
                  assert (Hcontra : exists b : bool, SRNat n = SRBool b).
                  eapply type_soundness_bool'.
                  apply Ht1.
                  apply IHse1ssem.
                  destruct Hcontra.
                  inversion H.
                *** (* sr1 = SRerror *)
                  (* impossible *)
                  assert (Hcontra : exists b : bool, SRError = SRBool b).
                  eapply type_soundness_bool'.
                  apply Ht1.
                  apply IHse1ssem.
                  destruct Hcontra.
                  inversion H.
              }
              {
                simpl.
                assumption.
              }
            }
          }
          {
            (* sr3 = SRNat n *)
            (* impossible *)
            assert (Hcontra : exists b : bool, SRNat n = SRBool b).
            eapply type_soundness_bool'.
            apply Ht2.
            apply IHse2ssem.
            destruct Hcontra.
            inversion H.
          }
          {
            (* sr3 = SRError *)
            (* impossible *)
            assert (Hcontra : exists b : bool, SRError = SRBool b).
            eapply type_soundness_bool'.
            apply Ht2.
            apply IHse2ssem.
            destruct Hcontra.
            inversion H.
          }
  - (* SLe *)
    {
      intros ty.
      intros t Htsem Ht.
      simpl in Htsem.
      inversion Htsem; subst.
      {
        inversion Ht; subst.
        specialize (IHse1 TyNat (ll1, TRNat n1) H3 H1).
        specialize (IHse2 TyNat (ll2, TRNat n2) H5 H4).
        destruct IHse1 as [ s1 IHse1 ].
        destruct IHse2 as [ s2 IHse2 ].
        destruct IHse1 as [ IHse1tilde IHse1ssem ].
        destruct IHse2 as [ IHse2tilde IHse2ssem ].
        destruct s1 as [ sl1 sr1 ].
        destruct s2 as [ sl2 sr2 ].
        apply type_soundness_nat' with (sl := sl1) (sr := sr1) in H1.
        Focus 2.
        apply IHse1ssem.
        destruct H1 as [ n1' H1 ]. subst.
        apply type_soundness_nat' with (sl := sl2) (sr := sr2) in H4.
        Focus 2.
        apply IHse2ssem.
        assert (Hn1 : n1' = n1).
        { inversion IHse1tilde. apply PeanoNat.Nat.eqb_eq.
          eapply andb_proj2. apply H0. }
        destruct H4 as [ n2' H4 ]. subst.
        assert (Hn2 : n2' = n2).
        { inversion IHse2tilde. apply PeanoNat.Nat.eqb_eq.
          eapply andb_proj2. apply H0. }
        subst.
        eexists (sl1 ++ sl2, SRBool (Nat.leb n1 n2)).
        split.
        unfold tilde.
        inversion H7. subst.
        apply PeanoNat.Nat.leb_le in H6.
        rewrite H6.
        rewrite tildeInputs_app.
        reflexivity.
        apply tilde_tildeInputs in IHse1tilde.
        assumption.
        apply tilde_tildeInputs in IHse2tilde.
        rewrite app_nil_r.
        assumption.
        constructor.
        apply IHse1ssem.
        apply IHse2ssem.
      }
      {
        inversion Ht; subst.
        specialize (IHse1 TyNat (ll1, TRNat n1) H3 H1).
        specialize (IHse2 TyNat (ll2, TRNat n2) H5 H4).
        destruct IHse1 as [ s1 IHse1 ].
        destruct IHse2 as [ s2 IHse2 ].
        destruct IHse1 as [ IHse1tilde IHse1ssem ].
        destruct IHse2 as [ IHse2tilde IHse2ssem ].
        destruct s1 as [ sl1 sr1 ].
        destruct s2 as [ sl2 sr2 ].
        apply type_soundness_nat' with (sl := sl1) (sr := sr1) in H1.
        Focus 2.
        apply IHse1ssem.
        destruct H1 as [ n1' H1 ]. subst.
        apply type_soundness_nat' with (sl := sl2) (sr := sr2) in H4.
        Focus 2.
        apply IHse2ssem.
        assert (Hn1 : n1' = n1).
        { inversion IHse1tilde. apply PeanoNat.Nat.eqb_eq.
          eapply andb_proj2. apply H0. }
        destruct H4 as [ n2' H4 ]. subst.
        assert (Hn2 : n2' = n2).
        { inversion IHse2tilde. apply PeanoNat.Nat.eqb_eq.
          eapply andb_proj2. apply H0. }
        subst.
        eexists (sl1 ++ sl2, SRBool (Nat.leb n1 n2)).
        split.
        unfold tilde.
        inversion H7. subst.
        apply PeanoNat.Nat.leb_nle in H6.
        rewrite H6.
        rewrite tildeInputs_app.
        reflexivity.
        apply tilde_tildeInputs in IHse1tilde.
        assumption.
        apply tilde_tildeInputs in IHse2tilde.
        rewrite app_nil_r.
        assumption.
        constructor.
        apply IHse1ssem.
        apply IHse2ssem.
        }
    }
  - (* SInBool *)
    {
      intros ty t Htsem Ht.
      inversion Ht; subst.
      simpl in Htsem.
      destruct t as [ ll lr ].
      destruct lr.
      destruct ll as [ | hd tl ].
      {
        (* ll = []  -- impossible *)
        inversion Htsem.
      }
      {
        (* ll = hd :: tl *)
        destruct tl.
        {
          simpl.
          destruct hd.
          inversion Htsem.
          subst.
          destruct n.
          { (* n = 0 --> false *)
            exists ([SIBoo false], SRBool false).
            split.
            reflexivity.
            constructor.
          }
          {
            (* n > 0 --> true *)
            exists ([SIBoo true], SRBool true).
            split.
            reflexivity.
            constructor.
          }
        }
        {
          (* tl = _ :: _  -- impossible *)
          inversion Htsem.
        }
      }
    }
  - (* SInNat *)
    intros ty t Htsem Ht.
    inversion Ht; subst.
    simpl in Htsem.
    destruct t as [ ll lr ].
    destruct lr.
    destruct ll as [ | hd tl ].
    {
      (* ll = []  -- impossible *)
      inversion Htsem.
    }
    {
      (* ll = hd :: tl *)
      destruct tl.
      {
        simpl.
        destruct hd.
        inversion Htsem.
        subst.
        exists ([SINat n], SRNat n).
        split.
        unfold tilde.
        unfold tildeInputs.
        unfold tildeInput.
        rewrite PeanoNat.Nat.eqb_refl.
        reflexivity.
        constructor.
      }
      {
        (* tl = _ :: _  -- impossible *)
        inversion Htsem.
      }
    }
Qed.
