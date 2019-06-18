(* Add LoadPath ".". *)

(*

- Should semantics be defined for typed programs only?

- What would type soundness be?

- Maybe go for small-step?

- easy to prove there is a trace in a small-step semantics.

HInBool ~> ( [ HINat _ ], HRError )
HInBool ~> ( [ HIBool true ], HRBool true )
HInBool ~> ( [ HIBool false ], HRBool false )

LInBool ~> ( [ LINat _ ], LRError )
LInBool ~> ( [ LINat 1 ], LRBool true )
LInBool ~> ( [ LINat 0 ], LRBool false )

P = if HInBool then 1 else 0

P! = if cast(LInNat) <= 0 then 0 else 1

1. extend the tilde relation s.t. true <-> 1, 2, 3, ...; false <-> 0; <----

2.A. cast inputs / cast outputs;

2.B. throw an exception on wrong input / cast output;
true | true ==> 1 + 1

2.C. continue w/out cast on inputs / cast output;

2.D. cast input to 1 whenever it is not zero;

2.E. throw an exception on wrong input;

2.F. continue w/out cast on inputs.

LInBool ~> ( [ LINat 2 ], LRNat 1 )

*)

Inductive HExp :=
  HNat : nat -> HExp
| HBool : bool -> HExp
| HPlus : HExp -> HExp -> HExp
| HTimes : HExp -> HExp -> HExp
| HIte : HExp -> HExp -> HExp -> HExp
| HLe : HExp -> HExp -> HExp
| HInBool : HExp
| HInNat : HExp.

Inductive LExp :=
  LNat : nat -> LExp
| LPlus : LExp -> LExp -> LExp
| LTimes : LExp -> LExp -> LExp
| LIte : LExp -> LExp -> LExp -> LExp -> LExp
| LIn : LExp.

Fixpoint compile (he : HExp) : LExp :=
  match he with
    HNat n => LNat n
  | HBool true => LNat 1
  | HBool false => LNat 0
  | HPlus he1 he2 => LPlus (compile he1) (compile he2)
  | HTimes he1 he2 => LTimes (compile he1) (compile he2)
  | HLe he1 he2 => LIte (compile he1) (compile he2) (LNat 1) (LNat 0)
  | HIte he1 he2 he3 => LIte (compile he1) (LNat 0) (compile he3) (compile he2)
  | HInBool => LIn
  | HInNat => LIn
  end.

Require Import List.

Inductive HResult :=
| HRBool : bool -> HResult
| HRNat : nat -> HResult
| HRError : HResult.

Inductive HInput :=
| HIBool : bool -> HInput
| HINat : nat -> HInput.

Definition HTrace := (list HInput * HResult)%type.

Inductive LResult :=
| LRNat : nat -> LResult.

Inductive LInput :=
| LINat : nat -> LInput.

Definition LTrace := (list LInput * LResult)%type.

Import ListNotations.

Inductive hsem : HExp -> HTrace -> Prop :=
| HSNat : forall n,
    hsem (HNat n) (nil, HRNat n)
| HSBool : forall b,
    hsem (HBool b) (nil, HRBool b)

| HSPlusSuccess : forall he1 hl1 n1,
    forall he2 hl2 n2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRNat n2) ->
      hsem (HPlus he1 he2) (app hl1 hl2, HRNat (n1 + n2))
| HSPlusLeftBool : forall he1 hl1 b1 he2,
    hsem he1 (hl1, HRBool b1) ->
    hsem (HPlus he1 he2) (hl1, HRError)
| HSPlusLeftError : forall he1 hl1 he2,
    hsem he1 (hl1, HRError) ->
    hsem (HPlus he1 he2) (hl1, HRError)
| HSPlusRightBool : forall he1 hl1 n1,
    forall he2 hl2 b2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRBool b2) ->
      hsem (HPlus he1 he2) (app hl1 hl2, HRError)
| HSPlusRightError : forall he1 hl1 n1,
    forall he2 hl2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRError) ->
      hsem (HPlus he1 he2) (app hl1 hl2, HRError)

| HSTimesSuccess : forall he1 hl1 n1,
    forall he2 hl2 n2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRNat n2) ->
      hsem (HTimes he1 he2) (app hl1 hl2, HRNat (n1 * n2))
| HSTimesLeftBool : forall he1 hl1 b1 he2,
    hsem he1 (hl1, HRBool b1) ->
    hsem (HTimes he1 he2) (hl1, HRError)
| HSTimesLeftError : forall he1 hl1 he2,
    hsem he1 (hl1, HRError) ->
    hsem (HTimes he1 he2) (hl1, HRError)
| HSTimesRightBool : forall he1 hl1 n1,
    forall he2 hl2 b2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRBool b2) ->
      hsem (HTimes he1 he2) (app hl1 hl2, HRError)
| HSTimesRightError : forall he1 hl1 n1,
    forall he2 hl2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRError) ->
      hsem (HTimes he1 he2) (app hl1 hl2, HRError)
           
| HSIteLeft : forall he1 he2 he3 hl1 hl2 r2,
    hsem he1 (hl1, HRBool true) ->
    hsem he2 (hl2, r2) ->
    hsem (HIte he1 he2 he3) (app hl1 hl2, r2)
| HSIteRight : forall he1 he2 he3 hl1 hl3 r3,
    hsem he1 (hl1, HRBool false) ->
    hsem he3 (hl3, r3) ->
    hsem (HIte he1 he2 he3) (app hl1 hl3, r3)
| HSIteNat : forall he1 he2 he3 hl1 n1,
    hsem he1 (hl1, HRNat n1) ->
    hsem (HIte he1 he2 he3) (hl1, HRError)
| HSIteError : forall he1 he2 he3 hl1,
    hsem he1 (hl1, HRError) ->
    hsem (HIte he1 he2 he3) (hl1, HRError)

| HSLeSuccess : forall he1 hl1 n1,
    forall he2 hl2 n2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRNat n2) ->
      hsem (HLe he1 he2) (app hl1 hl2, HRBool (Nat.leb n1 n2))
| HSLeLeftBool : forall he1 hl1 b1 he2,
    hsem he1 (hl1, HRBool b1) ->
    hsem (HLe he1 he2) (hl1, HRError)
| HSLeLeftError : forall he1 hl1 he2,
    hsem he1 (hl1, HRError) ->
    hsem (HLe he1 he2) (hl1, HRError)
| HSLeRightBool : forall he1 hl1 n1,
    forall he2 hl2 b2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRBool b2) ->
      hsem (HLe he1 he2) (app hl1 hl2, HRError)
| HSLeRightError : forall he1 hl1 n1,
    forall he2 hl2,
      hsem he1 (hl1, HRNat n1) ->
      hsem he2 (hl2, HRError) ->
      hsem (HLe he1 he2) (app hl1 hl2, HRError)
| HSInNatSuccess : forall n,
    hsem HInNat ([HINat n], HRNat n)
(* | HSInNatError : forall b, *)
(*     hsem HInNat ([HIBool b], HRError) *)
| HSInBoolSuccess : forall b,
    hsem HInBool ([HIBool b], HRBool b)
(* | HSInBoolError : forall n, *)
(*     hsem HInBool ([HINat n], HRError) *)
.

Inductive lsem : LExp -> LTrace -> Prop :=
| LSNat : forall n,
    lsem (LNat n) (nil, LRNat n)

| LSPlusSuccess : forall le1 ll1 n1,
    forall le2 ll2 n2,
      lsem le1 (ll1, LRNat n1) ->
      lsem le2 (ll2, LRNat n2) ->
      lsem (LPlus le1 le2) (app ll1 ll2, LRNat (n1 + n2))

| LSTimesSuccess : forall le1 ll1 n1,
    forall le2 ll2 n2,
      lsem le1 (ll1, LRNat n1) ->
      lsem le2 (ll2, LRNat n2) ->
      lsem (LTimes le1 le2) (app ll1 ll2, LRNat (n1 * n2))
| LSIteLeft : forall le1 le2 le3 le4 ll1 ll2 ll3 n1 n2 n3,
    lsem le1 (ll1, LRNat n1) ->
    lsem le2 (ll2, LRNat n2) ->
    le n1 n2 ->
    lsem le3 (ll3, LRNat n3) ->
    lsem (LIte le1 le2 le3 le4) (app ll1 (app ll2 ll3), LRNat n3)
| LSIteRight : forall le1 le2 le3 le4 ll1 ll2 ll4 n1 n2 n4,
    lsem le1 (ll1, LRNat n1) ->
    lsem le2 (ll2, LRNat n2) ->
    not (le n1 n2) ->
    lsem le4 (ll4, LRNat n4) ->
    lsem (LIte le1 le2 le3 le4) (app ll1 (app ll2 ll4), LRNat n4)
| LSInput : forall n,
    lsem LIn ([LINat n], LRNat n).

Definition tildeInput (hi : HInput) (li : LInput) : bool :=
  match (hi, li) with
  | (HINat n, LINat m) => PeanoNat.Nat.eqb n m
  | (HIBool true, LINat (S m)) => true
  | (HIBool false, LINat 0) => true
  | _ => false
  end.

Fixpoint tildeInputs (his : list HInput) (lis : list LInput) : bool :=
  match (his, lis) with
  | ([], []) => true
  | (x :: his', y :: lis') => andb (tildeInput x y) (tildeInputs his' lis')
  | _ => false
  end.

Definition tildeResult (hr : HResult) (lr : LResult) :=
  match (hr, lr) with
  | (HRNat n, LRNat m) => PeanoNat.Nat.eqb n m
  | (HRBool true, LRNat (S m)) => true
  | (HRBool false, LRNat 0) => true
  | _ => false
  end.

Definition tilde (ht : HTrace) (lt : LTrace) : bool :=
  match ht, lt with
  | (l1, HRNat n), (l2, LRNat m) => andb (tildeInputs l1 l2) (PeanoNat.Nat.eqb n m)
  | (l1, HRBool true), (l2, LRNat (S m)) => tildeInputs l1 l2
  | (l1, HRBool false), (l2, LRNat 0) => tildeInputs l1 l2
  | _, _ => false
  end.

Inductive type :=
  TNat
| TBool.

Inductive typing : HExp -> type -> Prop :=
| type_nat : forall n, typing (HNat n) TNat
| type_bool : forall b, typing (HBool b) TBool
| type_plus : forall he1 he2,
    typing he1 TNat ->
    typing he2 TNat ->
    typing (HPlus he1 he2) TNat
| type_times : forall he1 he2,
    typing he1 TNat ->
    typing he2 TNat ->
    typing (HTimes he1 he2) TNat
| type_hite : forall he1 he2 he3 t,
    typing he1 TBool ->
    typing he2 t ->
    typing he3 t ->
    typing (HIte he1 he2 he3) t
| type_hle : forall he1 he2,
    typing he1 TNat ->
    typing he2 TNat ->
    typing (HLe he1 he2) TBool
| type_hinnat :
    typing HInNat TNat
| type_hinbool :
    typing HInBool TBool.

Theorem type_correct :
  forall he : HExp,
  forall t : type,
    typing he t ->
    forall l hr,
      hsem he (l, hr) ->
      (t = TNat -> exists n, hr = HRNat n) /\
      (t = TBool -> exists b, hr = HRBool b).
Proof.
  induction he; intros; split; intros; subst.
  - exists n. inversion H0. subst. reflexivity.
  - inversion H.
  - inversion H.
  - exists b. inversion H0. subst. reflexivity.
  - (* HPlus *) inversion H0. subst.
    + inversion H. subst.
      specialize (IHhe1 TNat H3 hl1 (HRNat n1)).
      specialize (IHhe2 TNat H5 hl2 (HRNat n2)).
      destruct IHhe1 as [ IHhe1' IHhe1'' ].
      destruct IHhe2 as [ IHhe2' IHhe2'' ].
      assumption.
      assumption.
      exists (plus n1 n2).
      simpl. reflexivity.
    + inversion H. subst.
      specialize (IHhe1 TNat H8 l (HRBool b1) H2).
      destruct IHhe1.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHhe1 TNat H8 l HRError H2).
      destruct IHhe1.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHhe2 TNat H10 hl2 (HRBool b2) H6).
      destruct IHhe2.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHhe2 TNat H10 hl2 HRError H6).
      destruct IHhe2.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
  - (* HPlus Bool *) inversion H.
  - (* HTimes *) inversion H0. subst.
    + inversion H. subst.
      specialize (IHhe1 TNat H3 hl1 (HRNat n1)).
      specialize (IHhe2 TNat H5 hl2 (HRNat n2)).
      destruct IHhe1 as [ IHhe1' IHhe1'' ].
      destruct IHhe2 as [ IHhe2' IHhe2'' ].
      assumption.
      assumption.
      exists (mult n1 n2).
      simpl. reflexivity.
    + inversion H. subst.
      specialize (IHhe1 TNat H8 l (HRBool b1) H2).
      destruct IHhe1.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHhe1 TNat H8 l HRError H2).
      destruct IHhe1.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHhe2 TNat H10 hl2 (HRBool b2) H6).
      destruct IHhe2.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
    + inversion H. subst.
      specialize (IHhe2 TNat H10 hl2 HRError H6).
      destruct IHhe2.
      specialize (H1 eq_refl).
      destruct H1.
      inversion H1.
  - inversion H.
  - (* ite return TNat *) inversion H. subst. clear H.
    specialize (IHhe1 TBool H4).
    specialize (IHhe2 TNat H6).
    specialize (IHhe3 TNat H7).
    inversion H0; subst.
    + specialize (IHhe2 hl2 hr H9).
      destruct IHhe2 as [ IHhe2 IHhe2useless ].
      clear IHhe2useless.
      specialize (IHhe2 eq_refl).
      assumption.
    + specialize (IHhe3 hl3 hr H9).
      destruct IHhe3 as [ IHhe3 IHhe3useless ].
      clear IHhe3useless.
      specialize (IHhe3 eq_refl).
      assumption.
    + specialize (IHhe1 l (HRNat n1) H1).
      destruct IHhe1 as [ IHhe1useless IHhe1 ].
      clear IHhe1useless.
      specialize (IHhe1 eq_refl).
      destruct IHhe1. inversion H.
    + specialize (IHhe1 l HRError H1).
      destruct IHhe1 as [ IHhe1useless IHhe1 ].
      clear IHhe1useless.
      specialize (IHhe1 eq_refl).
      destruct IHhe1. inversion H.
  - (* ite return Bool *)
     inversion H. subst. clear H.
    specialize (IHhe1 TBool H4).
    specialize (IHhe2 TBool H6).
    specialize (IHhe3 TBool H7).
    inversion H0; subst.
    + specialize (IHhe2 hl2 hr H9).
      destruct IHhe2 as [ IHhe2useless IHhe2 ].
      clear IHhe2useless.
      specialize (IHhe2 eq_refl).
      assumption.
    + specialize (IHhe3 hl3 hr H9).
      destruct IHhe3 as [ IHhe3useless IHhe3 ].
      clear IHhe3useless.
      specialize (IHhe3 eq_refl).
      assumption.
    + specialize (IHhe1 l (HRNat n1) H1).
      destruct IHhe1 as [ IHhe1useless IHhe1 ].
      clear IHhe1useless.
      specialize (IHhe1 eq_refl).
      destruct IHhe1. inversion H.
    + specialize (IHhe1 l HRError H1).
      destruct IHhe1 as [ IHhe1useless IHhe1 ].
      clear IHhe1useless.
      specialize (IHhe1 eq_refl).
      destruct IHhe1. inversion H.
  - (* HLe returning nat *)
    inversion H.
  - (* HLe returning bool *)
    inversion H; subst.
    specialize (IHhe1 TNat H3).
    clear H3.
    specialize (IHhe2 TNat H4).
    clear H4.
    inversion H0; subst.
    + exists (Nat.leb n1 n2).
      reflexivity.
    + specialize (IHhe1 l (HRBool b1) H2).
      destruct IHhe1 as [ IHhe1 IHhe1useless ].
      clear IHhe1useless.
      specialize (IHhe1 eq_refl).
      destruct IHhe1. inversion H1.
    + specialize (IHhe1 l HRError H2).
      destruct IHhe1 as [ IHhe1 IHhe1useless ].
      clear IHhe1useless.
      specialize (IHhe1 eq_refl).
      destruct IHhe1. inversion H1.
    + specialize (IHhe2 hl2 (HRBool b2) H6).
      destruct IHhe2 as [ IHhe2 IHhe2useless ].
      clear IHhe2useless.
      specialize (IHhe2 eq_refl).
      destruct IHhe2. inversion H1.
    + specialize (IHhe2 hl2 HRError H6).
      destruct IHhe2 as [ IHhe2 IHhe2useless ].
      clear IHhe2useless.
      specialize (IHhe2 eq_refl).
      destruct IHhe2. inversion H1.
  - inversion H.
  - inversion H0.
    exists b. reflexivity.
  - inversion H0.
    exists n. reflexivity.
  - inversion H.
Qed.
 
Lemma type_correct_nat :
  forall he : HExp,
    typing he TNat ->
    forall hl hr,
      hsem he (hl, hr) ->
      exists n, hr = HRNat n.
Proof.
  intros.
  assert (Hn : 
             hsem he (hl, hr) ->
             (TNat = TNat -> exists n, hr = HRNat n) /\
             (TNat = TBool -> exists b, hr = HRBool b)).
  apply type_correct; trivial.
  destruct Hn as [ H1 H2 ].
  assumption.
  apply H1.
  reflexivity.
Qed.

Lemma type_correct_bool :
  forall he : HExp,
    typing he TBool ->
    forall hl hr,
      hsem he (hl, hr) ->
    exists b, hr = HRBool b.
Proof.
  intros.
  assert (Hb :
            hsem he (hl, hr) ->
            (TBool = TNat -> exists n, hr = HRNat n) /\
            (TBool = TBool -> exists b, hr = HRBool b)).
  apply type_correct; trivial.
  destruct Hb as [ H1 H2 ].
  assumption.
  apply H2.
  reflexivity.
Qed.

Definition translateResult (hr : HResult) : LResult :=
  match hr with
  | HRNat n => LRNat n
  | HRBool true => LRNat 1
  | HRBool false => LRNat 0
  | HRError => LRNat 0
  end.

Fixpoint translateInputs (hl : list HInput) : list LInput :=
  match hl with
  | [] => []
  | HINat n :: hl' => LINat n :: translateInputs hl'
  | HIBool true :: hl' => LINat 1 :: translateInputs hl'
  | HIBool false :: hl'  => LINat 0 :: translateInputs hl'
  end.

Theorem tildeInputs_translate :
  forall hl,
    tildeInputs hl (translateInputs hl) = true.
Proof.
  induction hl.
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
  forall h x,
    not (x = HRError) ->
    tilde (h, x) (translateInputs h, translateResult x) = true.
Proof.
  intros h x.
  intros Hx.
  destruct x.
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

    exfalso. apply Hx. reflexivity.
Qed.

Theorem type_soundness :
  forall he hl hr t,
    typing he t ->
    hsem he (hl, hr) ->
    hr <> HRError.
Proof.
  intros.
  destruct t.
  - assert (exists n : nat, hr = HRNat n).
    { eapply type_correct_nat.
      apply H.
      apply H0. }
    destruct H1.
    subst.
    intro Hcontra.
    inversion Hcontra.
  - assert (exists b : bool, hr = HRBool b).
    { eapply type_correct_bool.
      apply H.
      apply H0. }
    destruct H1.
    subst.
    intro Hcontra.
    inversion Hcontra.
Qed.

Lemma translateInputs_distr :
  forall hl1 hl2,
    translateInputs (hl1 ++ hl2) =
    (translateInputs hl1) ++ (translateInputs hl2).
Proof.
  intros.
  induction hl1.
  - simpl.
    reflexivity.
  - simpl.
    destruct a.
    + destruct b.
      * simpl.
        rewrite IHhl1.
        reflexivity.
      * simpl.
        rewrite IHhl1.
        reflexivity.
    + simpl.
      rewrite IHhl1.
      reflexivity.
Qed.

Theorem correct_compiler : forall he : HExp, forall t : type,
      typing he t ->
      forall hl hr,
        hsem he (hl, hr) ->
        tilde (hl, hr) (translateInputs hl, translateResult hr) = true /\
        lsem (compile he) (translateInputs hl, translateResult hr).
Proof.
  induction he; intros t Ht hl hr HS; inversion Ht; subst; inversion HS; subst.
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
  - (* HPlus *)
    specialize (IHhe1 TNat H1 hl1 (HRNat n1) H4).
    specialize (IHhe2 TNat H3 hl2 (HRNat n2) H6).
    destruct IHhe1 as [ IHhe1tilde IHhe1lsem ].
    destruct IHhe2 as [ IHhe2tilde IHhe2lsem ].
    split.
    + simpl.
      rewrite tildeInputs_translate.
      rewrite PeanoNat.Nat.eqb_refl.
      reflexivity.
    + simpl. rewrite translateInputs_distr. constructor.
      * assumption.
      * assumption.
  - (* HPlus error *)
    exfalso. 
    assert (Hcontra : exists n, HRError = HRNat n).
    { apply (type_correct_nat (HPlus he1 he2) (type_plus he1 he2 H1 H3) hl).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HPlus error left *)
    assert (Hcontra : exists n, HRError = HRNat n).
    { apply (type_correct_nat he1 H1 hl).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HPlus bool right *)
    assert (Hcontra : exists n, HRBool b2 = HRNat n).
    { apply (type_correct_nat he2 H3 hl2).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HPlus error right *)
    assert (Hcontra : exists n, HRError = HRNat n).
    { apply (type_correct_nat he2 H3 hl2).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HRTimes *)
    specialize (IHhe1 TNat H1 hl1 (HRNat n1) H4).
    specialize (IHhe2 TNat H3 hl2 (HRNat n2) H6).
    destruct IHhe1 as [ IHhe1tilde IHhe1lsem ].
    destruct IHhe2 as [ IHhe2tilde IHhe2lsem ].
    split.
    + simpl.
      rewrite tildeInputs_translate.
      rewrite PeanoNat.Nat.eqb_refl.
      reflexivity.
    + simpl. rewrite translateInputs_distr. constructor.
      * assumption.
      * assumption.
  - (* HTimes error *)
    exfalso. 
    assert (Hcontra : exists n, HRError = HRNat n).
    { apply (type_correct_nat (HTimes he1 he2) (type_times he1 he2 H1 H3) hl).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HTimes error left *)
    assert (Hcontra : exists n, HRError = HRNat n).
    { apply (type_correct_nat he1 H1 hl).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HTimes bool right *)
    assert (Hcontra : exists n, HRBool b2 = HRNat n).
    { apply (type_correct_nat he2 H3 hl2).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HTimes error right *)
    assert (Hcontra : exists n, HRError = HRNat n).
    { apply (type_correct_nat he2 H3 hl2).
      assumption. }
    inversion Hcontra. inversion H.
  - (* HIte true *)
    specialize (IHhe1 TBool H2 hl1 (HRBool true) H1).
    specialize (IHhe2 t H4 hl2 hr H8).
    destruct IHhe1 as [ IHhe1tilde IHhe1lsem ].
    destruct IHhe2 as [ IHhe2tilde IHhe2lsem ].
    clear IHhe3.
    split.
    + rewrite tilde_translate. 
      reflexivity.
      eapply type_soundness.
      apply Ht.
      apply HS.
    + simpl.
      rewrite translateInputs_distr.
      replace hl2 with (nil ++ hl2).
      rewrite translateInputs_distr.
      remember (translateResult hr) as thr.
      destruct thr. 
      eapply LSIteRight.
      * apply IHhe1lsem.
      * constructor.
      * intro Hcontra. inversion Hcontra.
      * apply IHhe2lsem.
      * simpl. reflexivity.
  - (* HIte false *)
    specialize (IHhe1 TBool H2 hl1 (HRBool false) H1).
    specialize (IHhe3 t H5 hl3 hr H8).
    destruct IHhe1 as [ IHhe1tilde IHhe1lsem ].
    destruct IHhe3 as [ IHhe3tilde IHhe3lsem ].
    clear IHhe2.
    split.
    + rewrite tilde_translate. 
      reflexivity.
      eapply type_soundness.
      apply Ht.
      apply HS.
    + simpl.
      rewrite translateInputs_distr.
      replace hl3 with (nil ++ hl3).
      rewrite translateInputs_distr.
      remember (translateResult hr) as thr.
      destruct thr. 
      eapply LSIteLeft.
      * apply IHhe1lsem.
      * constructor.
      * apply le_n.
      * apply IHhe3lsem.
      * simpl. reflexivity.
  - (* HIte error *)
    assert (HRError <> HRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* HIte error *)
    assert (HRError <> HRError).
    eapply type_soundness.
    apply H2.
    apply H0.
    contradiction H. reflexivity.
  - (* HLe *)
    specialize (IHhe1 TNat H1 hl1 (HRNat n1) H4).
    specialize (IHhe2 TNat H3 hl2 (HRNat n2) H6).
    destruct IHhe1 as [ IHhe1tilde IHhe1lsem ].
    destruct IHhe2 as [ IHhe2tilde IHhe2lsem ].
    remember (Nat.leb n1 n2) as b.
    destruct b.
    + split.
      * simpl.
        rewrite tildeInputs_translate.
        reflexivity.
      * simpl.
        rewrite translateInputs_distr.
        replace hl2 with (hl2 ++ []).
        ** rewrite translateInputs_distr.
           eapply LSIteLeft.
           *** apply IHhe1lsem.
           *** apply IHhe2lsem.
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
        replace hl2 with (hl2 ++ []).
        ** rewrite translateInputs_distr.
           eapply LSIteRight.
           *** apply IHhe1lsem.
           *** apply IHhe2lsem.
           *** apply PeanoNat.Nat.leb_nle.
               rewrite <- Heqb.
               reflexivity.
           *** constructor.
        ** rewrite app_nil_end.
           reflexivity.
  - (* HLe error *)
    assert (HRError <> HRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* HLe error *)
    assert (HRError <> HRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* HLe error *)
    assert (HRError <> HRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* HLe error *)
    assert (HRError <> HRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    contradiction H. reflexivity.
  - (* HInBool *)
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
  - (* HInNat *)
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

Definition hr_is_not_nat (hr : HResult) :=
  hr = HRError \/ hr = HRBool true \/ hr = HRBool false.

Definition hr_is_not_bool (hr : HResult) :=
  forall b, hr <> HRBool b.

Theorem type_soundness_nat :
  forall he hl hr,
    typing he TNat ->
    hsem he (hl, hr) ->
    hr_is_not_nat hr ->
    False.
Proof.
  intros he hl hr Ht HS Hr.
  inversion Hr; subst.
  - assert (Hcontra : HRError <> HRError).
    eapply type_soundness.
    apply Ht.
    apply HS.
    exfalso.
    apply Hcontra.
    reflexivity.
  - destruct H.
    + assert (Hcontra : exists n, hr = HRNat n).
      eapply type_correct_nat.
      apply Ht.
      apply HS.
      subst.
      destruct Hcontra.
      inversion H.
    + assert (Hcontra : exists n, hr = HRNat n).
      eapply type_correct_nat.
      apply Ht.
      apply HS.
      subst.
      destruct Hcontra.
      inversion H.
Qed.

Theorem type_soundness_nat' :
  forall he hl hr,
    typing he TNat ->
    hsem he (hl, hr) ->
    exists n,
      hr = HRNat n.
Proof.
  intros he hl hr Ht Hhsem.
  destruct hr.
  - eapply type_soundness_nat in Ht.
    exfalso.
    assumption.
    apply Hhsem.
    unfold hr_is_not_nat.
    right.
    destruct b.
    left. reflexivity.
    right. reflexivity.
  - exists n.
    reflexivity.
  - eapply type_soundness_nat in Ht.
    exfalso.
    assumption.
    apply Hhsem.
    unfold hr_is_not_nat.
    left.
    reflexivity.
Qed.
   
Theorem type_soundness_bool :
  forall he hl hr,
    typing he TBool ->
    hsem he (hl, hr) ->
    hr_is_not_bool hr ->
    False.
Proof.
  intros he hl hr Ht HS Hr.
  assert (Hrtrue : hr <> HRBool true).
  apply Hr.
  assert (Hrfalse : hr <> HRBool false).
  apply Hr.
  assert (H : exists b, hr = HRBool b).
  eapply type_correct_bool.
  apply Ht.
  apply HS.
  destruct H.
  destruct x; subst.
  - apply Hrtrue. reflexivity.
  - apply Hrfalse. reflexivity.
Qed.

Theorem type_soundness_bool' :
  forall he hl hr,
    typing he TBool ->
    hsem he (hl, hr) ->
    exists n,
      hr = HRBool n.
Proof.
  intros he hl hr Ht Hhsem.
  destruct hr.
  - exists b.
    reflexivity.
  - eapply type_soundness_bool in Ht.
    exfalso.
    assumption.
    apply Hhsem.
    unfold hr_is_not_bool.
    intros.
    intro Hcontra.
    inversion Hcontra.
  - eapply type_soundness_bool in Ht.
    exfalso.
    assumption.
    apply Hhsem.
    unfold hr_is_not_bool.
    intros b Hcontra.
    inversion Hcontra.
Qed.
  
Theorem at_least_one_trace:
  forall he t,
    typing he t ->
    exists hl hr,
      hsem he (hl, hr).
Proof.
  intros he. induction he; intros t Ht.
  - exists [].
    exists (HRNat n).
    constructor.
  - exists [].
    exists (HRBool b).
    constructor.
  - (* HPlus *)
    inversion Ht; subst.
    specialize (IHhe2 TNat H3).
    specialize (IHhe1 TNat H1).
    destruct IHhe2 as [ hl2 IHhe2 ].
    destruct IHhe2 as [ hr2 IHhe2 ].
    destruct IHhe1 as [ hl1 IHhe1 ].
    destruct IHhe1 as [ hr1 IHhe1 ].
    destruct hr1.
    + exfalso.
      eapply type_soundness_nat.
      apply H1.
      apply IHhe1.
      compute.
      right.
      destruct b.
      * left; reflexivity.
      * right; reflexivity.
    + destruct hr2.
      * exfalso.
        eapply type_soundness_nat.
        apply H3.
        apply IHhe2.
        compute.
        right.
        destruct b.
        ** left; reflexivity.
        ** right; reflexivity.
      * exists (hl1 ++ hl2).
        exists (HRNat (n + n0)).
        constructor; assumption.
      * exfalso.
        eapply type_soundness_nat.
        apply H3.
        apply IHhe2.
        compute.
        left.
        reflexivity.
    + exfalso.
      eapply type_soundness_nat.
      apply H1.
      apply IHhe1.
      compute.
      left.
      reflexivity.
  - (* Times *)
    inversion Ht; subst.
    specialize (IHhe2 TNat H3).
    specialize (IHhe1 TNat H1).
    destruct IHhe2 as [ hl2 IHhe2 ].
    destruct IHhe2 as [ hr2 IHhe2 ].
    destruct IHhe1 as [ hl1 IHhe1 ].
    destruct IHhe1 as [ hr1 IHhe1 ].
    destruct hr1.
    + exfalso.
      eapply type_soundness_nat.
      apply H1.
      apply IHhe1.
      compute.
      right.
      destruct b.
      * left; reflexivity.
      * right; reflexivity.
    + destruct hr2.
      * exfalso.
        eapply type_soundness_nat.
        apply H3.
        apply IHhe2.
        compute.
        right.
        destruct b.
        ** left; reflexivity.
        ** right; reflexivity.
      * exists (hl1 ++ hl2).
        exists (HRNat (n * n0)).
        constructor; assumption.
      * exfalso.
        eapply type_soundness_nat.
        apply H3.
        apply IHhe2.
        compute.
        left.
        reflexivity.
    + exfalso.
      eapply type_soundness_nat.
      apply H1.
      apply IHhe1.
      compute.
      left.
      reflexivity.
  - (* HIte *)
    inversion Ht; subst.
    specialize (IHhe1 TBool H2).
    specialize (IHhe2 t H4).
    specialize (IHhe3 t H5).
    destruct IHhe2 as [ hl2 IHhe2 ].
    destruct IHhe2 as [ hr2 IHhe2 ].
    destruct IHhe1 as [ hl1 IHhe1 ].
    destruct IHhe1 as [ hr1 IHhe1 ].
    destruct IHhe3 as [ hl3 IHhe3 ].
    destruct IHhe3 as [ hr3 IHhe3 ].
    destruct hr1.
    + destruct b.
      * exists (hl1 ++ hl2).
        exists (hr2).
        apply HSIteLeft; assumption.
      * exists (hl1 ++ hl3).
        exists (hr3).
        apply HSIteRight; assumption.
    + exfalso.
      eapply type_soundness_bool.
      apply H2.
      apply IHhe1.
      intro.
      intro Hcontra.
      inversion Hcontra.
    + exfalso.
      eapply type_soundness_bool.
      apply H2.
      apply IHhe1.
      intro.
      intro Hcontra.
      inversion Hcontra.
  - (* HLe *)
    inversion Ht; subst.
    specialize (IHhe2 TNat H3).
    specialize (IHhe1 TNat H1).
    destruct IHhe2 as [ hl2 IHhe2 ].
    destruct IHhe2 as [ hr2 IHhe2 ].
    destruct IHhe1 as [ hl1 IHhe1 ].
    destruct IHhe1 as [ hr1 IHhe1 ].
    destruct hr1.
    + exfalso.
      eapply type_soundness_nat.
      apply H1.
      apply IHhe1.
      compute.
      right.
      destruct b.
      * left; reflexivity.
      * right; reflexivity.
    + destruct hr2.
      * exfalso.
        eapply type_soundness_nat.
        apply H3.
        apply IHhe2.
        compute.
        right.
        destruct b.
        ** left; reflexivity.
        ** right; reflexivity.
      * exists (hl1 ++ hl2).
        exists (HRBool (Nat.leb n n0)).
        constructor; assumption.
      * exfalso.
        eapply type_soundness_nat.
        apply H3.
        apply IHhe2.
        compute.
        left.
        reflexivity.
    + exfalso.
      eapply type_soundness_nat.
      apply H1.
      apply IHhe1.
      compute.
      left.
      reflexivity.
  - (* HInBool *)
    exists [HIBool true].
    exists (HRBool true).
    constructor.
  - (* HInNat *)
    exists [HINat 0].
    exists (HRNat 0).
    constructor.
Qed.

Require Import LanguageModel.
Require Import ChainModel.
Require Import NonRobustTraceCriterion.

Section Source.

  Definition sprg := {e : HExp | exists τ, typing e τ }.
  Definition spar := sprg.
  Definition sctx := unit.
  Definition splug (p : spar) (c : sctx) := p.

  Definition source := {| prg := sprg; par := spar; ctx := sctx; plug := splug |}.

  Definition traceS := HTrace.

  Definition semS : sprg -> traceS -> Prop := fun p t => hsem (proj1_sig p) t.

  Definition semanticsS : Semantics source traceS.
  Proof.
    exists semS.
    destruct W as [e [[|] Hty]].
    - assert (H : exists hl hr, hsem e (hl, hr)).
      eapply at_least_one_trace.
      apply Hty.
      destruct H as [ hl H ].
      destruct H as [ hr H ].
      exists (hl, hr).
      unfold semS.
      simpl.
      assumption.
    - assert (H : exists hl hr, hsem e (hl, hr)).
      eapply at_least_one_trace.
      apply Hty.
      destruct H as [ hl H ].
      destruct H as [ hr H ].
      exists (hl, hr).
      unfold semS.
      simpl.
      assumption.
  Defined.

End Source.

Section Target.
  Definition tprg := LExp.
  Definition tpar := tprg.
  Definition tctx := unit.
  Definition tplug (p : tpar) (c : tctx) := p.

  Definition target := {| prg := tprg; par := tpar; ctx := tctx; plug := tplug |}.

  Definition traceT := LTrace.

  Definition semT : tprg -> traceT -> Prop := fun p t => lsem p t.
  Definition semanticsT : Semantics target traceT.
  Proof.
    exists semT.
    induction W.
    - eexists.
      constructor.
    - destruct IHW1.
      destruct IHW2.
      unfold semT in *.
      destruct x.
      destruct l0.
      destruct x0.
      destruct l1.
      eexists.
      constructor.
      apply H.
      apply H0.
    - destruct IHW1.
      destruct IHW2.
      unfold semT in *.
      destruct x.
      destruct l0.
      destruct x0.
      destruct l1.
      eexists.
      constructor.
      apply H.
      apply H0.
    - destruct IHW1.
      destruct IHW2.
      destruct IHW3.
      destruct IHW4.
      unfold semT in *.
      destruct x.
      destruct l0.
      destruct x0.
      destruct l1.
      destruct x1.
      destruct l2.
      destruct x2.
      destruct l3.
      remember (Nat.leb n n0) as b.
      destruct b.
      * eexists.
        eapply LSIteLeft.
        apply H.
        apply H0.
        apply PeanoNat.Nat.leb_le.
        symmetry.
        apply Heqb.
        apply H1.
      * eexists.
        eapply LSIteRight.
        apply H.
        apply H0.
        apply PeanoNat.Nat.leb_nle.
        symmetry.
        apply Heqb.
        apply H2.
    - eexists.
      unfold semT.
      apply (LSInput 0).
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
  forall hi li hl ll,
    tildeInputs (hi :: hl) (li :: ll) = true ->
    tildeInputs hl ll = true.
Proof.
  induction hl.
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
  forall hl1 hl2 ll1 ll2,
    tildeInputs hl1 ll1 = true ->
    tildeInputs hl2 ll2 = true ->
    tildeInputs (hl1 ++ hl2) (ll1 ++ ll2) = true.
Proof.
  induction hl1.
  {
    intros hl2 ll1 ll2.
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
    intros hl2 ll1 ll2.
    intros H1.
    intros H2.
    destruct ll1.
    {
      unfold tildeInputs in H1.
      inversion H1.
    }
    {
      specialize (IHhl1 hl2 ll1 ll2).
      inversion H1.
      apply andb_prop in H0.
      destruct H0.
      rewrite H.
      rewrite H0.
      simpl in *.
      rewrite H.
      simpl.
      apply IHhl1.
      assumption.
      assumption.
    }
  }
Qed.

Lemma tilde_tildeInputs :
  forall hl1 hr1 ll1 lr1,
    tilde (hl1, hr1) (ll1, lr1) = true ->
    tildeInputs hl1 ll1 = true.
Proof.
  intros.
  destruct hr1.
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
  forall hl1 hr1 ll1 lr1,
    tilde (hl1, hr1) (ll1, lr1) = true ->
    tildeResult hr1 lr1 = true.
Proof.
  intros.
  unfold tilde in *.
  destruct hr1.
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
  forall hl1 hr1 ll1 lr1,
    tildeInputs hl1 ll1 = true ->
    tildeResult hr1 lr1 = true ->
    tilde (hl1, hr1) (ll1, lr1) = true.
Proof.
  intros hl1 hr1 ll1 lr1.
  intros HI.
  intros HR.
  destruct hr1; destruct lr1; inversion HI; inversion HR.
  destruct b; destruct n; inversion H0; inversion H1.
  simpl.
  remember (tildeInputs hl1 ll1) as x.
  destruct x; reflexivity.
  unfold tildeResult in HR.
  simpl.
  reflexivity.
  simpl.
  rewrite HI.
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

Lemma correctness : rel_TC.
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
  destruct W as [ he Ht ].
  destruct Ht as [ ty Ht ].
  unfold semS.
  unfold proj1_sig.
  intro H.

  (* eapply correct_compiler in Ht.
  destruct Ht as [ Htilde Hlsem ]. *)
  generalize dependent Ht.
  generalize dependent t.
  generalize dependent ty.
  induction he.
  - (* HNat *)
    {
      simpl.
      intros ty.
      intros t.
      intros Hlsem.
      intros Ht.
      destruct t as [ li lr ].
      inversion Hlsem; subst.
      exists ([], HRNat n).
      split.
      + simpl. apply PeanoNat.Nat.eqb_refl.
      + constructor.
    }
  - (* HBool *) simpl.
    intros ty.
    intros t.
    intros Hlsem.
    intros Ht.
    destruct t as [ li lr ].
    destruct b.
    + inversion Hlsem; subst.
      exists ([], HRBool true).
      split.
      * simpl. reflexivity. 
      * simpl. constructor.
    + inversion Hlsem; subst.
      exists ([], HRBool false).
      split.
      * simpl. reflexivity. 
      * simpl. constructor.
  - (* HPlus *)
    intros ty.
    intros t Hlsem Ht.
    simpl in Hlsem.
    inversion Hlsem; subst.
    inversion Ht; subst.
    specialize (IHhe1 TNat (ll1, LRNat n1) H1 H2).
    specialize (IHhe2 TNat (ll2, LRNat n2) H3 H5).
    destruct IHhe1 as [ s1 IHhe1 ].
    destruct IHhe2 as [ s2 IHhe2 ].
    destruct IHhe1 as [ IHhe1tilde IHhe1hsem ].
    destruct IHhe2 as [ IHhe2tilde IHhe2hsem ].
    destruct s1 as [ hl1 hr1 ].
    destruct s2 as [ hl2 hr2 ].
    apply type_soundness_nat' with (hl := hl1) (hr := hr1) in H2.
    Focus 2.
    apply IHhe1hsem.
    destruct H2 as [ n1' H2 ]. subst.
    apply type_soundness_nat' with (hl := hl2) (hr := hr2) in H5.
    Focus 2.
    apply IHhe2hsem.
    assert (Hn1 : n1' = n1).
    { inversion IHhe1tilde. apply PeanoNat.Nat.eqb_eq.
      eapply andb_proj2. apply H0. }
    destruct H5 as [ n2' H5 ]. subst.
    assert (Hn2 : n2' = n2).
    { inversion IHhe2tilde. apply PeanoNat.Nat.eqb_eq.
      eapply andb_proj2. apply H0. }
    subst.
    eexists (hl1 ++ hl2, HRNat (n1 + n2)).
    split.
    unfold tilde.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite tildeInputs_app.
    reflexivity.
    eapply tilde_tildeInputs.
    apply IHhe1tilde.
    eapply tilde_tildeInputs.
    apply IHhe2tilde.
    constructor.
    apply IHhe1hsem.
    apply IHhe2hsem.
  - (* HTimes *)
    intros ty.
    intros t Hlsem Ht.
    simpl in Hlsem.
    inversion Hlsem; subst.
    inversion Ht; subst.
    specialize (IHhe1 TNat (ll1, LRNat n1) H1 H2).
    specialize (IHhe2 TNat (ll2, LRNat n2) H3 H5).
    destruct IHhe1 as [ s1 IHhe1 ].
    destruct IHhe2 as [ s2 IHhe2 ].
    destruct IHhe1 as [ IHhe1tilde IHhe1hsem ].
    destruct IHhe2 as [ IHhe2tilde IHhe2hsem ].
    destruct s1 as [ hl1 hr1 ].
    destruct s2 as [ hl2 hr2 ].
    apply type_soundness_nat' with (hl := hl1) (hr := hr1) in H2.
    Focus 2.
    apply IHhe1hsem.
    destruct H2 as [ n1' H2 ]. subst.
    apply type_soundness_nat' with (hl := hl2) (hr := hr2) in H5.
    Focus 2.
    apply IHhe2hsem.
    assert (Hn1 : n1' = n1).
    { inversion IHhe1tilde. apply PeanoNat.Nat.eqb_eq.
      eapply andb_proj2. apply H0. }
    destruct H5 as [ n2' H5 ]. subst.
    assert (Hn2 : n2' = n2).
    { inversion IHhe2tilde. apply PeanoNat.Nat.eqb_eq.
      eapply andb_proj2. apply H0. }
    subst.
    eexists (hl1 ++ hl2, HRNat (n1 * n2)).
    split.
    unfold tilde.
    rewrite PeanoNat.Nat.eqb_refl.
    rewrite tildeInputs_app.
    reflexivity.
    eapply tilde_tildeInputs.
    apply IHhe1tilde.
    eapply tilde_tildeInputs.
    apply IHhe2tilde.
    constructor.
    apply IHhe1hsem.
    apply IHhe2hsem.
  - (* HIte *)
    intros ty.
    intros t Hlsem Ht.
    simpl in Hlsem.
    (*
| LSIteLeft : forall le1 le2 le3 le4 ll1 ll2 ll3 n1 n2 n3,
    lsem le1 (ll1, LRNat n1) ->
    lsem le2 (ll2, LRNat n2) ->
    le n1 n2 ->
    lsem le3 (ll3, LRNat n3) ->
    lsem (LIte le1 le2 le3 le4) (app ll1 (app ll2 ll3), LRNat n3)
| LSIteRight : forall le1 le2 le3 le4 ll1 ll2 ll4 n1 n2 n4,
    lsem le1 (ll1, LRNat n1) ->
    lsem le2 (ll2, LRNat n2) ->
    not (le n1 n2) ->
    lsem le4 (ll4, LRNat n4) ->
    lsem (LIte le1 le2 le3 le4) (app ll1 (app ll2 ll4), LRNat n4)
*)
    inversion Hlsem as [ | | | le1' le2' le3' le4' ll1 ll2 ll3 n1 n2 n3 Hle1 Hle2 Hle Hle3 | le1' le2' le3' le4' ll1 ll2 ll4 n1 n2 n4 Hle1 Hle2 Hle Hle4 | ]; subst.
    + (* true branch *)
      inversion Ht as [ | | | | he1' he2' he3' t' Ht1 Ht2 Ht3  | | | ]; subst.
      clear Ht.
      specialize (IHhe1 TBool (ll1, LRNat n1) Hle1 Ht1).
      specialize (IHhe3 ty (ll3, LRNat n3) Hle3 Ht3).
      destruct IHhe1 as [ s1 IHhe1 ].
      destruct IHhe3 as [ s3 IHhe3 ].
      destruct IHhe1 as [ IHhe1tilde IHhe1hsem ].
      destruct IHhe3 as [ IHhe3tilde IHhe3hsem ].
      destruct s1 as [ hl1 hr1 ].
      destruct s3 as [ hl3 hr3 ].
      inversion Hle2. subst.
      inversion Hle; subst.
      clear Hle.
      destruct ty.
      * (* ty = TNat *)
        exists (hl1 ++ [] ++ hl3, HRNat n3).
        split.
        ** apply ti_tr_tilde.
           *** apply tildeInputs_app.
               eapply tilde_tildeInputs.
               apply IHhe1tilde.
           *** apply tildeInputs_app.
               **** reflexivity.
               **** eapply tilde_tildeInputs.
                    apply IHhe3tilde.
                    unfold tildeResult. apply PeanoNat.Nat.eqb_refl.
        ** 
           apply HSIteRight.

           {
             destruct hr1.
             *** (* hr1 = HRBool b *)
               destruct b.
               **** (* b = true *)
                 apply tilde_tildeResult in IHhe1tilde.
                 unfold tildeResult in IHhe1tilde.
                 inversion IHhe1tilde.
               **** (* b = false *)
                 assumption.
             *** (* hr1 = HRNat n *)
               (* impossible *)
               assert (Hcontra : exists b : bool, HRNat n = HRBool b).
               eapply type_soundness_bool'.
               apply Ht1.
               apply IHhe1hsem.
               destruct Hcontra.
               inversion H.
             *** (* hr1 = HRerror *)
               (* impossible *)
               assert (Hcontra : exists b : bool, HRError = HRBool b).
               eapply type_soundness_bool'.
               apply Ht1.
               apply IHhe1hsem.
               destruct Hcontra.
               inversion H.
           }
           {
             simpl.
             destruct hr3.
             *** (* hr3 = HRBool b *)
               (* impossible *)
               assert (Hcontra : exists n' : nat, HRBool b = HRNat n').
               eapply type_soundness_nat'.
               apply Ht3.
               apply IHhe3hsem.
               destruct Hcontra.
               inversion H.
             *** (* hr3 = HRNat n *)
                 apply tilde_tildeResult in IHhe3tilde.
                 unfold tildeResult in IHhe3tilde.
                 apply PeanoNat.Nat.eqb_eq in IHhe3tilde.
                 subst.
                 assumption.
             *** (* hr3 = HRerror *)
               (* impossible *)
               assert (Hcontra : exists n' : nat, HRError = HRNat n').
               eapply type_soundness_nat'.
               apply Ht3.
               apply IHhe3hsem.
               destruct Hcontra.
               inversion H.
           }
        ** (* ty = TBool *)
          destruct hr3.
          {
            (* hr3 = HRBool b *)
            exists (hl1 ++ [] ++ hl3, HRBool b).
            split.
            {
              apply ti_tr_tilde.
              {
                apply tildeInputs_app.
                apply tilde_tildeInputs in IHhe1tilde.
                assumption.
                apply tildeInputs_app.
                reflexivity.
                apply tilde_tildeInputs in IHhe3tilde.
                assumption.
              }
              {
                apply tilde_tildeResult in IHhe3tilde.
                assumption.
              }
            }
            {
              apply HSIteRight.

              {
                destruct hr1.
                *** (* hr1 = HRBool b0 *)
                  destruct b0.
                  **** (* b = true *)
                    apply tilde_tildeResult in IHhe1tilde.
                    unfold tildeResult in IHhe1tilde.
                    inversion IHhe1tilde.
                  **** (* b = false *)
                    assumption.
                *** (* hr1 = HRNat n *)
                  (* impossible *)
                  assert (Hcontra : exists b : bool, HRNat n = HRBool b).
                  eapply type_soundness_bool'.
                  apply Ht1.
                  apply IHhe1hsem.
                  destruct Hcontra.
                  inversion H.
                *** (* hr1 = HRerror *)
                  (* impossible *)
                  assert (Hcontra : exists b : bool, HRError = HRBool b).
                  eapply type_soundness_bool'.
                  apply Ht1.
                  apply IHhe1hsem.
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
            (* hr3 = HRNat n *)
            (* impossible *)
            assert (Hcontra : exists b : bool, HRNat n = HRBool b).
            eapply type_soundness_bool'.
            apply Ht3.
            apply IHhe3hsem.
            destruct Hcontra.
            inversion H.
          }
          {
            (* hr3 = HRError *)
            (* impossible *)
            assert (Hcontra : exists b : bool, HRError = HRBool b).
            eapply type_soundness_bool'.
            apply Ht3.
            apply IHhe3hsem.
            destruct Hcontra.
            inversion H.
          }
    +  (* false branch *)
    + (* true branch *)
      inversion Ht as [ | | | | he1' he2' he3' t' Ht1 Ht2 Ht3  | | | ]; subst.
      clear Ht.
      specialize (IHhe1 TBool (ll1, LRNat n1) Hle1 Ht1).
      specialize (IHhe2 ty (ll4, LRNat n4) Hle4 Ht2).
      destruct IHhe1 as [ s1 IHhe1 ].
      destruct IHhe2 as [ s2 IHhe2 ].
      destruct IHhe1 as [ IHhe1tilde IHhe1hsem ].
      destruct IHhe2 as [ IHhe2tilde IHhe2hsem ].
      destruct s1 as [ hl1 hr1 ].
      destruct s2 as [ hl2 hr2 ].
      inversion Hle2. subst.
      destruct n1 as [ | n1' ].
      {
        exfalso. apply Hle. constructor.
      }
      clear Hle.
      destruct ty.
      * (* ty = TNat *)
        exists (hl1 ++ [] ++ hl2, HRNat n4).
        split.
        ** apply ti_tr_tilde.
           *** apply tildeInputs_app.
               eapply tilde_tildeInputs.
               apply IHhe1tilde.
           *** apply tildeInputs_app.
               **** reflexivity.
               **** eapply tilde_tildeInputs.
                    apply IHhe2tilde.
                    unfold tildeResult. apply PeanoNat.Nat.eqb_refl.
        ** 
           apply HSIteLeft.

           {
             destruct hr1.
             *** (* hr1 = HRBool b *)
               destruct b.
               **** (* b = true *)
                 assumption.
               **** (* b = false *)
                 apply tilde_tildeResult in IHhe1tilde.
                 unfold tildeResult in IHhe1tilde.
                 inversion IHhe1tilde.
             *** (* hr1 = HRNat n *)
               (* impossible *)
               assert (Hcontra : exists b : bool, HRNat n = HRBool b).
               eapply type_soundness_bool'.
               apply Ht1.
               apply IHhe1hsem.
               destruct Hcontra.
               inversion H.
             *** (* hr1 = HRerror *)
               (* impossible *)
               assert (Hcontra : exists b : bool, HRError = HRBool b).
               eapply type_soundness_bool'.
               apply Ht1.
               apply IHhe1hsem.
               destruct Hcontra.
               inversion H.
           }
           {
             simpl.
             destruct hr2.
             *** (* hr2 = HRBool b *)
               (* impossible *)
               assert (Hcontra : exists n' : nat, HRBool b = HRNat n').
               eapply type_soundness_nat'.
               apply Ht2.
               apply IHhe2hsem.
               destruct Hcontra.
               inversion H.
             *** (* hr2 = HRNat n *)
                 apply tilde_tildeResult in IHhe2tilde.
                 unfold tildeResult in IHhe2tilde.
                 apply PeanoNat.Nat.eqb_eq in IHhe2tilde.
                 subst.
                 assumption.
             *** (* hr2 = HRerror *)
               (* impossible *)
               assert (Hcontra : exists n' : nat, HRError = HRNat n').
               eapply type_soundness_nat'.
               apply Ht2.
               apply IHhe2hsem.
               destruct Hcontra.
               inversion H.
           }
        ** (* ty = TBool *)
          destruct hr2.
          {
            (* hr3 = HRBool b *)
            exists (hl1 ++ [] ++ hl2, HRBool b).
            split.
            {
              apply ti_tr_tilde.
              {
                apply tildeInputs_app.
                apply tilde_tildeInputs in IHhe1tilde.
                assumption.
                apply tildeInputs_app.
                reflexivity.
                apply tilde_tildeInputs in IHhe2tilde.
                assumption.
              }
              {
                apply tilde_tildeResult in IHhe2tilde.
                assumption.
              }
            }
            {
              apply HSIteLeft.

              {
                destruct hr1.
                *** (* hr1 = HRBool b0 *)
                  destruct b0.
                  **** (* b = true *)
                    assumption.
                  **** (* b = false *)
                    apply tilde_tildeResult in IHhe1tilde.
                    unfold tildeResult in IHhe1tilde.
                    inversion IHhe1tilde.
                *** (* hr1 = HRNat n *)
                  (* impossible *)
                  assert (Hcontra : exists b : bool, HRNat n = HRBool b).
                  eapply type_soundness_bool'.
                  apply Ht1.
                  apply IHhe1hsem.
                  destruct Hcontra.
                  inversion H.
                *** (* hr1 = HRerror *)
                  (* impossible *)
                  assert (Hcontra : exists b : bool, HRError = HRBool b).
                  eapply type_soundness_bool'.
                  apply Ht1.
                  apply IHhe1hsem.
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
            (* hr3 = HRNat n *)
            (* impossible *)
            assert (Hcontra : exists b : bool, HRNat n = HRBool b).
            eapply type_soundness_bool'.
            apply Ht2.
            apply IHhe2hsem.
            destruct Hcontra.
            inversion H.
          }
          {
            (* hr3 = HRError *)
            (* impossible *)
            assert (Hcontra : exists b : bool, HRError = HRBool b).
            eapply type_soundness_bool'.
            apply Ht2.
            apply IHhe2hsem.
            destruct Hcontra.
            inversion H.
          }
  - (* HLe *)
    {
      intros ty.
      intros t Hlsem Ht.
      simpl in Hlsem.
      inversion Hlsem; subst.
      {
        inversion Ht; subst.
        specialize (IHhe1 TNat (ll1, LRNat n1) H3 H1).
        specialize (IHhe2 TNat (ll2, LRNat n2) H5 H4).
        destruct IHhe1 as [ s1 IHhe1 ].
        destruct IHhe2 as [ s2 IHhe2 ].
        destruct IHhe1 as [ IHhe1tilde IHhe1hsem ].
        destruct IHhe2 as [ IHhe2tilde IHhe2hsem ].
        destruct s1 as [ hl1 hr1 ].
        destruct s2 as [ hl2 hr2 ].
        apply type_soundness_nat' with (hl := hl1) (hr := hr1) in H1.
        Focus 2.
        apply IHhe1hsem.
        destruct H1 as [ n1' H1 ]. subst.
        apply type_soundness_nat' with (hl := hl2) (hr := hr2) in H4.
        Focus 2.
        apply IHhe2hsem.
        assert (Hn1 : n1' = n1).
        { inversion IHhe1tilde. apply PeanoNat.Nat.eqb_eq.
          eapply andb_proj2. apply H0. }
        destruct H4 as [ n2' H4 ]. subst.
        assert (Hn2 : n2' = n2).
        { inversion IHhe2tilde. apply PeanoNat.Nat.eqb_eq.
          eapply andb_proj2. apply H0. }
        subst.
        eexists (hl1 ++ hl2, HRBool (Nat.leb n1 n2)).
        split.
        unfold tilde.
        inversion H7. subst.
        apply PeanoNat.Nat.leb_le in H6.
        rewrite H6.
        rewrite tildeInputs_app.
        reflexivity.
        apply tilde_tildeInputs in IHhe1tilde.
        assumption.
        apply tilde_tildeInputs in IHhe2tilde.
        rewrite app_nil_r.
        assumption.
        constructor.
        apply IHhe1hsem.
        apply IHhe2hsem.
      }
      {
        inversion Ht; subst.
        specialize (IHhe1 TNat (ll1, LRNat n1) H3 H1).
        specialize (IHhe2 TNat (ll2, LRNat n2) H5 H4).
        destruct IHhe1 as [ s1 IHhe1 ].
        destruct IHhe2 as [ s2 IHhe2 ].
        destruct IHhe1 as [ IHhe1tilde IHhe1hsem ].
        destruct IHhe2 as [ IHhe2tilde IHhe2hsem ].
        destruct s1 as [ hl1 hr1 ].
        destruct s2 as [ hl2 hr2 ].
        apply type_soundness_nat' with (hl := hl1) (hr := hr1) in H1.
        Focus 2.
        apply IHhe1hsem.
        destruct H1 as [ n1' H1 ]. subst.
        apply type_soundness_nat' with (hl := hl2) (hr := hr2) in H4.
        Focus 2.
        apply IHhe2hsem.
        assert (Hn1 : n1' = n1).
        { inversion IHhe1tilde. apply PeanoNat.Nat.eqb_eq.
          eapply andb_proj2. apply H0. }
        destruct H4 as [ n2' H4 ]. subst.
        assert (Hn2 : n2' = n2).
        { inversion IHhe2tilde. apply PeanoNat.Nat.eqb_eq.
          eapply andb_proj2. apply H0. }
        subst.
        eexists (hl1 ++ hl2, HRBool (Nat.leb n1 n2)).
        split.
        unfold tilde.
        inversion H7. subst.
        apply PeanoNat.Nat.leb_nle in H6.
        rewrite H6.
        rewrite tildeInputs_app.
        reflexivity.
        apply tilde_tildeInputs in IHhe1tilde.
        assumption.
        apply tilde_tildeInputs in IHhe2tilde.
        rewrite app_nil_r.
        assumption.
        constructor.
        apply IHhe1hsem.
        apply IHhe2hsem.
        }
    }
  - (* HInBool *)
    {
      intros ty t Hlsem Ht.
      inversion Ht; subst.
      simpl in Hlsem.
      destruct t as [ ll lr ].
      destruct lr.
      destruct ll as [ | hd tl ].
      {
        (* ll = []  -- impossible *)
        inversion Hlsem.
      }
      {
        (* ll = hd :: tl *)
        destruct tl.
        {
          simpl.
          destruct hd.
          inversion Hlsem.
          subst.
          destruct n.
          { (* n = 0 --> false *)
            exists ([HIBool false], HRBool false).
            split.
            reflexivity.
            constructor.
          }
          {
            (* n > 0 --> true *)
            exists ([HIBool true], HRBool true).
            split.
            reflexivity.
            constructor.
          }
        }
        {
          (* tl = _ :: _  -- impossible *)
          inversion Hlsem.
        }
      }
    }
  - (* HInNat *)
    intros ty t Hlsem Ht.
    inversion Ht; subst.
    simpl in Hlsem.
    destruct t as [ ll lr ].
    destruct lr.
    destruct ll as [ | hd tl ].
    {
      (* ll = []  -- impossible *)
      inversion Hlsem.
    }
    {
      (* ll = hd :: tl *)
      destruct tl.
      {
        simpl.
        destruct hd.
        inversion Hlsem.
        subst.
        exists ([HINat n], HRNat n).
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
        inversion Hlsem.
      }
    }
Qed.
