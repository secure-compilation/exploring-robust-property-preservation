Require Import Events.
Require Import ClassicalExtras.
Require Import TraceModel.
Require Import Properties.

Record Topology {X : Set} :=
  {
    open : (X -> Prop) -> Prop;
    empty : open (fun x : X => False);
    full  : open (fun x : X => True);

    arbitrary_union :
      forall (F : (X -> Prop) -> Prop),
        (forall f, F f -> open f) ->
         open (fun x : X => exists f, F f /\ f x);

    finite_intersection :
      forall A1 A2, open A1 -> open A2 ->
       open (fun x : X => A1 x /\ A2 x)                        
  }.

Definition closed (X : Set) (τ : @Topology X) :
                  (X -> Prop) -> Prop :=
  (fun C => (open τ) (fun x => (~ C x))).

Definition dense (X : Set) (τ : @Topology X) :
                 (X -> Prop) -> Prop :=
  (fun D => forall A, (open τ) A ->
              (exists a, A a) ->
              (exists d, A d /\ D d)).

