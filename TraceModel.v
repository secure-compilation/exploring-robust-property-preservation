Require Import Events. 
Require Import ClassicalExtras.
Require Import Setoid.
Require Import List.


(** In this file, we define the trace model that will be used
    in the rest of the development, and prove several results
    about these traces. *)

CoInductive stream {A : Type} :=
   scons (e : A) (s : stream) : stream. 

Fixpoint list_stream_prefix {A : Type} (l : list A) (s : stream) :=
  match l, s with
  | nil, _ => True
  | cons a1 l1, scons a2 s2 => (a1 = a2) /\ (list_stream_prefix l1 s2)
  end.  

Fixpoint list_list_prefix {A : Type} (l1 l2 : list A) :=
  match l1, l2 with
  | nil, _ => True
  | cons a1 l1, cons a2 l2 => (a1 = a2) /\ list_list_prefix l1 l2
  | _, _ => False
  end.

Lemma list_list_prefix_ref {A : Type} (l : list A) : list_list_prefix l l. 
Proof. now induction l. Qed. 

Lemma list_list_prefix_asym {A : Type} : forall (l1 l2 : list A),
    list_list_prefix l1 l2 -> list_list_prefix l2 l1 -> l1 = l2. 
Proof.
  induction l1, l2; try now auto.
  simpl. intros [afoo Hpref] [afoo' Hpref']; subst; now rewrite (IHl1 l2). 
Qed.

Lemma list_list_prefix_trans {A : Type} : forall l1 l2 l3 : list A,
  list_list_prefix l1 l2 -> list_list_prefix l2 l3 -> list_list_prefix l1 l3.
Proof.
  induction l1; try now auto.  
  intros [] [] H1 H2; inversion H1; inversion H2; subst.
  simpl. firstorder.
Qed.

Lemma list_stream_prefix_trans {A : Type} : forall (l1 l2 : list A) (s : stream),
    list_list_prefix l1 l2 -> list_stream_prefix l2 s ->
    list_stream_prefix l1 s.
Proof.
  induction l1; auto.
  + intros [] [] Hpref1 Hpref2; inversion Hpref1; inversion Hpref2; subst. 
    simpl. split; auto; now apply (IHl1 l s).
Qed.  

(** A trace represents either a stopped execution, a silently diverging
    execution or an infinite execution. *)
Variant trace : Set :=
| tstop (l : list event) (e : endstate) : trace
| tsilent (l : list event) : trace
| tstream (s : @stream event) : trace.

(** A finite prefix is a list of events, that can be continued (ftbd)
    or not (fstop). *)
Variant finpref : Set :=
| fstop (l : list event) (es : endstate) : finpref
| ftbd  (l : list event) : finpref. 

Tactic Notation "destruct" "finpref" ident(m) "as" ident(e) ident(f) ident(p) :=
  destruct m as [ [| e p] f
                | [| e p]
                ].

Tactic Notation "induction" "finpref" ident(m) "as" ident(e) ident(f) ident(p) ident(Hp) :=
  destruct m as [m f | m]; induction m as [|e p Hp].

(** Prefix relation between finite prefixes and traces *)
(** *prefix relation *)

Definition prefix (m : finpref) (t : trace) : Prop :=
  match m, t with
  | fstop lm em, tstop lt et => em = et /\ lm = lt
  | ftbd  lm   , tstop lt et => list_list_prefix lm lt
  | ftbd  lm   , tsilent lt  => list_list_prefix lm lt
  | ftbd  lm   , tstream s   => list_stream_prefix lm s
  | _, _ => False
  end. 

(** Some traces/executions are finite, some are not. *)

Definition fin (t : trace) : Prop :=
  match t with
  | tstop l f => True
  | _ => False
  end. 
  
Definition inf (t : trace) : Prop := ~(fin t).
Hint Unfold inf.

(* A trace is either finite or not *)
Lemma fin_or_inf : forall t, fin t \/ inf t.
Proof.
 intros t. now apply classic. 
Qed.

(* A finite prefix has at least two possible continuations
   as we have at least two distinct events
   CH: this doesn't seem to use different_events though!
*)
Lemma many_continuations :
  forall m ta, inf ta -> exists t', prefix m t' /\ t' <> ta.
Proof.
  intros [] t Ht.
  + destruct t; try now exists (tstop l es).  
    unfold inf in Ht. exfalso. now apply Ht.   
  + exists (tstop l an_endstate); split; try now auto. 
    simpl. now apply list_list_prefix_ref.
    intros H. rewrite <- H in Ht. unfold inf in Ht.
    now apply Ht. 
Qed.


CoFixpoint constant_stream (e : event) : stream := scons e (constant_stream e).

Definition embedding (es : endstate) (m : finpref) : trace :=
  match m with
  | fstop l f => tstop l f
  | ftbd l => tstop l es
  end.

Lemma embed_pref (es : endstate) : forall m, prefix m (embedding es m).
Proof. destruct m; simpl; auto; apply list_list_prefix_ref. Qed.

Definition fpr (m1 m2 : finpref) : Prop :=
  match m1, m2 with
  | ftbd l1, ftbd l2 => list_list_prefix l1 l2
  | ftbd l1, fstop l2 e2 => list_list_prefix l1 l2
  | fstop l1 e1, fstop l2 e2 => e1 = e2 /\ l1 = l2
  | _, _ => False
  end. 

Lemma fpr_pref_pref : forall m1 m2 t,
    fpr m1 m2 -> prefix m2 t -> prefix m1 t.
Proof.
  intros [] [] [] Hfpr Hpref; try now auto; simpl in *; (try firstorder; now subst).  
  + simpl in *. now apply (list_list_prefix_trans l l0 l1).
  + simpl in *. now apply (list_list_prefix_trans l l0 l1).
  + simpl in *. now apply (list_stream_prefix_trans l l0 s). 
Qed.

Lemma list_list_same_ext : forall (l1 l2 l : list event),
    list_list_prefix l1 l -> list_list_prefix l2 l ->
    (list_list_prefix l1 l2 \/ list_list_prefix l2 l1). 
Proof.
  induction l1.
  + now left.
  + intros [] [] Hpref1 Hpref2; try now right. 
    ++ inversion Hpref1; inversion Hpref2; subst; simpl.
       destruct (IHl1 l l0); now auto.
Qed.      

Lemma list_stream_same_ext : forall (l1 l2 : list event) (s : stream),
    list_stream_prefix l1 s -> list_stream_prefix l2 s ->
    (list_list_prefix l1 l2 \/ list_list_prefix l2 l1).
Proof.
  induction l1.
  + now left.
  + intros [] [] Hpref1 Hpref2.
    ++ now right.
    ++ inversion Hpref1; inversion Hpref2; subst; simpl.
       destruct (IHl1 l s); now auto.
Qed.                      
  
Lemma same_ext : forall m1 m2 t,
    prefix m1 t -> prefix m2 t ->
    fpr m1 m2 \/ fpr m2 m1.
Proof.
  intros m1 m2 [] Hpref1 Hpref2.
  + destruct m1, m2; simpl in *; try now auto. 
    ++ inversion Hpref1; inversion Hpref2; subst; now auto.
    ++ inversion Hpref1; subst; now right.
    ++ inversion Hpref2; subst; now left.
    ++ now apply (list_list_same_ext l0 l1 l).
  + destruct m1, m2; simpl in *; try now auto. 
    ++ now apply (list_list_same_ext l0 l1 l).
  +  destruct m1, m2; simpl in *; try now auto. 
    ++ now apply (list_stream_same_ext l l0 s).
Qed.   

Lemma same_fpr : forall m1 m2 m,
    fpr m1 m -> fpr m2 m ->
    (fpr m1 m2 \/ fpr m2 m1).
Proof.
  intros [] [] [] Hpref1 Hpref2; simpl in Hpref1, Hpref2; try now auto. 
  + inversion Hpref1; inversion Hpref2; subst. now auto.
  + inversion Hpref1; subst. now right.
  + inversion Hpref2; subst. now left.
  + simpl. now apply (list_list_same_ext l l0 l1).
  + simpl. now apply (list_list_same_ext l l0 l1).
Qed. 
  

Fixpoint snoc {A : Type} (l : list A) (x : A) : list A :=
  match l with
  | nil => cons x nil
  | cons x' l' => cons x' (snoc l' x)
  end.

Lemma list_prefix_snoc_list_prefix {A : Type} : forall (l1 l2 : list A) (a : A),
    list_list_prefix l1 l2 ->
    list_list_prefix l1 (snoc l2 a).
Proof.
  induction l1.
  + auto.
  + destruct l2. contradiction.
    intros a1 H1. inversion H1; subst. 
    simpl. split; auto; now apply (IHl1 l2 a0). 
Qed.

Lemma list_snoc_diff {A : Type} : forall (l : list A) (a b : A),
        list_list_prefix (snoc l a) (snoc l b) ->  a = b.
Proof.
  induction l; intros a1 b1 H; simpl in H; inversion H; auto.     
Qed.

Definition diverges (t : trace) : Prop :=
  match t with
  | tsilent l => True
  | _ => False
  end. 


CoInductive stream_eq {A : Type} : stream -> stream -> Prop :=
  | econs : forall (a : A) s1 s2, stream_eq s1 s2 -> stream_eq (scons a s1) (scons a s2). 

Lemma stream_eq_sym {A : Type} : forall (s1 s2 : stream), @stream_eq A s1 s2 -> @stream_eq A s2 s1.
Proof.
  cofix CH.
  intros s1 s2 Heq.
  inversion Heq; subst; constructor.
  now apply CH.
Qed.

Definition stream_hd {A : Type} (s : @stream A) : A :=
  match s with
  | scons a _ => a
  end. 

Definition stream_tl {A : Type} (s : @stream A): @stream A :=
  match s with
  | scons _ s' => s'
  end.

Lemma stream_eq_hd_tl {A : Type} : forall (s1 s2 : @stream A),
    stream_hd s1 = stream_hd s2 ->
    stream_eq (stream_tl s1) (stream_tl s2) ->
    stream_eq s1 s2.
Proof.
  intros [] [] H H0. simpl in *.
  subst. now constructor. 
Qed.


Lemma stream_eq_finetely_refutable {A : Type} : forall s1 s2,
    ~ (stream_eq s1 s2) <-> (exists l (a1 a2 : A),
                              list_stream_prefix (snoc l a1) s1 /\
                              list_stream_prefix (snoc l a2) s2 /\
                          a1 <> a2). 
Proof.
  intros s1 s2. split.
  + rewrite contra. intros H.
    rewrite <- dne. rewrite not_ex_forall_not in H.
    generalize dependent s2.
    generalize dependent s1.
    cofix Heq.
    intros [] [] H.
    assert (e = e0).
    { specialize (H nil). rewrite not_ex_forall_not in H.
       specialize (H e). rewrite not_ex_forall_not in H.
       specialize (H e0). rewrite de_morgan1 in H.
       destruct H as [H | H].  
       * exfalso. now apply H.  
       * rewrite de_morgan1 in H. destruct H as [H | H].
         ** exfalso. now apply H.
         ** now rewrite <- dne in H. }
    subst. constructor. 
    apply Heq.
    intros l [a1 [a2 [Hpref1 [Hpref2 Hdiff]]]].
    specialize (H (cons e0 l)). apply H. 
    exists a1, a2. repeat split; try now auto.
  + intros [l [a1 [a2 [Hpref1 [Hpref2 Hdiff]]]]] Heq.
    generalize dependent s1. generalize dependent s2.
    induction l.
    ++ intros [] Hpref2 [] Hpref1 Heq; simpl in *. inversion Hpref1; inversion Hpref2; subst.
       apply Hdiff. now inversion Heq.
    ++ intros [] Hpref2 [] Hpref1 Heq; simpl in *. inversion Hpref1; inversion Hpref2; subst.
       apply (IHl s H2 s0 H0). now inversion Heq.
Qed.


(* Various lemmas about snoc, and fpr *)

Lemma destruct_pref {A : Type} : forall (l : list A),
    l = nil \/ exists (a : A) (l' : list A),  l = snoc l' a.
Proof.
  induction l. 
  - now left.
  - right. destruct IHl.
    + subst. now exists a, nil.
    + destruct H as [e [m' H]]. subst.
      now exists e, (cons a m').
Qed.

Lemma snoc_length {A : Type} : forall (l' : list A) (a : A) (n : nat),
    Datatypes.length (snoc l' a) = S n -> Datatypes.length l' = n.
Proof.
  induction l'.
  - intros. simpl in H. inversion H. reflexivity.
  - intros e n Hlen. simpl in *. inversion Hlen.
    destruct n as [| m].
    + destruct l'; now auto.
    + rewrite H0. now rewrite (IHl' e m).  
Qed.

Theorem list_ind_snoc {A : Type} :
  forall (P : list A -> Prop),
    P nil ->
    (forall (l : list A) (a : A), P l -> P (snoc l a)) ->
    forall l, P l.
Proof.
  intros P Hnil Hind.
  assert (H: forall (n : nat) (l : list A), Datatypes.length l = n -> P l).
  { induction n.
    - intros l Hlen; try now auto.
      destruct l; try now auto.
    - intros l Hlen.
      destruct (destruct_pref l); try now auto.
      subst; assumption.
      destruct H as [e' [p' H']].
      subst; apply snoc_length in Hlen. specialize (IHn p' Hlen).
      now specialize (Hind p' e' IHn). }
  intros p. now apply (H (Datatypes.length p) p).
Qed.

Fixpoint app_list_stream (l : list event) (s : stream) : stream :=
  match l with
  | nil => s
  | cons e l' => scons e (app_list_stream l' s)
  end.

Definition tapp (m : finpref) (t : trace) : trace :=
  match m, t with
  | fstop l f, _ => tstop l f (* justification: *)
(*                            we can't really add anything after a stopped trace. *)
  | ftbd l, tstop l' f => tstop (l ++ l') f
  | ftbd l, tsilent l' => tsilent (l ++ l')
  | ftbd l, tstream s => tstream (app_list_stream l s)
  end.

Lemma tapp_pref : forall (m : finpref) (t : trace),
    prefix m (tapp m t).
Proof.
  induction finpref m as e f p IHp; intros; try now auto.
  - simpl in *. now destruct t.
  - destruct t; split; simpl in *; try now auto.
    specialize (IHp (tstop l e0)); assumption.
    specialize (IHp (tsilent l)); assumption.
    specialize (IHp (tstream s)); assumption.
Qed.

Lemma snoc_nil {A : Type} : forall (l : list A) (a : A), snoc l a <> nil.
Proof.
  induction l; intros a0; intros Hf; inversion Hf.
Qed.

Lemma nil_bottom {A : Type} : forall (l : list A), list_list_prefix l nil -> l = nil. 
Proof. now induction l. Qed.  
  
Lemma list_proper_or_equal {A : Type}: forall (l1 l2 : list A),
    list_list_prefix l1 l2 -> l1 = l2 \/ exists a, list_list_prefix (snoc l1 a) l2.
Proof.
  induction l1.
  + intros []; try now left.
    intros H. right. now exists a.
  + intros [] Hpref; inversion Hpref; subst.
    simpl. destruct (IHl1 l) as [K | [a K]]; auto;
             [left; now rewrite K | right; now exists a].
Qed.


Lemma list_pref_snoc_pref {A : Type} : forall (l1 l2 : list A) (a1 a2 : A),
    list_list_prefix (snoc l1 a1) (snoc l2 a2) ->
    list_list_prefix l1 l2. 
Proof.
  induction l1; try now auto.
  intros [] a1 a2 Hpref; inversion Hpref; subst.
  + apply nil_bottom in H0. exfalso. now apply snoc_nil in H0. 
  + simpl. split; auto. now apply (IHl1 l a1 a2).
Qed.    

Lemma snoc_longer {A : Type} : forall (l : list A) (a : A),
    list_list_prefix l (snoc l a).
Proof. now induction l. Qed. 

Lemma snoc_strictly_longer {A : Type} : forall (l : list A) (a : A),
    ~ list_list_prefix (snoc l a) l.
Proof.
  induction l; try now auto.
  intros a0. simpl. intros [afoo H]; now apply (IHl a0).   
Qed.

Lemma list_snoc_pointwise: forall (l p : list event) i1 i2 a1 a2,
                          i1 <> i2 ->
                          list_list_prefix (snoc l i1) (snoc p a1) ->
                          list_list_prefix (snoc l i2) (snoc p a2) ->
                          (i1 = a1 /\ i2 = a2).
Proof.
  induction l; intros p i1 i2 a1 a2 diff_i l1_pref l2_pref.
  + destruct p; inversion l1_pref; inversion l2_pref; auto.
    subst. exfalso. now apply diff_i.
  + destruct p; simpl in l1_pref, l2_pref.
    ++ destruct l1_pref as [aa1 contra].
       now destruct l.
    ++ destruct l1_pref as [ae l1_pref]. destruct l2_pref as [foo l2_pref].
       now apply (IHl p i1 i2 a1 a2).
Qed.

Lemma snocs_aux_lemma {A : Type }: forall (l p : list A) (i1 i2 a : A),
    i1 <> i2 -> list_list_prefix (snoc l i1) (snoc p a) -> list_list_prefix (snoc l i2) p -> False.
Proof.
  induction l; intros [] i1 i2 ev Hdiff Hpref1 Hpref2;
    inversion Hpref1; inversion Hpref2; subst.
  + now apply Hdiff.
  + now apply (IHl l0 i1 i2 ev).
Qed.
