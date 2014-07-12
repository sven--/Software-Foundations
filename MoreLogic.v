(** * More Logic *)

Require Export "Prop".

(* ############################################################ *)
(** * Existential Quantification *)

(** Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

*)


(** *** *)
(** Coq's [Notation] facility can be used to introduce more
    familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** *** *)
(** We can use the usual set of tactics for
    manipulating existentials.  For example, to prove an
    existential, we can [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note that we have to explicitly give the witness. *)

(** *** *)
(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity.  Qed.

(** *** *)
(** Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).  
  apply Hm.  Qed. 


(** Here is another example of how to work with existentials. *)
Lemma exists_example_3 : 
  exists (n:nat), even n /\ beautiful n.
Proof.
(* WORKED IN CLASS *)
  exists 8.
  split.
  unfold even. simpl. reflexivity.
  apply b_sum with (n:=3) (m:=5).
  apply b_3. apply b_5.
Qed.

(** **** Exercise: 1 star, optional (english_exists) *)
(** In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean? *)

(* there exists some natural nuber s.t. beautiful (S n). holds. *)

(*
*)
(** **** Exercise: 1 star (dist_not_exists) *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not. intros. inversion H0.
  apply H1 in H. inversion H.
Qed.

(** **** Exercise: 3 stars, optional (not_exists_dist) *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.
  unfold not.
  intros.
  (* assert(G : forall x, P x \/ ((P x) -> False)).
  intros. apply (H (P x0)). *)
  assert(Gx : P x \/ (P x -> False)).
  apply H.
  inversion Gx. apply H1.
  apply ex_falso_quodlibet.
  apply H0.
  exists x.
  apply H1.
Qed.

(** **** Exercise: 2 stars (dist_exists_or) *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  unfold iff.
  split.
  intros.
  inversion H.
  inversion H0.
  left. exists witness. apply H1.
  right. exists witness. apply H1.
  
  intros.
  inversion H.
  inversion H0. exists witness. left. apply H1.
  inversion H0. exists witness. right. apply H1.
Qed.


(* ###################################################### *)
(** * Evidence-carrying booleans. *)

(** So far we've seen two different forms of equality predicates:
[eq], which produces a [Prop], and
the type-specific forms, like [beq_nat], that produce [boolean]
values.  The former are more convenient to reason about, but
we've relied on the latter to let us use equality tests 
in _computations_.  While it is straightforward to write lemmas
(e.g. [beq_nat_true] and [beq_nat_false]) that connect the two forms,
using these lemmas quickly gets tedious. 
*)

(** *** *)
(** 
It turns out that we can get the benefits of both forms at once 
by using a construct called [sumbool]. *)

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.

(** Think of [sumbool] as being like the [boolean] type, but instead
of its values being just [true] and [false], they carry _evidence_
of truth or falsity. This means that when we [destruct] them, we
are left with the relevant evidence as a hypothesis -- just as with [or].
(In fact, the definition of [sumbool] is almost the same as for [or].
The only difference is that values of [sumbool] are declared to be in
[Set] rather than in [Prop]; this is a technical distinction 
that allows us to compute with them.) *) 

(** *** *)

(** Here's how we can define a [sumbool] for equality on [nat]s *)

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
(**
  intros n.
  induction n as [|n'].
  intros. destruct m as [|m']. left. reflexivity. right. unfold not.
  intros. inversion H.
  intros. destruct m as [|m']. right. unfold not. intros. inversion H.
  assert (G : {n' = m'} + {n' <> m'}).
  apply IHn'.
  inversion G.
  left. rewrite H. reflexivity.
  right. unfold not. intros. unfold not in H. apply H. inversion H0. reflexivity.
Qed.
**)
  (* WORKED IN CLASS *)
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined.

  
(** Read as a theorem, this says that equality on [nat]s is decidable:
that is, given two [nat] values, we can always produce either 
evidence that they are equal or evidence that they are not.
Read computationally, [eq_nat_dec] takes two [nat] values and returns
a [sumbool] constructed with [left] if they are equal and [right] 
if they are not; this result can be tested with a [match] or, better,
with an [if-then-else], just like a regular [boolean]. 
(Notice that we ended this proof with [Defined] rather than [Qed]. 
The only difference this makes is that the proof becomes _transparent_,
meaning that its definition is available when Coq tries to do reductions,
which is important for the computational interpretation.)
*) 

(** *** *)
(** 
Here's a simple example illustrating the advantages of the [sumbool] form. *)

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

(**
More generally, for an inductive type with constructors C1 and C2, we have the following equivalence


if term [dep_ret_type] then term1 else term2 ≡
match term [dep_ret_type] with
| C1 _ … _ => term1
| C2 _ … _ => term2
end

Here is an example.

TWO CONSTRUCTOR, similar logic with left / right.
**)

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2).   (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2". 
    reflexivity.  Qed.

(** Compare this to the more laborious proof (in MoreCoq.v) for the 
   version of [override] defined using [beq_nat], where we had to
   use the auxiliary lemma [beq_nat_true] to convert a fact about booleans
   to a Prop. *)


(** **** Exercise: 1 star (override_shadow') *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros.
  unfold override'.
  destruct (eq_nat_dec k1 k2) as [true|false].
  reflexivity.
  reflexivity.
Qed.




(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  all_empty : (all P) []
  | all_cons : forall (l : list X) (v : X), all P l -> P v -> all P (v :: l).
(*
    fun (l : list X) => ex X P.

  fun (k':nat) => if eq_nat_dec k k' then x else f k'.
  all_intro : (all X P).

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.
(*
    forall (witness:X), P witness -> ex X P.
*)

*)

Fact all_1 : all ev [2;4;6].
Proof. apply all_cons. apply all_cons. apply all_cons. apply all_empty. apply ev_SS. apply ev_SS. apply ev_SS. apply ev_0. apply ev_SS. apply ev_SS. apply ev_0. apply ev_SS. apply ev_0. Qed.

Fact all_2 : ~(all ev [2;3;6]).
Proof. unfold not. intros. inversion H. inversion H2. inversion H7. inversion H9. Qed.



Fixpoint is_elem {X : Type} (v : X) (l : list X) : Prop :=
  match l with
  | [] => False
  | h :: t => h = v \/ is_elem v t 
  end.

Fact is_elem_1 : is_elem 2 [1;2;3].
Proof. simpl. right. left. reflexivity. Qed.

Fact is_elem_2 : ~(is_elem 4 [1;2;3]).
Proof. simpl. unfold not. intros H. inversion H. inversion H0. inversion H0. inversion H1. inversion H1. inversion H2. inversion H2. Qed.


Theorem all_not_exists : forall {X : Type} (P : X -> Prop) (l : list X),
  all P l -> ~(exists x, (is_elem x l) /\ ~(P x)).
Proof.
  intros.
  unfold not.
  induction H.
  intros. inversion H. inversion H0. inversion H1.
  intros. apply IHall. inversion H1. inversion H2. inversion H3. rewrite <- H5 in H4. apply H4 in H0. inversion H0.
  exists witness. split. apply H5. apply H4.
Qed.

Corollary exists_not_all : forall {X : Type} (P : X -> Prop) (l : list X),
  ~~(exists x, (is_elem x l) /\ ~(P x)) -> ~(all P l).
Proof.
  intros X P l.
  apply contrapositive. apply all_not_exists.
Qed.

Theorem not_exists_all : forall {X : Type} (P : X -> Prop) (l : list X),
  ~(exists x, (is_elem x l) /\ ~(P x)) -> all P l.
Proof.
  unfold not.
  intros.
  
  induction l as [|l'].
  intros. apply all_empty.

  
  apply all_cons.
  apply IHl.
  intros.
  apply H.
  inversion H0.
  inversion H1.
  exists witness.
  split.
  simpl.
  right.
  apply H2.
  apply H3.
Abort.


  
  

  


(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)
Print fold.

Theorem forallb_fold : forall {X : Type} (test : X -> bool) (l : list X),
  (forallb test l) =
  (fold (fun x ans => (andb (test x) ans)) l true).
Proof.
  induction l as [|h t].
  reflexivity.
  simpl. rewrite IHt. reflexivity.
Qed.

  
Theorem forallb_false : forall {X : Type} (test : X -> bool) (l : list X),
  (forallb test l) = false -> (exists x, (is_elem x l) /\ (test x) = false).
Proof.
  induction l as [|h t].
  intros. inversion H.
  intros.
  inversion H.
  destruct (test h) as [t|f] eqn:e.
  simpl in H1. rewrite H1. simpl.
  apply IHt in H1. inversion H1.
  exists witness. inversion H0. split. right. apply H2. apply H3.

  exists h. split. simpl. left. reflexivity.
  simpl. apply e.
Qed.


Theorem forallb_true : forall {X : Type} (test : X -> bool) (l : list X),
  (forallb test l) = true -> all (fun x => test x = true) l.
Proof.
  induction l as [|h t].
  intros.
  apply all_empty.
  intros.
  apply all_cons.
  apply IHt.
  simpl in H.
  apply andb_true_elim2 in H.
  apply H.
  simpl in H.
  apply andb_true_elim1 in H.
  apply H.
Qed.
  
(*
Theorem forallb_true : forall {X : Type} (test : X -> bool) (l : list X),
  (forallb test l) = true -> ~(exists x, (is_elem x l) /\ (test x) = false).
Proof.
Qed.
*)
  
  

(** **** Exercise: 4 stars, advanced (filter_challenge) *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
    [1,4,6,2,3]
    is an in-order merge of
    [1,6,2]
    and
    [4,3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

(*
Definition in_order_merge {X : Type} (l1 l2 : list X) : list X :=
  if (beq_nat 0 (length l1)) then l2 else l1.

Fixpoint in_order_merge {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | h :: t => [h] ++ l2 ++ l1
  end.
*)

(*
Inductive is_in_order_merge {X : Type} (l1 l2 : list X) : list X :=
  | default : (is_in_order_merge l1 l2)
  .
*)
Inductive iom {X : Type} : list X -> list X -> list X -> Prop :=
  iom_empty : iom [] [] []
  | iom_left_cons : forall (l l1 l2 : list X) (v : X), 
                (iom l l1 l2) -> (iom (v :: l) (v :: l1) l2)
  | right_cons : forall (l l1 l2 : list X) (v : X),
                iom l l1 l2 -> iom (v :: l) l1 (v :: l2).

Lemma negb_refl : forall (b1 b2 : bool),
                    b1 = b2 -> negb(b1) = negb(b2).
Proof.
  intros. destruct b1. rewrite H. reflexivity. rewrite H. reflexivity.
Qed.

Theorem iom_spec {X : Type} (P : X -> bool) (l l1 l2 : list X) :
  forallb P l1 = true ->
  forallb (fun x => negb(P x)) l2 = true ->
  iom l l1 l2 ->
  filter P l = l1.
Proof.
  intros.
  generalize dependent H.
  generalize dependent H0.
  induction H1.
  intros. reflexivity.
  intros. simpl. simpl in H. apply andb_prop in H. inversion H.
  rewrite H2. rewrite IHiom. reflexivity. apply H0. apply H3.

  simpl. intros. apply andb_prop in H0. inversion H0. intros.
  apply negb_refl in H2. rewrite negb_involutive in H2. simpl in H2. rewrite H2. apply IHiom. apply H3. apply H.
(*  
  induction l as [|h t].
  simpl. intros. inversion H1. reflexivity.
  simpl. intros.
  destruct (P h) as [t|f] eqn:e.
  inversion H1.
*)
Qed.

(*  
Inductive iom {X : Type} (l1 l2 : list X) : list X -> Prop :=
  left_cons : forall (l : list X),
                match l with
                | [] => is_in_order_merge [] l2 l
                | h :: t => is_in_order_merge l1 [] l
                end
            .
*)

(*  
Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  all_empty : (all P) []
  | all_cons : forall (l : list X) (v : X), all P l -> P v -> all P (v :: l).

*)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2) *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

Inductive subseq {X : Type} : list X -> list X -> Prop :=
    sub_0 : forall l : list X, subseq [] l
  | sub_add_both : forall (l1 l2 : list X) (v : X),
                   subseq l1 l2 -> subseq (v :: l1) (v :: l2)
  | sub_add_one : forall (l1 l2 : list X) (v : X),
                  subseq l1 l2 -> subseq l1 (v :: l2).

Theorem filter_spec {X : Type} : forall (l s : list X) (P : X -> bool),
  subseq s l ->
  forallb P s = true ->
(*  (length s) <= (length (filter P l)). *)
  subseq s (filter P l).
Proof.
  intros. induction H.
  apply sub_0.
  inversion H0. apply andb_prop in H2. inversion H2.
  simpl. rewrite H1. apply sub_add_both.
  apply IHsubseq. apply H3.
  simpl. destruct (P v). apply sub_add_one. apply IHsubseq. apply H0.
  apply IHsubseq. apply H0.
Qed.

Fact subseq_length {X : Type} : forall (l s : list X),
  subseq s l ->
  length s <= length l.
Proof.
  intros. induction H. apply O_le_n.
  simpl. apply n_le_m__Sn_le_Sm. apply IHsubseq.
  simpl. apply le_S. apply IHsubseq.
Qed.

Corollary filter_spec_ {X : Type} : forall (l s : list X) (P : X -> bool),
  subseq s l ->
  forallb P s = true ->
  (length s) <= (length (filter P l)).
Proof.
  intros.
  assert(G : subseq s (filter P l)).
  apply filter_spec. apply H. apply H0.
  apply subseq_length in G. apply G.
Qed.
(*
********* proving it directily with length was quite hard...
harder statement -> more information on inductive hypotheis!!! **********
  intros. generalize dependent l.
  induction l as [|h t].
  simpl. intros. inversion H. reflexivity.
  simpl. intros. destruct (P h) eqn:e.
  simpl.
  inversion H.

  
  destruct s as [|sh st]. apply O_le_n.

  destruct t as [|m t]. simpl. inversion H. apply O_le_n.
  simpl. inversion H3. reflexivity. inversion H3. simpl. apply O_le_n.
  simpl.
  
  induction l as [|h t].
  simpl. intros. inversion H. reflexivity.

  intros.
  simpl.
  inversion H. apply O_le_n.
  simpl. apply n_le_m__Sn_le_Sm. apply (IHt l1 P). apply H3. 

  
  induction l as [|h t].
  simpl. intros. apply H.
  simpl. intros.
  destruct (P h) as [t|f] eqn : e.
  destruct s as [|h' t'] eqn : e2.
  apply sub_0.

*)
  

(** **** Exercise: 4 stars, advanced (no_repeats) *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_cons {X : Type} : forall (l : list X) (x v : X),
  appears_in x l -> appears_in x (v :: l).
Proof.
  induction l as [|h t].
  simpl. intros. inversion H.
  simpl. intros. apply ai_later. apply H.
Qed.

Lemma appears_snoc {X : Type} : forall (l : list X) (x v : X),
  appears_in x l -> appears_in x (snoc l v).
Proof.
  induction l as [|h t].
  simpl. intros. inversion H.
  simpl. intros. inversion H. apply ai_here.
  apply ai_later. apply IHt. apply H1.
Qed.

Lemma appears_app_after {X : Type} : forall (l1 l2: list X) (x : X) ,
(* Lemma appears_app_after {X : Type} (l1 l2: list X) (x : X) : *)
  appears_in x l1 -> appears_in x (l1 ++ l2).
Proof.
  induction l1 as [|h t].
  simpl. intros. inversion H.
  simpl. intros. inversion H. apply ai_here. apply ai_later. apply IHt. apply H1.
Qed.

Lemma appears_rearrange_snoc {X : Type} : forall (l : list X) (x v : X),
  appears_in x (snoc l v) ->
  appears_in x (cons v l).
Proof.
  induction l as [|h t].
  simpl. intros. apply H.
  simpl. intros.
  inversion H. apply ai_later. apply ai_here.
  assert(G : appears_in x (v :: t)).
  apply IHt. apply H1.
  inversion G. apply ai_here.
  apply ai_later. apply ai_later. apply H4.
Qed.

Lemma ai_end {X : Type} : forall (l : list X) (x : X),
  appears_in x (snoc l x).
Proof.
  induction l as [|h t].
  simpl. intros. apply ai_here.
  simpl. intros. apply ai_later. apply IHt.
Qed.
  
Lemma appears_rev {X : Type} : forall (l : list X) (x : X),
  appears_in x l -> appears_in x (rev l).
Proof.
  induction l as [|h t].
  simpl. intros. apply H.
  simpl. intros. inversion H.  apply ai_end.
  apply appears_snoc. apply IHt. apply H1.
Qed.                                            
Lemma appears_rearrange_cons {X : Type} : forall (l : list X) (x v : X),
  appears_in x (cons v l) ->
  appears_in x (snoc l v).
Proof.
  intros. inversion H. apply ai_end. apply appears_snoc. apply H1.
Qed.

Lemma appears_comm {X : Type} : forall (l1 l2 : list X) (x : X),
  appears_in x (l1 ++ l2) ->
  appears_in x (l2 ++ l1).
Proof.
  intros l1.
  induction l1 as [|h t].
  simpl. intros. rewrite app_nil_end. simpl in H. apply H.
  simpl. intros.

  assert(G : appears_in  x ((snoc l2 h) ++ t)).
  apply IHt.
  replace (t ++ snoc l2 h) with (snoc (t ++ l2) h).
  apply appears_rearrange_cons. apply H.
  rewrite snoc_sep. rewrite snoc_sep. apply app_assoc.
  rewrite snoc_sep in G. rewrite cons_sep. rewrite app_assoc in G. apply G.
Qed.  

Lemma appears_app_before {X : Type} : forall (l1 l2: list X) (x : X),
  appears_in x l1 -> appears_in x (l2 ++ l1).
Proof.
  intros.
  apply (appears_app_after l1 l2 x) in H.
  apply appears_comm in H.
  apply H.
  (************
   Declaring via "forall", or as a parameter?
***********) 
Qed.

Lemma subseq_cons {X : Type} : forall (l t : list X) (h : X),
  subseq (h :: t) l -> subseq t l.
Proof.
  intros.
  induction l as [|x y]. inversion H.
  inversion H. 
  apply sub_add_one. apply H1.
  apply sub_add_one. apply IHy. apply H2.
Qed.
(*  
  induction t as [|x y].
  intros. apply sub_0.
  intros.
*)

Lemma subseq_refl {X : Type} : forall (l : list X),
  subseq l l.
Proof.
  induction l as [|h t].
  apply sub_0.
  apply sub_add_both. apply IHt.
Qed.
  
Theorem appears_subseq : forall (X:Type) (l1 l2 : list X) (x : X),
  subseq l1 l2 ->
  appears_in x (l1) ->
  appears_in x (l2).
Proof.
  intros. generalize dependent H0. induction H.
  intros. inversion H0.
  intros. inversion H0. apply ai_here. apply ai_later. apply IHsubseq. apply H2.
  intros. apply IHsubseq in H0. apply ai_later. apply H0.
Qed.
(*
  induction l1 as [|h t].
  simpl. intros. inversion H0.
  simpl. intros. apply IHt. apply subseq_cons in H. apply H.
*)

Lemma subseq_insert_mid : forall (X:Type) (l1 l2 : list X) (x : X),
  subseq (l1 ++ l2) (l1 ++ [x] ++ l2).
Proof.
  induction l1 as [|h t].
  simpl. intros. apply sub_add_one. apply subseq_refl.
  simpl. intros. apply sub_add_both. apply IHt.
Qed.

Lemma appears_rearrange : forall (X:Type) (l1 l2 l3 : list X) (x : X), 
  appears_in x ((l1 ++ l2) ++ l3) ->
  appears_in x ((l2 ++ l1) ++ l3).
Proof.
  (*
  intros.
  generalize dependent l1. generalize dependent l2.
  induction l3 as [|h t].
  intros. rewrite app_nil_end. rewrite app_nil_end in H. apply appears_comm. apply H.
  simpl. intros.
  assert(G : appears_in x ((l2 ++ l1) ++ t)).
  apply IHt. assert (G2 : subseq ((l1 ++ l2) ++ t) ((l1 ++ l2) ++ h ::t)).
  apply subseq_insert_mid.

  
  rewrite cons_sep. rewrite cons_sep in H.
  replace ((l2 ++ l1) ++ [h] ++ t) with ((l2 ++ (l1 ++ [h])) ++ t).
  apply (IHt l2 (l1 ++ [h])).
  replace ((l1 ++ l2) ++ [h] ++ t) with ((snoc (l1 ++ l2) h) ++ t) in H.
*)

  
  induction l1 as [|h t].
  simpl. intros. rewrite app_nil_end. apply H.
  simpl. intros. inversion H.
  apply appears_app_after. apply appears_app_before. apply ai_here.
  assert(G : appears_in x ((l2 ++ t) ++ l3)).
  apply IHt.  apply H1.

  rewrite cons_sep. rewrite app_assoc in G. rewrite app_assoc. rewrite app_assoc.

  assert(G2 : subseq (l2 ++ t ++ l3) (l2 ++ h :: t ++ l3)).
  apply subseq_insert_mid.
  apply appears_subseq with (l1:=(l2 ++ t ++ l3)).
  apply G2.
  apply G.
Qed.

(*  
  simpl. intros. apply appears_comm.
  inversion H. apply ai_here.

  inversion H1. rewrite cons_sep.
  rewrite app_assoc. rewrite app_assoc.
  apply appears_comm.
  apply appears_subseq with (l1:= t++l2++l3).
  simpl.
  assert(G : appears_in x (l2 ++ t ++ l3)).
  apply IHt. apply H1. apply 
Qed.
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  induction xs as [|h t].
  intros. right. simpl in H. apply H.
  intros.
  assert(G : appears_in x t \/ appears_in x (h :: ys)).
  apply (IHt (h :: ys) x).
  rewrite cons_sep. rewrite cons_sep in H.
  rewrite <- app_assoc.
  apply appears_rearrange. apply H.
  
  inversion G. left. apply ai_later. apply H0.
  inversion H0. left. apply ai_here. right. apply H2.
Qed.

(*
  apply appears_comm. rewrite app_assoc. apply appears_comm.
  apply appears_comm in H. rewrite <- app_assoc in H. apply appears_comm in H.
  
  rewrite <- app_assoc.
  apply (appears_comm t [h]).

  apply H.
Qed.
*)


Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros.
  inversion H.
  apply (appears_app_after xs ys).
  apply H0.
  apply (appears_app_before ys xs).
  apply H0.
Qed.

(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

Definition disjoint {X : Type} (l1 l2 : list X) : Prop :=
  ~(exists x, appears_in x l1 /\ appears_in x l2).

Example disjoint1 : disjoint [1;3;5] [2;4].
Proof.
  unfold disjoint. unfold not. intros. inversion H.
  inversion H0. inversion H2. rewrite H4 in H1. inversion H1. inversion H6. inversion H9. inversion H12.
  inversion H4. rewrite H7 in H1. inversion H1. inversion H9. inversion H12. inversion H15. inversion H7. Qed.

Example disjoint2 : ~(disjoint [1;3;5] [2;5;6]).
Proof.
  unfold disjoint. unfold not. simpl. intros.
  apply H. exists 5. split. apply ai_later. apply ai_later. apply ai_here. apply ai_later. apply ai_here.
Qed.

(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

Fixpoint no_repeats {X : Type} (l : list X) : Prop :=
  match l with
  | [] => True
  | h :: t => ~(appears_in h t) /\ no_repeats t
  end.

Example no_repeats1 : no_repeats [1;5;2].
Proof. unfold no_repeats. unfold not. split. intros.
       inversion H. inversion H1. inversion H4.
       split. intros. inversion H. inversion H1.
       split. intros. inversion H. apply always_works.
Qed.

Example no_repeats2 : ~(no_repeats [1;5;2;1]).
Proof.
  unfold no_repeats. unfold not. intros.
  inversion H.
  apply H0.
  apply ai_later. apply ai_later. apply ai_here.
Qed.

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)

Theorem disjoint_app {X : Type} : forall (l1 l2 : list X),
  no_repeats l1 ->
  no_repeats l2 ->
  disjoint l1 l2 ->
  no_repeats (l1 ++ l2).
Proof.
  unfold disjoint. unfold not.
  induction l1 as [|h t].
  simpl. intros. apply H0.
  simpl. unfold not. intros.
  inversion H.
  assert(G : no_repeats(t ++ l2)).
  apply IHt. apply H3. apply H0. intro. apply H1. inversion H4.
  inversion H5. exists witness. split.
  apply appears_cons. apply H6. apply H7.
  split.
  intros.
  apply appears_in_app in H4. inversion H4. apply H2 in H5. inversion H5.
  apply H1. exists h. split. apply ai_here. apply H5. apply G.
Qed.


(** **** Exercise: 3 stars (nostutter) *)
(** Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all (except from your study group partner, if
    you have one).

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1,4,1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
  nostutter_empty : nostutter []
  | nostutter_cons : forall (l : list nat) (v : nat),
                       hd_opt l <> Some v -> nostutter l -> nostutter (v :: l).

(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)


Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
Proof. apply nostutter_cons. simpl. unfold not. intros. inversion H.
       apply nostutter_cons. simpl. unfold not. intros. inversion H.
       apply nostutter_cons. simpl. unfold not. intros. inversion H.
       apply nostutter_cons. simpl. unfold not. intros. inversion H.       apply nostutter_cons. simpl. unfold not. intros. inversion H.       apply nostutter_cons. simpl. unfold not. intros. inversion H.       apply nostutter_empty.
       Qed.
Example test_nostutter_1_suggested:      nostutter [3;1;4;1;5;6].
Proof. repeat constructor; unfold not; intro; inversion H. Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
Proof. apply nostutter_empty. Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_2_suggested:  nostutter [].
Proof. repeat constructor; unfold not; intro; inversion H. Qed.

Example test_nostutter_3:  nostutter [5].
Proof. apply nostutter_cons. simpl. unfold not. intros. inversion H. apply nostutter_empty. Qed.

(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)
Example test_nostutter_3_suggested:  nostutter [5].
Proof. repeat constructor; unfold not; intro; inversion H. Qed.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof. unfold not. intro. inversion H. inversion H3. simpl in H6. unfold not in H6. apply H6. reflexivity. Qed.

Example test_nostutter_4_suggested: not (nostutter [3;1;1;4]).
Proof. intro.
       repeat match goal with
           tt : nostutter _ |- _ => inversion tt; clear tt; subst
       end.
       contradiction H1; auto.
       Qed.

(* 
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle) *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma nat_plus_S : forall (x y : nat),
  S x = S y <-> x = y.
Proof.
  intros.
  assert(G : {x = y} + {x <> y}).
  apply eq_nat_dec.
  inversion G. split. intros. apply H. intros. rewrite H. reflexivity.
  unfold not in H. split. intros. inversion H0. reflexivity. intros. rewrite H0. reflexivity.
Qed.
  
Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof.
  induction l1 as [|h t].
  simpl. intros. reflexivity.
  simpl. intros. apply nat_plus_S. apply IHt.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  induction l as [|h t].
  simpl. intros. inversion H.
  simpl. intros. inversion H. exists []. exists t. simpl. reflexivity.
  assert(G : exists l1 : list X, exists l2 : list X, t = l1 ++ x :: l2).
  apply IHt.
  apply H1.
  inversion G.
  inversion H3.
  exists (h :: witness).
  exists witness0.
  simpl. rewrite H4. reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  repeats_here : forall (l : list X) (v : X),
                   appears_in v l -> repeats (v :: l)
  | repeats_later : forall (l : list X) (v : X),
                   repeats l -> repeats (v :: l).

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Lemma length_0 : forall (X:Type) (l :list X),
                   length l = 0 -> l = [].
Proof.
  intros. destruct l as [|h t]. reflexivity. inversion H.
Qed.

(*
Fixpoint occurence {X : Type} (l : list X) (v : X) : Prop -> nat :=
  match l with
  | [] => True -> 0
  | h :: t => (appears_in v [h]) -> 1 + occurence t v
  end.
*)
(*
Eval compute in map (plus 3) [2; 0; 2].

test_map1: map (plus 3) [2; 0; 2] = [5; 3; 5]
test_map2: map oddb [2; 1; 2; 5] = [false; true; false; true]
test_map3:
  map (fun n : nat => [evenb n; oddb n]) [2; 1; 2; 5] =
  [[true; false]; [false; true]; [true; false]; [false; true]]
map_snoc:
  forall (X Y : Type) (f : X -> Y) (l : list X) (v : X),
  map f (snoc l v) = snoc (map f l) (f v)
map_rev:
  forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l)
fold_map_correct:
  forall (X Y : Type) (f : X -> Y) (l : list X), fold_map f l = map f l
*)

Inductive occurence {X:Type} : list X -> X -> nat -> Prop :=
  occur_none : forall (l:list X) (v:X),
                 (occurence l v 0)
  | occur_cons_same : forall (l:list X) (adder:X) (n:nat),
                 (occurence l adder n) ->
                 (occurence (adder :: l) adder (n+1))
  | occur_cons_diff : forall (l:list X) (adder v:X) (n:nat),
                 ~(adder = v) ->
                 (occurence l v n) ->
                 (occurence (adder :: l) v n).

Example occurence_0 : occurence [5;7] 5 1 /\ occurence [5;7] 7 1.
Proof. split.
       apply occur_cons_same with (l:=[7]) (adder:=5) (n:=0).
       apply occur_cons_diff. unfold not. intros. inversion H.
       apply occur_none.

       constructor. unfold not. intros. inversion H.
       apply (occur_cons_same [] 7 0).
       constructor.
Qed.

Example occurence_1 : occurence [1;1;1] 1 0 /\
                      occurence [1;1;1] 1 1 /\
                      occurence [1;1;1] 1 2 /\
                      occurence [1;1;1] 1 3 /\
                      ~(occurence [1;1;1] 1 4).
Proof.
  split.
  constructor.

  split.
  apply occur_cons_same with (n:=0).
  constructor.

  split.
  apply occur_cons_same with (n:=1).
  apply occur_cons_same with (n:=0).
  constructor.

  split.
  apply occur_cons_same with (n:=2).
  apply occur_cons_same with (n:=1).
  apply occur_cons_same with (n:=0).
  constructor.

  unfold not.
  intro.
  inversion H. subst. clear H.
  inversion H3. subst. inversion H1. subst.
  inversion H0. subst. inversion H1. subst.
  inversion H2. rewrite <- H5 in H1. inversion H1.
  contradiction H4. reflexivity.
  contradiction H2. reflexivity.
  contradiction H2. reflexivity.
Qed.

Example occurence_2 : occurence [1;1;2;4;2;1;4;3;1;4] 0 0 /\
                      occurence [1;1;2;4;2;1;4;3;1;4] 1 4 /\
                      occurence [1;1;2;4;2;1;4;3;1;4] 2 2 /\
                      occurence [1;1;2;4;2;1;4;3;1;4] 3 1 /\
                      occurence [1;1;2;4;2;1;4;3;1;4] 4 3 /\
                      occurence [1;1;2;4;2;1;4;3;1;4] 5 0
.
Proof.
  split.
  repeat constructor.

  split.
  apply occur_cons_same with (n:=3).
  apply occur_cons_same with (n:=2).
  constructor. unfold not. intros. inversion H.
  constructor. unfold not. intros. inversion H.
  constructor. unfold not. intros. inversion H.  
  apply occur_cons_same with (n:=1).  
  constructor. unfold not. intros. inversion H.
  constructor. unfold not. intros. inversion H.
  apply occur_cons_same with (n:=0).
  constructor.

  split.
  constructor. unfold not. intros. inversion H.
  constructor. unfold not. intros. inversion H.
  apply occur_cons_same with (n:=1).  
  constructor. unfold not. intros. inversion H.
  apply occur_cons_same with (n:=0).    
  constructor.

  split.
  constructor. unfold not. intros. inversion H.  
  constructor. unfold not. intros. inversion H.
  constructor. unfold not. intros. inversion H.
  constructor. unfold not. intros. inversion H.
  constructor. unfold not. intros. inversion H.
  constructor. unfold not. intros. inversion H.
  constructor. unfold not. intros. inversion H.
  apply occur_cons_same with (n:=0).
  constructor.

  split.
  constructor. unfold not. intros. inversion H.  
  constructor. unfold not. intros. inversion H.
  constructor. unfold not. intros. inversion H.
  apply occur_cons_same with (n:=2).
  constructor. unfold not. intros. inversion H.  
  constructor. unfold not. intros. inversion H.
  apply occur_cons_same with (n:=1).
  constructor. unfold not. intros. inversion H.  
  constructor. unfold not. intros. inversion H.  
  apply occur_cons_same with (n:=0).
  constructor.

  repeat constructor.
Qed.



Inductive frequency {X:Type} : list X -> X -> nat -> Prop :=
  freq : forall (l:list X) (v:X) (n:nat),
                (occurence l v n) ->
                ~(occurence l v (n+1)) ->
                (frequency l v n).

Example frequency_0 : frequency [5;7] 5 1 /\
                      frequency [5;7] 7 1 /\
                      frequency [5;7] 6 0.
Proof. split. constructor. apply occur_cons_same with (n:=0).
       constructor. unfold not. intros.
       inversion H. rewrite plus_comm in H1. inversion H1. rewrite H5 in H3. simpl in H3. inversion H3. inversion H10. inversion H5. inversion H11.
       
       split.
       constructor. apply occur_cons_diff. unfold not. intros. inversion H.
       apply occur_cons_same with (n:=0). constructor.
       unfold not. intros. inversion H. inversion H5.
       rewrite plus_comm in H7. inversion H7. rewrite H11 in H9. simpl in H9. inversion H9. contradiction H8. reflexivity.

       constructor. constructor. unfold not. intros.
       inversion H. inversion H5. inversion H11.
Qed.

Theorem freq_sum_length : forall (X:Type) (l:list X),
        excluded_middle ->
        (forall x,
        exists n, (frequency l x n) /\ ~(frequency l x (n+1))).
Admitted.

(*
Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
  unfold excluded_middle. intros. generalize dependent l1.
  induction l2 as [|h2 t2].
  simpl. intros. apply ex_falso_quodlibet.
  destruct l1 as [|h1 t1]. inversion H1.
  assert(G : appears_in h1 [] -> False). intro. inversion H2.
  apply G. apply H0. apply ai_here.

  
  simpl. intro. induction l1 as [|h1 t1]. simpl. intros. inversion H1.

  simpl. intros.
  apply IHt2. intros. assert(G : x = h2 \/ x <> h2). apply H. inversion G.
  admit.
  assert(G' : appears_in x (h2 :: t2)). apply H0. apply H2.
  inversion G'. rewrite H5 in H3. unfold not in H3. apply ex_falso_quodlibet. apply H3. reflexivity. apply H5. simpl.
  apply Sn_le_Sm__n_le_m in H1.
  apply Sn_le_Sm__n_le_m. 

          


  
  simpl. intros. inversion H1.
  
  unfold excluded_middle. intros. generalize dependent l2.
  induction l1 as [|x l1'].
  intros. inversion H1.
  intros. assert(G : (appears_in x l1') \/ ~(appears_in x l1')). apply H.
  inversion G.
  apply repeats_here. apply H2.
  apply repeats_later. induction l2 as [|h t].
  apply ex_falso_quodlibet. assert(G' : appears_in x [] -> False).
  intros. inversion H3. apply G'. apply H0. apply ai_here.

(*  apply IHt. intros. apply H0 in H3. *)
  
  unfold not in H2.
  apply IHl1' with (l2:=t). intros.
  assert(G' : (x0 = x) \/ x0 <> x). apply H. inversion G'. rewrite H4 in H3. apply H2 in H3. inversion H3.
  apply ai_later with (b:=x) in H3. apply H0 in H3. inversion H3.
  admit.

  
  apply H6. simpl in H1. apply Sn_le_Sm__n_le_m in H1. apply H1.

  (*
  intros. apply H0. apply ai_later. apply H3. simpl.

  apply ex_falso_quodlibet. unfold not in H2. apply H2. 
  apply IHl1' with (l2:=l2).
  
  
  unfold excluded_middle.
  intros X l1 l2 excluded_middle. generalize dependent l2.
  induction l1 as [|x l1'].
  simpl. intros. inversion H0.
  simpl. intros.
  destruct l1' as [|h t]. inversion H0. apply length_0 in H2. assert (G : appears_in x l2). apply H. apply ai_here. rewrite H2 in G. inversion G. inversion H2.
  simpl in H0.
  assert(G : x = h \/ x <> h).
  apply excluded_middle.
  inversion G.
  rewrite H1. apply repeats_here.
  simpl in IHl1'. apply repeats_later.
  destruct l2 as[|h2 t2].
  assert(G2 : ~(appears_in x [])). unfold not. intros. inversion H2.
  unfold not in G2. apply ex_falso_quodlibet. apply G2. apply H with (x0:=x). apply ai_here. (** THERE SHOULD BE MORE SIMPLE WAY :( **)
  apply IHl1' with (l2:=t2).

  intros. 


  
  simpl in H0. apply Sn_le_Sm__n_le_m in H0. apply H0.
*)
Qed.
*)

(* $Date: 2014-02-22 09:43:41 -0500 (Sat, 22 Feb 2014) $ *)
