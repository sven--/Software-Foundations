(** * Induction: Proof by Induction *)
 

(** The next line imports all of our definitions from the
    previous chapter. *)

Require Export Basics.

(** For it to work, you need to use [coqc] to compile [Basics.v]
    into [Basics.vo].  (This is like making a .class file from a .java
    file, or a .o file from a .c file.)
  
    Here are two ways to compile your code:
  
     - CoqIDE:
   
         Open [Basics.v].
         In the "Compile" menu, click on "Compile Buffer".
   
     - Command line:
   
         Run [coqc Basics.v]

    *)

(* ###################################################################### *)
(** * Naming Cases *)

(** The fact that there is no explicit command for moving from
    one branch of a case analysis to the next can make proof scripts
    rather hard to read.  In larger proofs, with nested case analyses,
    it can even become hard to stay oriented when you're sitting with
    Coq and stepping through the proof.  (Imagine trying to remember
    that the first five subgoals belong to the inner case analysis and
    the remaining seven cases are what remains of the outer one...)
    Disciplined use of indentation and comments can help, but a better
    way is to use the [Case] tactic. *)

(** [Case] is not built into Coq: we need to define it ourselves.
    There is no need to understand how it works -- you can just skip
    over the definition to the example that follows.  It uses some
    facilities of Coq that we have not discussed -- the string
    library (just for the concrete syntax of quoted strings) and the
    [Ltac] command, which allows us to declare custom tactics.  Kudos
    to Aaron Bohannon for this nice hack! *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.
(** Here's an example of how [Case] is used.  Step through the
   following proof and observe how the context changes. *)

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".  (* <----- here *)
    reflexivity.
  Case "b = false".  (* <---- and here *)
    rewrite <- H. 
    reflexivity.  
Qed.

(** [Case] does something very straightforward: It simply adds a
    string that we choose (tagged with the identifier "Case") to the
    context for the current goal.  When subgoals are generated, this
    string is carried over into their contexts.  When the last of
    these subgoals is finally proved and the next top-level goal
    becomes active, this string will no longer appear in the context
    and we will be able to see that the case where we introduced it is
    complete.  Also, as a sanity check, if we try to execute a new
    [Case] tactic while the string left by the previous one is still
    in the context, we get a nice clear error message.

    For nested case analyses (e.g., when we want to use a [destruct]
    to solve a goal that has itself been generated by a [destruct]),
    there is an [SCase] ("subcase") tactic. *)

(** **** Exercise: 2 stars (andb_true_elim2) *)
(** Prove [andb_true_elim2], marking cases (and subcases) when
    you use [destruct]. *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  Case "b is true".
  simpl.
  intros H.
  rewrite -> H.
  reflexivity.
  Case "b is false".
  simpl.
  intros H'.
  destruct c.
  SCase "c is true".
  reflexivity.
  SCase "c is false".
  rewrite -> H'.
  reflexivity.
Qed.

(** [] *)

(** There are no hard and fast rules for how proofs should be
    formatted in Coq -- in particular, where lines should be broken
    and how sections of the proof should be indented to indicate their
    nested structure.  However, if the places where multiple subgoals
    are generated are marked with explicit [Case] tactics placed at
    the beginning of lines, then the proof will be readable almost no
    matter what choices are made about other aspects of layout.

    This is a good place to mention one other piece of (possibly
    obvious) advice about line lengths.  Beginning Coq users sometimes
    tend to the extremes, either writing each tactic on its own line
    or entire proofs on one line.  Good style lies somewhere in the
    middle.  In particular, one reasonable convention is to limit
    yourself to 80-character lines.  Lines longer than this are hard
    to read and can be inconvenient to display and print.  Many
    editors have features that help enforce this. *)

(* ###################################################################### *)
(** * Proof by Induction *)

(** We proved in the last chapter that [0] is a neutral element
    for [+] on the left using a simple argument.  The fact that it is
    also a neutral element on the _right_... *)

Theorem plus_0_r_firsttry : forall n:nat,
  n + 0 = n.

(** ... cannot be proved in the same simple way.  Just applying
  [reflexivity] doesn't work: the [n] in [n + 0] is an arbitrary
  unknown number, so the [match] in the definition of [+] can't be
  simplified.  *)

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

(** *** *)

(** And reasoning by cases using [destruct n] doesn't get us much
   further: the branch of the case analysis where we assume [n = 0]
   goes through, but in the branch where [n = S n'] for some [n'] we
   get stuck in exactly the same way.  We could use [destruct n'] to
   get one step further, but since [n] can be arbitrarily large, if we
   try to keep on like this we'll never be done. *)

Theorem plus_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'].
  Case "n = 0".
    reflexivity. (* so far so good... *)
  Case "n = S n'".
    simpl.       (* ...but here we are stuck again *)
Abort.

(** *** *)

(** To prove such facts -- indeed, to prove most interesting
    facts about numbers, lists, and other inductively defined sets --
    we need a more powerful reasoning principle: _induction_.

    Recall (from high school) the principle of induction over natural
    numbers: If [P(n)] is some proposition involving a natural number
    [n] and we want to show that P holds for _all_ numbers [n], we can
    reason like this:
         - show that [P(O)] holds;
         - show that, for any [n'], if [P(n')] holds, then so does
           [P(S n')];
         - conclude that [P(n)] holds for all [n].

    In Coq, the steps are the same but the order is backwards: we
    begin with the goal of proving [P(n)] for all [n] and break it
    down (by applying the [induction] tactic) into two separate
    subgoals: first showing [P(O)] and then showing [P(n') -> P(S
    n')].  Here's how this works for the theorem we are trying to
    prove at the moment: *)

(** *** *)

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".     reflexivity.
  Case "n = S n'".  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Like [destruct], the [induction] tactic takes an [as...]
    clause that specifies the names of the variables to be introduced
    in the subgoals.  In the first branch, [n] is replaced by [0] and
    the goal becomes [0 + 0 = 0], which follows by simplification.  In
    the second, [n] is replaced by [S n'] and the assumption [n' + 0 =
    n'] is added to the context (with the name [IHn'], i.e., the
    Induction Hypothesis for [n']).  The goal in this case becomes [(S
    n') + 0 = S n'], which simplifies to [S (n' + 0) = S n'], which in
    turn follows from the induction hypothesis. *)

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** **** Exercise: 2 stars (basic_induction) *)

(** Prove the following lemmas using induction. You might need
    previously proven results. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros IHn.
  induction IHn as [|n].
  Case "n is 0".
  reflexivity.
  Case "n under IH n-1".
  Check IHn.
  simpl.
  rewrite -> IHn.
  reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n'].
  Case "n is 0".
  reflexivity.
  Case "n under IH of n-1".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [|n'].
  Case "n is 0".
  rewrite -> (plus_0_r m).
  reflexivity.
  Case "n under IH n-1".
  rewrite <- (plus_n_Sm m n').
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction m as [|m'].
  Case "m is 0".
  simpl.
  rewrite -> (plus_comm n 0).
  reflexivity.
  Case "m under IH of m-1".
  rewrite -> (plus_comm n (S m' + p)).
  rewrite <- (plus_n_Sm n m').
  simpl.
  rewrite -> (plus_comm (m' + p) n).
  rewrite -> IHm'.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars (double_plus) *)

(** Consider the following function, which doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  induction n as [|n'].
  Case "n is 0".
  reflexivity.
  Case "n under IH of n-1".
  simpl.
  rewrite -> IHn'.
  rewrite <- (plus_n_Sm n' n').
  reflexivity.
Qed.


(** **** Exercise: 1 star (destruct_induction) *)
(** Briefly explain the difference between the tactics
    [destruct] and [induction].  *)

(**
INDUCTION
http://coq.inria.fr/distrib/current/refman/Reference-Manual010.html#hevea_tactic71
This tactic applies to any goal. The argument term must be of inductive type and the tactic induction generates subgoals, one for each possible form of term, i.e. one for each constructor of the inductive type.

If the argument is dependent in either the conclusion or some hypotheses of the goal, the argument is replaced by the appropriate constructor form in each of the resulting subgoals and induction hypotheses are added to the local context using names whose prefix is IH.

There are particular cases:

    If term is an identifier ident denoting a quantified variable of the conclusion of the goal, then induction ident behaves as intros until ident; induction ident.
    If term is a num, then induction num behaves as intros until num followed by induction applied to the last introduced hypothesis. Remark: For simple induction on a numeral, use syntax induction (num) (not very interesting anyway).
    The argument term can also be a pattern of which holes are denoted by “_”. In this case, the tactic checks that all subterms matching the pattern in the conclusion and the hypotheses are compatible and performs induction using this subterm.


DESTRUCT
This tactic applies to any goal. The argument term must be of inductive or co-inductive type and the tactic generates subgoals, one for each possible form of term, i.e. one for each constructor of the inductive or co-inductive type. Unlike induction, no induction hypothesis is generated by destruct.

If the argument is dependent in either the conclusion or some hypotheses of the goal, the argument is replaced by the appropriate constructor form in each of the resulting subgoals, thus performing case analysis. If non-dependent, the tactic simply exposes the inductive or co-inductive structure of the argument. *)


(* ###################################################################### *)
(** * Proofs Within Proofs *)


(** In Coq, as in informal mathematics, large proofs are very
    often broken into a sequence of theorems, with later proofs
    referring to earlier theorems.  Occasionally, however, a proof
    will need some miscellaneous fact that is too trivial (and of too
    little general interest) to bother giving it its own top-level
    name.  In such cases, it is convenient to be able to simply state
    and prove the needed "sub-theorem" right at the point where it is
    used.  The [assert] tactic allows us to do this.  For example, our
    earlier proof of the [mult_0_plus] theorem referred to a previous
    theorem named [plus_O_n].  We can also use [assert] to state and
    prove [plus_O_n] in-line: *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). (** forall n : nat, ~~ *)
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.  Qed.

Theorem mult_1_plus : forall n m : nat,
  (1 + n) * m = n * m + m.
Proof.
  simpl.
  intros n m.
  rewrite -> (plus_comm m (n * m)).
  reflexivity.
Qed.

Theorem mult_l_0 : forall n : nat,
  n * 0 = 0.
  induction n as [|n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n under IH of n-1".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem mult_l_1 : forall n : nat,
  n * 1 = n.
  induction n as [|n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n under IH of n-1".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.




(** The [assert] tactic introduces two sub-goals.  The first is
    the assertion itself; by prefixing it with [H:] we name the
    assertion [H].  (Note that we could also name the assertion with
    [as] just as we did above with [destruct] and [induction], i.e.,
    [assert (0 + n = n) as H].  Also note that we mark the proof of
    this assertion with a [Case], both for readability and so that,
    when using Coq interactively, we can see when we're finished
    proving the assertion by observing when the ["Proof of assertion"]
    string disappears from the context.)  The second goal is the same
    as the one at the point where we invoke [assert], except that, in
    the context, we have the assumption [H] that [0 + n = n].  That
    is, [assert] generates one subgoal where we must prove the
    asserted fact and a second subgoal where we can use the asserted
    fact to make progress on whatever we were trying to prove in the
    first place. *)

(** Actually, [assert] will turn out to be handy in many sorts of
    situations.  For example, suppose we want to prove that [(n + m)
    + (p + q) = (m + n) + (p + q)]. The only difference between the
    two sides of the [=] is that the arguments [m] and [n] to the
    first inner [+] are swapped, so it seems we should be able to
    use the commutativity of addition ([plus_comm]) to rewrite one
    into the other.  However, the [rewrite] tactic is a little stupid
    about _where_ it applies the rewrite.  There are three uses of
    [+] here, and it turns out that doing [rewrite -> plus_comm]
    will affect only the _outer_ one. *)

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)...
     it seems like plus_comm should do the trick! *)
  rewrite -> (plus_comm n m).
  (* Doesn't work...Coq rewrote the wrong plus! *)
  reflexivity.
Qed.

(** To get [plus_comm] to apply at the point where we want it, we can
    introduce a local lemma stating that [n + m = m + n] (for
    the particular [m] and [n] that we are talking about here), prove
    this lemma using [plus_comm], and then use this lemma to do the
    desired rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.  Qed.

(** **** Exercise: 4 stars (mult_comm) *)
(** Use [assert] to help prove this theorem.  You shouldn't need to
    use induction. *)

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> (plus_assoc).
  rewrite -> (plus_assoc).
(**  rewrite -> (plus_comm n m). *)
  assert (H : n + m = m + n).
  Case "assertion".
    rewrite -> plus_comm.
    reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem mult_plus_1 : forall n m : nat,
  n * (1 + m) = n * m + n.
Proof.
  simpl.
  intros n m.
  induction n as [|n'].
  Case "0".
  simpl.
  reflexivity.
  Case "n under IH of n-1".
  simpl.
  rewrite -> IHn'.
  rewrite -> plus_n_Sm.
  rewrite -> plus_n_Sm.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

(** Now prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.)  You may find that [plus_swap] comes in
    handy. *)

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros n m.
  induction n as [|n'].
  Case "n is 0".
  simpl.
  rewrite mult_0_r.
  reflexivity.
  Case "n under IH of n-1".
  simpl.
  rewrite -> IHn'.
  rewrite -> mult_plus_1.
  rewrite -> plus_comm.
  reflexivity.
Qed.

(** **** Exercise: 2 stars, optional (evenb_n__oddb_Sn) *)

(** Prove the following simple fact: *)

Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  simpl.
  induction n as [|n'].
  Case "n = 0".
  reflexivity.
  Case "n under IH of n-1".
  rewrite -> IHn'.
  assert(H : evenb(S n') = negb(evenb(n'))).
    SCase "assertion".
    simpl.
    rewrite -> IHn'.
    rewrite -> negb_involutive.
    reflexivity.
  rewrite -> H.
  rewrite -> IHn'.
  reflexivity.
Qed.

(* ###################################################################### *)
(** * More Exercises *)

(** **** Exercise: 3 stars, optional (more_exercises) *)
(** Take a piece of paper.  For each of the following theorems, first
    _think_ about whether (a) it can be proved using only
    simplification and rewriting, (b) it also requires case
    analysis ([destruct]), or (c) it also requires induction.  Write
    down your prediction.  Then fill in the proof.  (There is no need
    to turn in your piece of paper; this is just to encourage you to
    reflect before hacking!) *)

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  induction n as [|n'].
  Case "0".
  reflexivity.
  Case "n under IHn'".
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  simpl.
  destruct b as [|b'].
  reflexivity.
  reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat, 
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  induction p as [|p'].
  simpl.
  intros H.
  rewrite -> H.
  reflexivity.
  simpl.
  intros a.
  rewrite <- IHp'.
  reflexivity.
  rewrite -> a.
  reflexivity.
Qed.

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite -> plus_n_Sm.
  rewrite -> plus_comm.
  reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros a b.
  destruct a as [|].
  Case "a true".
  simpl.
  assert (H : orb b (negb b) = true).
  SCase "assertion".
    destruct b as [|].
    reflexivity.
    reflexivity.
  rewrite -> H.
  reflexivity.
  Case "a false".
  simpl.
  reflexivity.
Qed.


Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  rewrite -> (mult_comm (n + m) p).
  rewrite -> (mult_comm n p).
  rewrite -> (mult_comm m p).
  induction p as [|p'].
  Case "p = 0".
  simpl.
  reflexivity.
  Case "p under IHp'".
  simpl.
  rewrite -> IHp'.
  assert(H : forall a b c d : nat, a + b + (c + d) = a + c + (b + d)).
    SCase "assertion".
    intros a b c d.
    rewrite -> plus_assoc.
    rewrite -> plus_assoc.
    rewrite -> plus_comm.
    rewrite -> (plus_comm (a + c + b) d).
    rewrite <- (plus_assoc a b c).
    rewrite <- (plus_assoc a c b).
    rewrite -> (plus_comm b c).
    reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  induction n as [|n'].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n under IHn'".
  simpl.
  intros m p.
  rewrite -> IHn'.
  rewrite -> mult_plus_distr_r.
  reflexivity.
Qed.

(** **** Exercise: 2 stars, optional (beq_nat_refl) *)
(** Prove the following theorem.  Putting [true] on the left-hand side
of the equality may seem odd, but this is how the theorem is stated in
the standard library, so we follow suit.  Since rewriting 
works equally well in either direction, we will have no 
problem using the theorem no matter which way we state it. *)

Theorem beq_nat_refl : forall n : nat, 
  true = beq_nat n n.
Proof.
  intros n.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

(** **** Exercise: 2 stars, optional (plus_swap') *)
(** The [replace] tactic allows you to specify a particular subterm to
   rewrite and what you want it rewritten to.  More precisely,
   [replace (t) with (u)] replaces (all copies of) expression [t] in
   the goal by expression [u], and generates [t = u] as an additional
   subgoal. This is often useful when a plain [rewrite] acts on the wrong
   part of the goal.  

   Use the [replace] tactic to do a proof of [plus_swap'], just like
   [plus_swap] but without needing [assert (n + m = m + n)]. 
*)

Theorem plus_swap' : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> (plus_assoc).
  rewrite -> (plus_assoc).
(**  rewrite -> (plus_comm n m). *)
  replace (n+m) with (m+n).
  reflexivity.
  rewrite -> plus_comm.
  reflexivity.
Qed.

(** **** Exercise: 3 stars (binary_commute) *)
(** Recall the [increment] and [binary-to-unary] functions that you
    wrote for the [binary] exercise in the [Basics] chapter.  Prove
    that these functions commute -- that is, incrementing a binary
    number and then converting it to unary yields the same result as
    first converting it to unary and then incrementing.

    (Before you start working on this exercise, please copy the
    definitions from your solution to the [binary] exercise here so
    that this file can be graded on its own.  If you find yourself
    wanting to change your original definitions to make the property
    easier to prove, feel free to do so.) *)

Check bin.
Check incr.
Check to_unary.

Theorem binary_commute : forall n : bin, to_unary(incr(n)) = 1+(to_unary(n)).
Proof.
  induction n as[|n0|n1].
  Case "n = 0".
  simpl.
  reflexivity.
  Case "n under IHn0, which means n = xxx0".
  simpl.
  rewrite -> plus_0_r.
  rewrite -> plus_n_Sm.
  rewrite <- (plus_assoc (to_unary n0) (to_unary n0) 1).
  rewrite -> plus_comm.
  rewrite <- plus_assoc.
  rewrite -> (plus_1_l (to_unary n0)).
  reflexivity.
  Case "n under IHn1, which means n = xxx1".
  simpl.
  rewrite -> plus_0_r.
  rewrite -> plus_0_r.
  rewrite -> IHn1.
  simpl.
  rewrite <- plus_assoc.
  rewrite -> (plus_comm (to_unary n1) 1).
  rewrite -> (plus_1_l (to_unary n1)).
  reflexivity.
Qed.



(** **** Exercise: 5 stars, advanced (binary_inverse) *)
(** This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    the previous exercise to complete this one.

    (a) First, write a function to convert natural numbers to binary
        numbers.  Then prove that starting with any natural number,
        converting to binary, then converting back yields the same
        natural number you started with.

    (b) You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, it is not true!
        Explain what the problem is.

    (c) Define a function [normalize] from binary numbers to binary
        numbers such that for any binary number b, converting to a
        natural and then back to binary yields [(normalize b)].  Prove
        it.

    Again, feel free to change your earlier definitions if this helps
    here. 
*)

Fixpoint to_binary (n : nat) : bin :=
  match n with
  | 0 => O'
  | S n' => incr(to_binary(n'))
  end.

Lemma conversion_plus_1 :
  forall n : bin, to_unary(incr(n)) = to_unary(n) + 1.
Proof.
  induction n as [|n0|n1].
  Case "0".
  simpl.
  reflexivity.
  Case "n0".
  simpl.
  rewrite -> plus_0_r.
  reflexivity.
  Case "n1".
  simpl.
  rewrite -> plus_0_r.
  rewrite -> plus_0_r.
  rewrite -> IHn1.
  rewrite -> plus_assoc.
  rewrite -> plus_comm.
  rewrite -> (plus_comm ((to_unary n1) + (to_unary n1) + 1) 1).
  rewrite <- (plus_assoc (to_unary n1) 1 (to_unary n1)).
  rewrite <- (plus_assoc (to_unary n1) (to_unary n1) 1).
  replace (1 + to_unary n1) with (to_unary n1 + 1).
  reflexivity.
  rewrite -> plus_comm.
  reflexivity.
Qed.

Theorem conversion_involutive :
  forall n : nat, to_unary(to_binary(n)) = n.
Proof.
  induction n as [|n'].
  Case "0".
  simpl.
  reflexivity.
  Case "IHn'".
  simpl.
  destruct (to_binary n') as [|n'0|n'1].
  SCase "0".
  rewrite <- IHn'.
  simpl. reflexivity.
  SCase "n'0".
  rewrite <- IHn'.
  simpl.
  rewrite -> plus_0_r.
  rewrite <- (plus_1_l ((to_unary n'0) + (to_unary n'0))).
  rewrite -> (plus_comm ((to_unary n'0) + (to_unary n'0)) 1).
  reflexivity.
  SCase "n'1".
  rewrite <- IHn'.
  simpl.
  rewrite -> plus_0_r.
  rewrite -> plus_0_r.
  rewrite -> plus_n_Sm.
  replace (to_unary(incr n'1)) with (to_unary(n'1) + 1).
  rewrite <- (plus_1_l 1).
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  rewrite -> plus_comm.
  rewrite -> (plus_comm ((to_unary n'1) + (to_unary n'1) + 1) 1).
  rewrite <- plus_assoc.
  rewrite <- plus_assoc.
  rewrite -> (plus_comm 1 (to_unary n'1)).
  reflexivity.
  rewrite -> conversion_plus_1.
  reflexivity.
Qed.

(** (b)
binary A*O is all maped to 0, not injective. *)


Fixpoint reverse (n m : bin) : bin :=
  match n with
  | O' => m
  | A n' => (reverse n' (A m))
  | B n' => ((reverse n') (B m))
  end.
Eval compute in to_unary(A(B(A(O')))).
Eval compute in to_unary(B(B(B(O')))).

Eval compute in reverse (B(B(B(B(O'))))) O'.

Eval compute in reverse (B(B(B(A(O'))))) O'.
Eval compute in reverse (B(B(A(B(O'))))) O'.
Eval compute in reverse (B(A(B(B(O'))))) O'.
Eval compute in reverse (A(B(B(B(O'))))) O'.

Eval compute in reverse (B(B(A(A(O'))))) O'.
Eval compute in reverse (B(A(B(A(O'))))) O'.
Eval compute in reverse (A(B(B(A(O'))))) O'.
Eval compute in reverse (B(A(A(B(O'))))) O'.
Eval compute in reverse (A(B(A(B(O'))))) O'.
Eval compute in reverse (A(A(B(B(O'))))) O'.

Fixpoint reverse_depth (d : nat) (n m : bin) : bin :=
  match d with
  | 0 => O'
  | S d' =>
    match n with
    | O' => m
    | A n' => (reverse_depth (d-1) n' (A m)) 
    | B n' => (reverse_depth (d-1) n') (B m)
    end
  end.

Eval compute in (reverse_depth 5 (B(B(A(A(O'))))) O').

Theorem reverse_involutive :
  forall n : bin, (reverse (reverse n O') O') = n.
Proof.
  intros n.
  induction n as [|n0|n1].
  Case "0".
  simpl.
  reflexivity.
  Case "n0".
  simpl.
  Abort.




Fixpoint len (n : bin) :=
  match n with
  | O' => 1
  | A n' => 1 + len(n')
  | B n' => 1 + len(n')
  end.

Eval compute in len(to_binary(8)).
Eval compute in len(to_binary(7)).
Eval compute in len(to_binary(6)).
Eval compute in len(to_binary(5)).
Eval compute in len(to_binary(4)).
Eval compute in len(to_binary(3)).
Eval compute in len(to_binary(2)).
Eval compute in len(to_binary(1)).
Eval compute in len(to_binary(0)).

Theorem reverse_depth_0 :
  forall n : bin, (reverse_depth 0 n O') = O'.
Proof.
  destruct n as [|n0|n1].
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Theorem reverse_depth_involutive :
  forall n : bin, (reverse_depth (len n) (reverse_depth (len n) n O') O') = n.
Proof.
  intros n.
  induction (len n) as [|l'].
  simpl.
  rewrite -> reverse_depth_0.
  Abort.
    

(**
A*B[A|B]*O -> B[A|B]*O
A*O -> O
 *)

(**
Fixpoint sub_normalize (n : bin) : bin :=
  match n with
  | O' => O'
  | A n' => sub_normalize(n')
  | B n' => n
  end.

Fixpoint sub_normalize_2 (n : bin) : nat :=
  match n with
  | O' => 0
  | A n' => 1 + sub_normalize_2(n')
  | B n' => 1
  end.
*)

Fixpoint normalize (n : bin) : bin :=
  match n with
  | O' => O'
  | A n' =>
    match normalize(n') with
    | O' => O'
    | A n'' => A(A(n''))
    | B n'' => A(B(n''))
    end
  | B n' => B (normalize n')
  end.

Eval compute in normalize(A(A(A(O')))).
Eval compute in normalize(B(A(A(A(O'))))).
Eval compute in normalize(A(B(A(A(A(O')))))).
Eval compute in normalize(B(A(B(A(A(A(O'))))))).
Eval compute in normalize(A(B(A(B(A(A(A(O')))))))).

Lemma tmp : forall n : bin, normalize(n) = O' -> to_unary(n) = 0.
Proof.
  intros v w.
  induction v as [|n0|n1] eqn:T.
  Case "0".
  simpl. reflexivity.
  Case "n0".
  simpl.

  rewrite -> IHn0.
  reflexivity.
Abort.  

Theorem conversion_involutive_inverse :
  forall n : bin, to_binary(to_unary(n)) = normalize(n).
Proof.
  intros n.
  induction n as [|n0|n1] eqn:T.
  Case "0".
  simpl.
  reflexivity.
  Case "n0".
  simpl.
  rewrite -> plus_0_r.
  induction (normalize n0) as [|x|y] eqn:TT.
Abort.
(**
  
  rewrite <- IHn0.
  destruct (to_binary (to_unary n0)) as [|x|y].
  simpl.

  induction (to_unary n0) as [|x].
    SCase "0".
    simpl.
    reflexivity.
    SCase "x".
    simpl.
    rewrite -> plus_comm.
    simpl.
    rewrite -> IHx.
    
  assert(H : forall a : nat, to_binary(a + a) = A(to_binary(a))).
    SCase "assertion".
    induction a as [|a'].
    simpl. 
Qed.
*)

(* ###################################################################### *)
(** * Advanced Material *)

(** ** Formal vs. Informal Proof *)

(** "Informal proofs are algorithms; formal proofs are code." *)

(** The question of what, exactly, constitutes a "proof" of a
    mathematical claim has challenged philosophers for millennia.  A
    rough and ready definition, though, could be this: a proof of a
    mathematical proposition [P] is a written (or spoken) text that
    instills in the reader or hearer the certainty that [P] is true.
    That is, a proof is an act of communication.

    Now, acts of communication may involve different sorts of readers.
    On one hand, the "reader" can be a program like Coq, in which case
    the "belief" that is instilled is a simple mechanical check that
    [P] can be derived from a certain set of formal logical rules, and
    the proof is a recipe that guides the program in performing this
    check.  Such recipes are _formal_ proofs.

    Alternatively, the reader can be a human being, in which case the
    proof will be written in English or some other natural language,
    thus necessarily _informal_.  Here, the criteria for success are
    less clearly specified.  A "good" proof is one that makes the
    reader believe [P].  But the same proof may be read by many
    different readers, some of whom may be convinced by a particular
    way of phrasing the argument, while others may not be.  One reader
    may be particularly pedantic, inexperienced, or just plain
    thick-headed; the only way to convince them will be to make the
    argument in painstaking detail.  But another reader, more familiar
    in the area, may find all this detail so overwhelming that they
    lose the overall thread.  All they want is to be told the main
    ideas, because it is easier to fill in the details for themselves.
    Ultimately, there is no universal standard, because there is no
    single way of writing an informal proof that is guaranteed to
    convince every conceivable reader.  In practice, however,
    mathematicians have developed a rich set of conventions and idioms
    for writing about complex mathematical objects that, within a
    certain community, make communication fairly reliable.  The
    conventions of this stylized form of communication give a fairly
    clear standard for judging proofs good or bad.

    Because we are using Coq in this course, we will be working
    heavily with formal proofs.  But this doesn't mean we can ignore
    the informal ones!  Formal proofs are useful in many ways, but
    they are _not_ very efficient ways of communicating ideas between
    human beings. *)

(** For example, here is a proof that addition is associative: *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n']. reflexivity. 
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** Coq is perfectly happy with this as a proof.  For a human,
    however, it is difficult to make much sense of it.  If you're used
    to Coq you can probably step through the tactics one after the
    other in your mind and imagine the state of the context and goal
    stack at each point, but if the proof were even a little bit more
    complicated this would be next to impossible.  Instead, a
    mathematician might write it something like this: *)
(** - _Theorem_: For any [n], [m] and [p],
      n + (m + p) = (n + m) + p.
    _Proof_: By induction on [n].

    - First, suppose [n = 0].  We must show 
        0 + (m + p) = (0 + m) + p.  
      This follows directly from the definition of [+].

    - Next, suppose [n = S n'], where
        n' + (m + p) = (n' + m) + p.
      We must show
        (S n') + (m + p) = ((S n') + m) + p.
      By the definition of [+], this follows from
        S (n' + (m + p)) = S ((n' + m) + p),
      which is immediate from the induction hypothesis. [] *)

(** The overall form of the proof is basically similar.  This is
    no accident: Coq has been designed so that its [induction] tactic
    generates the same sub-goals, in the same order, as the bullet
    points that a mathematician would write.  But there are
    significant differences of detail: the formal proof is much more
    explicit in some ways (e.g., the use of [reflexivity]) but much
    less explicit in others (in particular, the "proof state" at any
    given point in the Coq proof is completely implicit, whereas the
    informal proof reminds the reader several times where things
    stand). *)

(** Here is a formal proof that shows the structure more
    clearly: *)

Theorem plus_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n']. 
  Case "n = 0".
    reflexivity. 
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.   Qed.

(** **** Exercise: 2 stars, advanced (plus_comm_informal) *)
(** Translate your solution for [plus_comm] into an informal proof. *)

(** Theorem: Addition is commutative.
Proof : By induction on n.
When n = 0 =>
statement is directly derived from the definition of natural numbers and addition.
Suppose statement holds for n = n'-1, when n = n' =>
n'+m = m+n' <=> n'+m-1 = m+n'-1 <=> n'-1+m = m+n'-1 <=> induction hypothesis.
This completes the proof.

*)

(** **** Exercise: 2 stars, optional (beq_nat_refl_informal) *)
(** Write an informal proof of the following theorem, using the
    informal proof of [plus_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!
 
    Theorem: [true = beq_nat n n] for any [n].
    
    Proof: (* FILL IN HERE *)
[]
 *)

(* $Date: 2014-02-19 21:36:35 -0500 (Wed, 19 Feb 2014) $ *)
