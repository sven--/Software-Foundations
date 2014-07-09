(** * Prop: Propositions and Evidence *)

Require Export Logic.



(* ####################################################### *)
(** ** From Boolean Functions to Propositions *)

(** In chapter [Basics] we defined a _function_ [evenb] that tests a
    number for evenness, yielding [true] if so.  We can use this
    function to define the _proposition_ that some number [n] is
    even: *)

Definition even (n:nat) : Prop := 
  evenb n = true.

(** That is, we can define "[n] is even" to mean "the function [evenb]
    returns [true] when applied to [n]."  

    Note that here we have given a name
    to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. This isn't a fundamentally
    new kind of proposition;  it is still just an equality. *)

(** Another alternative is to define the concept of evenness
    directly.  Instead of going via the [evenb] function ("a number is
    even if a certain computation yields [true]"), we can say what the
    concept of evenness means by giving two different ways of
    presenting _evidence_ that a number is even. *)

(** ** Inductively Defined Propositions *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).


(** This definition says that there are two ways to give
    evidence that a number [m] is even.  First, [0] is even, and
    [ev_0] is evidence for this.  Second, if [m = S (S n)] for some
    [n] and we can give evidence [e] that [n] is even, then [m] is
    also even, and [ev_SS n e] is the evidence. *)


(** **** Exercise: 1 star (double_even) *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  induction n as [|n'].
  simpl.
  apply ev_0.
  simpl.
  apply ev_SS.
  apply IHn'.
Qed.


(** *** Discussion: Computational vs. Inductive Definitions *)

(** We have seen that the proposition "[n] is even" can be
    phrased in two different ways -- indirectly, via a boolean testing
    function [evenb], or directly, by inductively describing what
    constitutes evidence for evenness.  These two ways of defining
    evenness are about equally easy to state and work with.  Which we
    choose is basically a question of taste.

    However, for many other properties of interest, the direct
    inductive definition is preferable, since writing a testing
    function may be awkward or even impossible.  

    One such property is [beautiful].  This is a perfectly sensible
    definition of a set of numbers, but we cannot translate its
    definition directly into a Coq Fixpoint (or into a recursive
    function in any other common programming language).  We might be
    able to find a clever way of testing this property using a
    [Fixpoint] (indeed, it is not too hard to find one in this case),
    but in general this could require arbitrarily deep thinking.  In
    fact, if the property we are interested in is uncomputable, then
    we cannot define it as a [Fixpoint] no matter how hard we try,
    because Coq requires that all [Fixpoint]s correspond to
    terminating computations.

    On the other hand, writing an inductive definition of what it
    means to give evidence for the property [beautiful] is
    straightforward. *)



(** **** Exercise: 1 star (ev__even) *)
(** Here is a proof that the inductive definition of evenness implies
    the computational one. *)

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [|n' E'].
  Case "E = ev_0". 
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".
    unfold even. apply IHE'.  
Qed.

Theorem ev__even' : forall n,
  ev n -> even n.
Proof.
  intros n E.
  induction n as [|n'].
  reflexivity.
  unfold even.
  unfold even in IHn'.
  inversion E.
  
  Abort.


  
(** Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)

(** induction on [n] will derive following situation
  n' : nat
  E : ev (S n')
  IHn' : ev n' -> even n'
  ============================
   even (S n')
as E holds, ev n' cannot be true. IHn' becomes meaningless
**)

(** The induction principle for inductively defined propositions does
    not follow quite the same form as that of inductively defined
    sets.  For now, you can take the intuitive view that induction on
    evidence [ev n] is similar to induction on [n], but restricts our
    attention to only those numbers for which evidence [ev n] could be
    generated.  We'll look at the induction principle of [ev] in more
    depth below, to explain what's really going on. *)

(** **** Exercise: 1 star (l_fails) *)
(** The following proof attempt will not succeed.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
   Intuitively, we expect the proof to fail because not every
   number is even. However, what exactly causes the proof to fail?

*)

Theorem l : forall n,
              ev n.
Proof.
  intros n. induction n.
  Case "O". simpl. apply ev_0.
  Case "S".

Abort.
(**
  Case := "S" : String.string
  n : nat
  IHn : ev n
  ============================
   ev (S n)

When ev n holds, ev (S n) cannot hold true, considering all possible constructors.
**)



(** **** Exercise: 2 stars (ev_sum) *)
(** Here's another exercise requiring induction. *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
  intros n m e1 e2.
  induction e1 as [|x y].
  simpl. apply e2.
  simpl. apply ev_SS. apply IHy.
Qed.


(* ##################################################### *)
(** * Inductively Defined Propositions *)

(**  As a running example, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)

(** Informally, a number is [beautiful] if it is [0], [3], [5], or the
    sum of two [beautiful] numbers.  

    More pedantically, we can define [beautiful] numbers by giving four
    rules:

       - Rule [b_0]: The number [0] is [beautiful].
       - Rule [b_3]: The number [3] is [beautiful]. 
       - Rule [b_5]: The number [5] is [beautiful]. 
       - Rule [b_sum]: If [n] and [m] are both [beautiful], then so is
         their sum. *)
(** ** Inference Rules *)
(** We will see many definitions like this one during the rest
    of the course, and for purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**
                              -----------                               (b_0)
                              beautiful 0
                              
                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5    

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)   
*)

(** *** *)
(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both [beautiful] numbers, then it follows that [n+m] is
    [beautiful] too.  If a rule has no premises above the line, then
    its conclusion holds unconditionally.

    These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_: *)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   
*)
(** *** *)
(** 
    Of course, there are other ways of using these rules to argue that
    [8] is [beautiful], for instance:
         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8   
*)

(** **** Exercise: 1 star (varieties_of_beauty) *)
(** How many different ways are there to show that [8] is [beautiful]? *)

(**
infinite.
all the beautiful numbers should be form of
0*x + 3*y + 5*z.
y = 1, z = 1 is fixed, but x can be arbitrary number, and for such (x,y,z), we can make at least one such formation.
**)

(** *** *)
(** In Coq, we can express the definition of [beautiful] as
    follows: *)

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).


(** The first line declares that [beautiful] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (That is, for each number [n], the claim that "[n] is
    [beautiful]" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.  Each of the remaining lines
    embodies one of the rules for [beautiful] numbers.
*)
(** *** *)
(** 
    The rules introduced this way have the same status as proven 
    theorems; that is, they are true axiomatically. 
    So we can use Coq's [apply] tactic with the rule names to prove 
    that particular numbers are [beautiful].  *)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* This simply follows from the rule [b_3]. *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
  (**
  apply (b_sum 5 3).
  apply (b_sum 5 0).
  apply (b_sum 5 0).
  apply b_5.
  apply b_0.
  apply b_0.
  apply b_3.
  **)
   (* First we use the rule [b_sum], telling Coq how to
      instantiate [n] and [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* To solve the subgoals generated by [b_sum], we must provide
      evidence of [beautiful 3] and [beautiful 5]. Fortunately we
      have rules for both. *)
   apply b_3.
   apply b_5.
Qed.

(** *** *)
(** As you would expect, we can also prove theorems that have
hypotheses about [beautiful]. *)

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.

(** **** Exercise: 2 stars (b_times2) *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
  intros n H.
  replace (2*n) with (n+n).
  apply (b_sum n n).
  apply H.
  apply H.
  simpl.
  rewrite plus_0_r.
  reflexivity.
Qed.

(** **** Exercise: 3 stars (b_timesm) *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  intros n m H.
  induction m as [|m'].
  simpl. apply b_0.
  simpl. apply (b_sum n (m' * n)). apply H. apply IHm'.
Qed.


(* ####################################################### *)
(** ** Induction Over Evidence *)

(** Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)

(** The fact that we introduced [beautiful] with an [Inductive]
    declaration tells Coq not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    four constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [beautiful n], then we know that [E] must have one of four shapes:

      - [E] is [b_0] (and [n] is [O]),
      - [E] is [b_3] (and [n] is [3]), 
      - [E] is [b_5] (and [n] is [5]), or 
      - [E] is [b_sum n1 n2 E1 E2] (and [n] is [n1+n2], where [E1] is
        evidence that [n1] is beautiful and [E2] is evidence that [n2]
        is beautiful). *)

(** *** *)    
(** This permits us to _analyze_ any hypothesis of the form [beautiful
    n] to see how it was constructed, using the tactics we already
    know.  In particular, we can use the [induction] tactic that we
    have already seen for reasoning about inductively defined _data_
    to reason about inductively defined _evidence_.

    To illustrate this, let's define another property of numbers: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercise: 1 star (gorgeous_tree) *)
(** Write out the definition of [gorgeous] numbers using inference rule
    notation.


         ------------------------------- (g_0)
                   gorgeous 0


                    gorgeous n
         ------------------------------- (g_plus3)
                   gorgeous n+3


                    gorgeous n
         ------------------------------- (g_plus5)
                   gorgeous n+5
*)


(** **** Exercise: 1 star (gorgeous_plus13) *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
  intros n H.
  apply g_plus5.
  apply g_plus5.
  apply g_plus3.
  apply H.
Qed.


(** *** *)
(** It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
   Case "g_0".
       apply b_0.
   Case "g_plus3". 
       apply b_sum. apply b_3.
       apply IHgorgeous.
   Case "g_plus5".
       apply b_sum. apply b_5. apply IHgorgeous. 
Qed.

(** Notice that the argument proceeds by induction on the _evidence_ [H]! *) 

(** Let's see what happens if we try to prove this by induction on [n]
   instead of induction on the evidence [H]. *)

Theorem gorgeous__beautiful_FAILED : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   Case "n = 0". apply b_0.
   Case "n = S n'". (* We are stuck! *)
Abort.

(** The problem here is that doing induction on [n] doesn't yield a
    useful induction hypothesis. Knowing how the property we are
    interested in behaves on the predecessor of [n] doesn't help us
    prove that it holds for [n]. Instead, we would like to be able to
    have induction hypotheses that mention other numbers, such as [n -
    3] and [n - 5]. This is given precisely by the shape of the
    constructors for [gorgeous]. *)




(** **** Exercise: 2 stars (gorgeous_sum) *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m p1 p2.
  induction p1 as [|n'|n'].
  rewrite plus_comm.
  rewrite plus_0_r.
  apply p2.
  rewrite <- plus_assoc.
  apply g_plus3.
  apply IHp1.
  rewrite <- plus_assoc.
  apply g_plus5.
  apply IHp1.
Qed.

(**
0 3 5 6 (8 9 10) ...
**)

(** **** Exercise: 3 stars, advanced (beautiful__gorgeous) *)

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros n p1.
  induction p1 as [|n'|n'|x y p2 p3 p4 p5].
  apply g_0.
  apply g_plus3.
  apply g_0.
  apply g_plus5.
  apply g_0.
  apply gorgeous_sum.
  apply p3.
  apply p5.
Qed.

(** **** Exercise: 3 stars, optional (g_times2) *)
(** Prove the [g_times2] theorem below without using [gorgeous__beautiful].
    You might find the following helper lemma useful. *)

Lemma helper_g_times2 : forall x y z, x + (z + y)= z + x + y.
Proof.
  intros x y z.
  rewrite -> plus_assoc.
  rewrite -> (plus_comm x z).
  reflexivity.
Qed.

Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl. 
   induction H.
   simpl.
   apply g_0.
   rewrite plus_0_r in IHgorgeous.
   rewrite plus_0_r.
   rewrite helper_g_times2.
   rewrite plus_assoc.
   simpl.
   apply g_plus3.
   apply g_plus3.
   apply IHgorgeous.

   rewrite plus_0_r in IHgorgeous.
   rewrite plus_0_r.
   rewrite helper_g_times2.
   simpl.
   apply g_plus5.
   apply g_plus5.
   apply IHgorgeous.
Qed.




(* ####################################################### *)
(** ** [Inversion] on Evidence *)

(** Another situation where we want to analyze evidence for evenness
    is when proving that, if [n] is even, then [pred (pred n)] is
    too.  In this case, we don't need to do an inductive proof.  The
    right tactic turns out to be [inversion].  *)

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercise: 1 star, optional (ev_minus2_n) *)
(** What happens if we try to use [destruct] on [n] instead of [inversion] on [E]? *)

Theorem ev_minus2': forall n,
  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  destruct E as [| n' E'].
  simpl. apply ev_0.
  simpl. apply E'.
Qed.

(** it works **)


(** *** *)
(** Another example, in which [inversion] helps narrow down to
the relevant cases. *)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  inversion E as [| n' E']. 
  apply E'. Qed.

(** ** [inversion] revisited *)

(** These uses of [inversion] may seem a bit mysterious at first.
    Until now, we've only used [inversion] on equality
    propositions, to utilize injectivity of constructors or to
    discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence
    for inductively defined propositions.

    (You might also expect that [destruct] would be a more suitable
    tactic to use here. Indeed, it is possible to use [destruct], but 
    it often throws away useful information, and the [eqn:] qualifier
    doesn't help much in this case.)    

    Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)


(** **** Exercise: 1 star (inversion_practice) *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n p1.
  inversion p1 as [n'|n' p2].
  rewrite <- H0 in p1.
  rewrite <- H0 in p2.
  inversion p2 as [|].
  rewrite <- H in H0.
  inversion H0.
  rewrite H0 in H1.
  inversion H1.
  rewrite <- H3.
  apply H.
  (* SSev__even *)
Qed.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  intros p1.
  inversion p1 as [DONTAPPEAR|n p2].
  inversion p2 as [DONTAPPEAR|n' p3].
  inversion p3.
Qed.

(** **** Exercise: 3 stars, advanced (ev_ev__ev) *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m p1 p2.
  generalize dependent m.
  induction p2 as [p2_A|n' p2_B].
  intros m p1. simpl in p1. apply p1.
  intros m p1. apply IHp2_B. simpl in p1. apply SSev__even in p1. apply p1.
Qed.

(** **** Exercise: 3 stars, optional (ev_plus_plus) *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p prop1 prop2.

  assert(prop3 : ev(n + m + (n + p))).
  apply (ev_sum (n+m) (n+p)).
  apply prop1. apply prop2.
  assert(prop4 : ev(n+n)).
  replace (n+n) with (double n).
  apply double_even.
  apply double_plus.
  apply (ev_ev__ev (n+n) (m+p)).
  replace (n+m+(n+p)) with (n+n+(m+p)) in prop3.
  apply prop3.
  rewrite (plus_comm n m).
  rewrite (helper_g_times2).
  rewrite plus_assoc.
  rewrite plus_assoc.
  reflexivity.
  apply prop4.
Qed.
  

(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars (palindromes) *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
    c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove that 
       forall l, pal (l ++ rev l).
    - Prove that 
       forall l, pal l -> l = rev l.
*)

Inductive pal {X : Type} : list X -> Prop :=
  | pal_0 : pal []
  | pal_1 : forall v:X, pal [v]
  | pal_add  : forall v:X, forall l:list X,
                 pal l -> pal ([v] ++ l ++ [v]).
(*
                 pal l -> (pal (snoc (cons v l) v)).
*)

Lemma app_nil_end : forall (X : Type) (l : list X),
  l ++ [] = l.
Proof.
  induction l as [|h t].
  reflexivity.
  simpl.
  rewrite IHt.
  reflexivity.
Qed.

Lemma app_snoc : forall (X : Type) (l : list X) (v : X),
  snoc l v = l ++ [v].
Proof.
  induction l as [|h t].
  reflexivity.
  simpl.
  intros v.
  rewrite IHt.
  reflexivity.
Qed.

Lemma app_assoc : forall (X : Type) (l1 l2 l3 : list X),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  induction l1 as [|h t].
  simpl. reflexivity.
  simpl. intros l2 l3. rewrite IHt. reflexivity.
Qed.

Lemma rev_distr : forall (X : Type) (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1 as [|h t].
  intros l2.
  simpl.
  rewrite app_nil_end.
  reflexivity.
  intros l2.
  simpl.
  rewrite IHt.
  rewrite app_snoc.
  rewrite app_snoc.
  apply app_assoc.
Qed.
  
Theorem pal_thm1 : forall (X : Type) (l : list X),
  pal (l ++ rev l).
Proof.
  intros X l.
  induction l as [|h t].
  simpl. apply pal_0.
  simpl.

  assert(p1 : pal ([h] ++ (t ++ rev t) ++ [h])).
  apply (pal_add h (t ++ rev t)).
  apply IHt.
  replace (h :: t ++ snoc (rev t) h) with ([h] ++ (t ++ rev t) ++ [h]).
  apply p1.
  simpl.
  replace ((t ++ rev t) ++ [h]) with (t ++ snoc (rev t) h).
  reflexivity.
  rewrite app_snoc.
  rewrite app_assoc.
  reflexivity.
Qed.
  
Theorem pal_thm2 : forall (X : Type) (l : list X),
  pal l -> l = rev l.
Proof.
  intros X.
  intros l p1.
  induction p1 as [|v|v l].
  reflexivity.
  reflexivity.
(*  symmetry in IHp1. *)
  rewrite rev_distr.
  rewrite rev_distr.
  simpl.
  rewrite <- IHp1.
  reflexivity.
Qed.


(** **** Exercise: 5 stars, optional (palindrome_converse) *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)


(**
Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.
**)

Fixpoint head_trim {X : Type} (l : list X) :=
  match l with
  | [] => []
  | h :: t => t
  end.

Fixpoint tail_trim {X : Type} (l : list X) :=
  match l with
  | [] => []
  | h :: t => rev (head_trim (rev l))
  end.

Fixpoint trim {X : Type} (l : list X) :=
  head_trim (tail_trim l).

Fixpoint head_elem {X : Type} (l : list X) :=
  match l with
  | [] => []
  | h :: t => [h]
  end.

Fixpoint tail_elem {X : Type} (l : list X) :=
  match l with
  | [] => []
  | h :: t => head_elem (rev l)
  end.

Lemma cons_sep : forall {X : Type} {l : list X} {v : X},
  v :: l = [v] ++ l.
Proof.
  induction l as [|h t].
  reflexivity.
  simpl. rewrite IHt. reflexivity.
Qed.

Lemma snoc_sep : forall {X : Type} {l : list X} {v : X},
  snoc l v = l ++ [v].
Proof.
  induction l as [|h t].
  reflexivity.
  simpl. intros v. rewrite (IHt v). reflexivity.
Qed.

Lemma rev_cons : forall {X : Type} {l : list X} {v : X},
  rev (v :: l) = (rev l) ++ [v].
Proof.
  induction l as [|h t].
  reflexivity.
  intros v.
  rewrite IHt.
  rewrite cons_sep.
  rewrite cons_sep.
  rewrite app_nil_end.
  rewrite rev_distr.
  rewrite IHt.
  reflexivity.
Qed.

Lemma rev_not_nil : forall {X : Type} {t : list X} {h : X},
  rev (h :: t) = [] -> False.
Proof.
  intros X t h p.
  inversion p.
  destruct (rev t) as [|x y].
  inversion H0.
  inversion H0.
Qed.

Lemma cons_refl : forall {X : Type} {l l' : list X} {v v' : X},
  v :: l = v' :: l' -> v = v' /\ l = l'.
Proof.
  intros X l l' v v' p.
  inversion p.
  split.
  reflexivity. reflexivity.
Qed.

Lemma app_tail_elem : forall {X : Type} {l : list X} {v : X},
  tail_elem (l ++ [v]) = [v].
Proof.
  intros X l v.
  (**
  destruct (l ++ [v]) as [|h t] eqn : e.
  destruct l as [|lh lt]. inversion e. inversion e.
  simpl.
**)
  (**
  rewrite <- snoc_sep in e.
**)
  induction l as [|h t].
  reflexivity.
  rewrite <- IHt.
  simpl.
  destruct t as [|h' t']. reflexivity.
  simpl.
Abort.
(**
  reflexivity.
  rewrite <- snoc_sep.


  rewrite <- (rev_involutive X l).
  rewrite <- rev_cons.
  destruct (v :: rev l) as [|h t] eqn : p1.
  inversion p1.
  simpl.
  apply cons_refl in p1.
  inversion p1.
  rewrite <- H0.
  rewrite rev_involutive.


  
  destruct (rev (h :: t)) as [|h' t'] eqn : p2.
  apply rev_not_nil in p2.
  inversion p2.
  simpl.
  
  simpl.
  
  unfold tail_elem.
  
  simpl.
  rewrite <- snoc_sep.

  destruct l as [|h t].
  reflexivity.
  rewrite <- app_snoc.
  simpl.
**)
    
Lemma app_tail_elem : forall {X : Type} {l1 l2 : list X} {v : X},
  tail_elem (l1 ++ (v :: l2)) = (tail_elem (v :: l2)).
Proof.
  intros X l1 l2 v.
  induction l2 as [|h t].
  simpl.
  Abort.

  (**
Lemma list_decomp : forall {X : Type} {l : list X},
  (ble_nat 2 (length l)) = true ->
  (head_elem l) ++ (trim l) ++ (tail_elem l)
  = l.
Proof.
  intros X l p1.
  destruct l as [|v0 l_].
  inversion p1.
  destruct l_ as [|v1 l__].
  inversion p1.
  simpl in p1.
  induction l__ as [|x y].
  reflexivity.
  rewrite <- (rev_involutive X y).
  (** l = x + y = x + rev z + m **)
  destruct (rev y) as [|m z] eqn : e1.
  reflexivity.
Qed.
**)

Lemma rev_refl : forall {X : Type} {l1 l2 : list X},
  l1 = l2 -> rev l1 = rev l2.
Proof.
  intros X l1 l2 p1.
  rewrite p1.
  reflexivity.
Qed.

Fixpoint get_mod (n : nat) :=
  match n with
  | 0 => 0
  | S n' => match (get_mod n') with
            | 0 => 1
            | 1 => 0
            | S n'' => 42
            end
  end.

Eval compute in get_mod 2.
Eval compute in get_mod 3.
Eval compute in get_mod 4.
Eval compute in get_mod 5.

Theorem mod_0_even : forall n : nat,
  get_mod n = 0 -> ev n.
Proof.
  intros n.
  induction n as [|n'].
  intros t. apply ev_0.
  intros t.
Abort.


Inductive odd : nat -> Prop :=
    odd_1 : odd 1 | odd_SS : forall n : nat, odd n -> odd (S (S n)).

Theorem oddb_to_odd : forall n : nat,
  evenb n = false -> odd n.
Proof.
  intros n P.
  
  induction n as [|n'].
Abort.

Theorem ev_or_odd : forall n,
  ev n \/ odd n.
Admitted.

Theorem step_induction (p : nat -> Prop) :
  (forall n : nat, (p n) -> (p (n+2))) -> (p 0) -> (p 1)
-> forall n : nat, p n.
Proof.
  intros h1 h2 h3 n.
  assert(G : forall e, ev e -> p e).
  intros e h4.
  induction h4 as [|e'].
  apply h2.
  replace (S (S e')) with (e' + 2).
  apply h1.
  apply IHh4.
  rewrite plus_comm.
  reflexivity.
  assert(G' : forall o : nat, (odd o) -> p o).
  intros o h4.
  induction h4 as [|o'].
  apply h3.
  replace (S (S o')) with (o' + 2).
  apply h1.
  apply IHh4.
  rewrite plus_comm.
  reflexivity.
  assert(H : ev n \/ odd n).
  apply ev_or_odd.
  inversion H.
  apply G. apply H0.
  apply G'. apply H0.
Qed.

(**
Theorem list_length_induction {X : Type} (p : list X -> Prop) :
  forall n : nat,
**)

Theorem list_step_induction {X : Type} (p : list X -> Prop) :
  p [] -> (forall v : X, p [v]) ->
  (forall (l : list X) (v0 v1 : X),
     (p l) -> (p ([v0] ++ l ++ [v1])))
    -> (forall l : list X, p l).
Admitted.


Theorem pal_thm3 : forall {X : Type} {l : list X},
  l = rev l -> pal l.
Proof.
  intros X l.
  intros p1.
  destruct l as [|a b] eqn : e1.
  apply pal_0.
  destruct (rev l) as [|a' b'] eqn : e2.
  rewrite e1 in e2.
  apply rev_not_nil in e2.
  inversion e2.

  rewrite <- e1 in p1.
  rewrite e2 in p1.
  rewrite e1 in p1.
  apply cons_refl in p1.
  inversion p1.

  rewrite <- e1.

  destruct (rev b) as [|a'' mid] eqn : e3.
  assert(e4 : b = []).
  symmetry. rewrite <- rev_involutive. rewrite e3. reflexivity.
  rewrite e4 in e1. rewrite e1. apply pal_1.
  assert(main : (rev l) = a :: b).
  rewrite H. rewrite H0. apply e2.
  apply rev_refl in main.
  rewrite rev_involutive in main.
  rewrite rev_cons in main.
  rewrite e1 in main.
  rewrite e3 in main.
  rewrite cons_sep in main.
  symmetry in main.
  rewrite cons_sep in main.
  rewrite app_assoc in main.
  rewrite <- cons_sep  in main.
  rewrite <- cons_sep  in main.
  apply cons_refl in main.
  assert(target : l = [a] ++ mid ++ [a]).
  rewrite e1.
  inversion main as [e4 e5].
  rewrite <- e5.
  rewrite cons_sep.
  reflexivity.
  rewrite target.
  apply pal_add.
Abort.

Definition pal_prop {X : Type} (l : list X) :=
  l = rev l -> pal l.

Lemma app_end_refl : forall {X : Type} {l1 l2 : list X} {v : X},
  l1 ++ [v] = l2 ++ [v] -> l1 = l2.
Proof.
  intros X.
  induction l1 as [|h t].
  intros l2 v p1.
  inversion p1.
  destruct l2 as [|h' t']. reflexivity. inversion H0. apply rev_refl in H2. rewrite rev_distr in H2. simpl in H2. inversion H2.
  intros l2 v p1. rewrite cons_sep in p1.
  destruct l2 as [|h2 t2].
  inversion p1.
  apply rev_refl in H1.
  rewrite rev_distr in H1.
  simpl in H1.
  inversion H1.


  rewrite app_assoc in p1.
  symmetry in p1.
  rewrite cons_sep in p1.
  rewrite app_assoc in p1.
  apply cons_refl in p1.
  inversion p1 as [p2 p3].
  symmetry in p3.
  apply IHt in p3.
  rewrite p2.
  rewrite p3.
  reflexivity.
Qed.
  
Theorem pal_thm3 : forall {X : Type} {l : list X},
  (pal_prop l).
Proof.
  Print pal_prop.
  intros X.
  apply (list_step_induction pal_prop).
  intros tmp. apply pal_0.
  intros tmp tmp2. apply pal_1.


  unfold pal_prop.
  intros l v0 v1 p1 p2.
  rewrite rev_distr in p2.
  rewrite rev_distr in p2.
  simpl in p2.
  rewrite cons_sep in p2.
  symmetry in p2.
  rewrite cons_sep in p2.
  apply cons_refl in p2.
  inversion p2 as [p3 p4].
  rewrite p3.
  apply pal_add.
  apply p1.
  rewrite p3 in p4.
  apply app_end_refl in p4.
  rewrite p4.
  reflexivity.
Qed.  

(** **** Exercise: 4 stars, advanced (subsequence) *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1,2,3]
    is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
    but it is _not_ a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove that subsequence is reflexive, that is, any list is a
      subsequence of itself.  

    - Prove that for any lists [l1], [l2], and [l3], if [l1] is a
      subsequence of [l2], then [l1] is also a subsequence of [l2 ++
      l3].

    - (Optional, harder) Prove that subsequence is transitive -- that
      is, if [l1] is a subsequence of [l2] and [l2] is a subsequence
      of [l3], then [l1] is a subsequence of [l3].  Hint: choose your
      induction carefully!
*)

Inductive subseq : list nat -> list nat -> Prop :=
  sub_0 : forall l : list nat, subseq [] l
| sub_add_both : forall l1 l2 : list nat, forall v : nat,
              subseq l1 l2 -> subseq (v :: l1) (v :: l2)            | sub_add_one : forall l1 l2 : list nat, forall v : nat,
              subseq l1 l2 -> subseq l1 (v :: l2).


Theorem subseq_refl : forall (l : list nat),
                        subseq l l.
Proof.
  induction l as [|h t].
  apply sub_0.
  apply sub_add_both.
  apply IHt.
Qed.

Lemma subseq_cons : forall (l1 l2 : list nat) (v : nat),
                       subseq (v :: l1) l2 -> subseq l1 l2.
Proof.
  intros.
  (* TODO *)
  (* induction H. *)
  (* v :: l1 = [] ?????????????? *)
  (**
  l1 : list nat
  l2 : list nat
  v : nat
  H : subseq (v :: l1) l2
  ============================
   subseq l1 l2

  l1 : list nat
  v : nat
  l : list nat
  ============================
   subseq l1 l
**)
  inversion H as [A|B|C].
  apply sub_add_one with (v:=v) in H3.
  apply H3.
  rewrite <- H2 in H.
  inversion H0.
  apply sub_add_one with (v:=v) in H6.
  apply sub_add_one with (v:=v0) in H6.
  apply H6.
  inversion H.
Abort.

(*
Proof.
  intros l1 l2 v p1.
  induction l2 as [|h t].
  inversion p1.
  assert (G : subseq l1 t).
  apply IHt.
  inversion p1.
  (*
  inversion p1.
  apply (sub_add_one l1 l3 v) in H2.
  apply H2.
*)
  
  induction l1 as [|h t].
  intros l2 v p1.
  apply sub_0.

  intros l2 v p1.

  
  intros l1 l2 v p1.
  inversion p1.
  rewrite <- H0 in p1.
  inversion p1.
  apply (sub_add_one l1 l3 v) in H4.
  apply H4.
  apply (sub_add_one l1 l3 v) in H2.
  apply H2.
  
  rewrite <- H1 in p1.
  inversion p1.
Qed.
*)
(*
  l1 : list nat
  l2 : list nat
  v : nat
  p1 : subseq (v :: l1) l2
  ============================
   subseq l1 l2
*)
   
Theorem subseq_app_after : forall (l1 l2 l3 : list nat),
                       subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 p.
  induction p.
  (** inversion ?????????????????? **)
  apply sub_0.
  apply sub_add_both with (v:=v) in IHp.
  apply IHp.
  apply sub_add_one with (v:=v) in IHp.
  apply IHp.
Qed.

Theorem subseq_app_before : forall (l1 l2 l3 : list nat),
                       subseq (l3 ++ l1) l2 -> subseq l1 l2.
Proof.
  intros l1 l2 l3 p1.
  induction p1 as [WRYYY| |].
Abort.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
                         subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
  intros.
  generalize dependent l1.
  induction H0.
  intros. inversion H. apply sub_0.
  intros. inversion H. apply sub_0. apply sub_add_both. apply IHsubseq. apply H3.
  apply sub_add_one. apply IHsubseq. apply H3.
  intros. apply sub_add_one. apply IHsubseq. apply H.
Qed.
(**  
  intros.
  generalize dependent l3.
  induction H.
  intros.
  apply sub_0.
  intros.
  


    
  intros l1 l2 l3 p1.
  generalize dependent l3.
  induction p1.
  intros l3 p1.
  apply sub_0.
  intros l3 p2.
**)  

Theorem subseq_trans' : forall (l1 l2 l3 : list nat),
                         subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros.
  generalize dependent l1.
  induction H0.
  intros. inversion H. apply sub_0.
  intros. inversion H. apply sub_0. apply sub_add_both. apply IHsubseq. apply H3.
  apply sub_add_one. apply IHsubseq. apply H3.
  intros. inversion H. apply sub_0. apply IHsubseq in H. rewrite H2. apply sub_add_one. apply H. apply IHsubseq in H. apply sub_add_one. apply H.
Qed.
  
(** **** Exercise: 2 stars, optional (R_provability) *)
(** Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [1,0]] (O)
    - [R 1 [1,2,1,0]] (O)
    - [R 6 [3,2,1,0]] (X)
*)


    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Theorem R1 : R 2 (1 :: 0 :: nil).
      Proof.
      apply c2. apply c2. apply c1.
      Qed.
    Theorem R2 : R 1 (1 :: 2 :: 1 :: 0 :: nil).
      Proof.
      apply c3. apply c2. apply c3. apply c3. apply c2. apply c2. apply c2. apply c1.
      Qed.

(* ####################################################### *)
(** * Relations *)

(** A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeModule.  


(** One useful example is the "less than or equal to"
    relation on numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in chapter [Prop].  We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) -> 2+2=5].) *)

(** *** *)
(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof. 
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** *** *)
(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars (total_relation) *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop :=
  | total : forall n m : nat, (total_relation n m).

Fact total_relation1 : (total_relation 5 7).
Proof. apply total. Qed.

(** **** Exercise: 2 stars (empty_relation) *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation : nat -> Prop := .

Fact empty_relation1 : empty_relation 42 -> 2 + 2 = 5.
Proof. intros. induction H. Qed.

(** **** Exercise: 2 stars, optional (le_exercises) *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  generalize dependent m.
  induction H0.
  intros. apply H.
  intros. apply IHle in H. apply le_S in H. apply H.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n as [|n'].
  apply le_n.
  apply le_S in IHn'.
  apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.
  generalize dependent n.
  induction m as [|m'].
  intros. inversion H. apply le_n.
  intros. inversion H. apply le_n. apply IHm' in H1. apply le_S in H1. apply H1.
Qed.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros.
  generalize dependent n.
  induction m as [|m'].
  intros. inversion H. apply le_n. inversion H1.
  intros. inversion H. apply le_n. apply IHm' in H1. apply le_S. apply H1.
Qed.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intro.
  induction a as [|a'].
  simpl. intros. apply O_le_n.
  intros. apply (n_le_m__Sn_le_Sm a' (a'+b)) in IHa'. simpl. apply IHa'.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
  unfold lt.
  intros.
  assert (G : forall x y : nat, S x <= S (x + y)). intros. rewrite plus_comm. rewrite plus_n_Sm. rewrite plus_comm. apply le_plus_l.
  apply conj.
  apply (le_trans (S n1) (S (n1 + n2)) m). apply G. apply H.
  apply (le_trans (S n2) (S (n1 + n2)) m). rewrite plus_comm. apply G. apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros.
  assert(G : m <= S m).
  replace (S m) with (m + 1).
  apply (le_plus_l m 1).
  rewrite plus_comm. reflexivity.
  apply (le_trans (S n) m (S m)).
  apply H. apply G.
Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  intros.
  generalize dependent n.
  induction m as [|m'].
  intros. destruct n as [|n']. apply le_n. inversion H.
  intros. destruct n as [|n']. apply O_le_n. simpl in H. apply IHm' in H. apply n_le_m__Sn_le_Sm in H. apply H.
Qed.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  intro.
  induction n as [|n'].
  intros. induction H. reflexivity. reflexivity.
  intros. inversion H. simpl. apply IHn'. apply le_n.
  simpl. apply IHn'. rewrite <- H1 in H. apply Sn_le_Sm__n_le_m in H. apply H.
Qed.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
  intros.
  apply ble_nat_true in H.
  apply ble_nat_true in H0.
  assert (G : n <= o).
  apply (le_trans n m o).
  apply H. apply H0.
  apply le_ble_nat in G. apply G.
Qed.

(** **** Exercise: 2 stars, optional (ble_nat_false) *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  unfold not.
  intros n. induction n as [|n'].
  intros. inversion H.
  intros. destruct m as [|m']. inversion H0.
  simpl in H. apply IHn' with (m:=m'). apply H. apply Sn_le_Sm__n_le_m in H0. apply H0.
Qed.


(** **** Exercise: 3 stars (R_provability) *)
Module R.
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
  
    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

observation : (m+n) = o always. (observation behind this : c5 -> m and n's location becomes not important)
second one is impossible.
first one is possible only using c2, c3, c1 -> possible in all cases.
*)

Fact R_ex1 : R 1 1 2.
Proof. apply c2. apply c3. apply c1. Qed.

(** **** Exercise: 3 stars, optional (R_fact) *)  
(** Relation [R] actually encodes a familiar function.  State and prove two
    theorems that formally connects the relation and the function. 
    That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)

Theorem R_to_my_thm : forall m n o : nat, R m n o -> m + n = o.
Proof.
  intros. induction H. reflexivity. rewrite <- IHR. reflexivity. rewrite <- IHR. rewrite plus_n_Sm. reflexivity. rewrite <- plus_n_Sm in IHR. inversion IHR. reflexivity. rewrite plus_comm. apply IHR.
  (*
  induction m as [|m'].
  intros. induction H. reflexivity. simpl. rewrite IHR. reflexivity.
  rewrite <- plus_n_Sm. rewrite IHR. reflexivity.
  simpl in IHR. rewrite <- plus_n_Sm in IHR. inversion IHR. reflexivity.
  rewrite plus_comm. apply IHR.
  intros.
*)
Qed.

Lemma R_0_n_n : forall n, R 0 n n.
Proof.
  induction n as [|n'].
  apply c1.
  apply c3.
  apply IHn'.
Qed.


Theorem my_thm_to_R : forall m n o, m + n = o -> R m n o.
Proof.
  intros. induction H.
  induction m as [|m']. simpl. apply R_0_n_n. apply c2 in IHm'. rewrite plus_comm in IHm'. rewrite plus_n_Sm in IHm'. rewrite plus_comm in IHm'. apply IHm'.
Qed.

End R.


(* ##################################################### *)
(** * Programming with Propositions Revisited *)

(** As we have seen, a _proposition_ is a statement expressing a factual claim,
    like "two plus two equals four."  In Coq, propositions are written
    as expressions of type [Prop]. . *)

Check (2 + 2 = 4).
(* ===> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ===> ble_nat 3 2 = false : Prop *)

Check (beautiful 8).
(* ===> beautiful 8 : Prop *)

(** *** *)
(** Both provable and unprovable claims are perfectly good
    propositions.  Simply _being_ a proposition is one thing; being
    _provable_ is something else! *)

Check (2 + 2 = 5).
(* ===> 2 + 2 = 5 : Prop *)

Check (beautiful 4).
(* ===> beautiful 4 : Prop *)

(** Both [2 + 2 = 4] and [2 + 2 = 5] are legal expressions
    of type [Prop]. *)

(** *** *)
(** We've mainly seen one place that propositions can appear in Coq: in
    [Theorem] (and [Lemma] and [Example]) declarations. *)

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But they can be used in many other ways.  For example, we have also seen that
    we can give a name to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. *)

Definition plus_fact : Prop  :=  2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true : 
  plus_fact.
Proof. reflexivity.  Qed.

(** *** *)
(** We've seen several ways of constructing propositions.  

       - We can define a new proposition primitively using [Inductive].

       - Given two expressions [e1] and [e2] of the same type, we can
         form the proposition [e1 = e2], which states that their
         values are equal.

       - We can combine propositions using implication and
         quantification. *)
(** *** *)
(** We have also seen _parameterized propositions_, such as [even] and
    [beautiful]. *)

Check (even 4).
(* ===> even 4 : Prop *)
Check (even 3).
(* ===> even 3 : Prop *)
Check even. 
(* ===> even : nat -> Prop *)

(** *** *)
(** The type of [even], i.e., [nat->Prop], can be pronounced in
    three equivalent ways: (1) "[even] is a _function_ from numbers to
    propositions," (2) "[even] is a _family_ of propositions, indexed
    by a number [n]," or (3) "[even] is a _property_ of numbers."  *)

(** Propositions -- including parameterized propositions -- are
    first-class citizens in Coq.  For example, we can define functions
    from numbers to propositions... *)

Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

(** ... and then partially apply them: *)

Definition teen : nat->Prop := between 13 19.

(** We can even pass propositions -- including parameterized
    propositions -- as arguments to functions: *)

Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

(** *** *)
(** Here are two more examples of passing parameterized propositions
    as arguments to a function.  

    The first function, [true_for_all_numbers], takes a proposition
    [P] as argument and builds the proposition that [P] is true for
    all natural numbers. *)

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

(** The second, [preserved_by_S], takes [P] and builds the proposition
    that, if [P] is true for some natural number [n'], then it is also
    true by the successor of [n'] -- i.e. that [P] is _preserved by
    successor_: *)

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

(** *** *)
(** Finally, we can put these ingredients together to define
a proposition stating that induction is valid for natural numbers: *)

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P -> 
    true_for_all_numbers P. 





(** **** Exercise: 3 stars (combine_odd_even) *)
(** Complete the definition of the [combine_odd_even] function
    below. It takes as arguments two properties of numbers [Podd] and
    [Peven]. As its result, it should return a new property [P] such
    that [P n] is equivalent to [Podd n] when [n] is odd, and
    equivalent to [Peven n] otherwise. *)

Definition combine_odd_even_inside (Podd Peven : nat -> Prop) (n : nat) : Prop :=
  if(evenb n) then Peven n else Podd n.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  combine_odd_even_inside Podd Peven.

(** To test your definition, see whether you can prove the following
    facts: *)

Lemma evenb_not_oddb : forall n : nat, forall b : bool,
                         evenb n = b -> oddb n = (negb b).
Proof. intros. unfold oddb. rewrite H. reflexivity. Qed.

Lemma oddb_not_evenb : forall n : nat, forall b : bool,
                         oddb n = b -> evenb n = (negb b).
Proof. intros. unfold oddb in H. rewrite <- H. rewrite negb_involutive. reflexivity. Qed.

Theorem combine_odd_even_intro : 
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  unfold combine_odd_even. unfold combine_odd_even_inside.
  intros. destruct (evenb n) as [t|f] eqn:e.
  apply H0. apply evenb_not_oddb in e. apply e.
  apply H. apply evenb_not_oddb in e. simpl in e. apply e.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  unfold combine_odd_even. unfold combine_odd_even_inside.
  intros.
  apply oddb_not_evenb in H0.
  rewrite H0 in H.
  simpl in H.
  apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  unfold combine_odd_even. unfold combine_odd_even_inside.
  intros.
  apply oddb_not_evenb in H0.
  rewrite H0 in H.
  simpl in H.
  apply H.
Qed.

(** [] *)

(* ##################################################### *)
(** One more quick digression, for adventurous souls: if we can define
    parameterized propositions using [Definition], then can we also
    define them using [Fixpoint]?  Of course we can!  However, this
    kind of "recursive parameterization" doesn't correspond to
    anything very familiar from everyday mathematics.  The following
    exercise gives a slightly contrived example. *)

(** **** Exercise: 4 stars, optional (true_upto_n__true_everywhere) *)
(** Define a recursive function
    [true_upto_n__true_everywhere] that makes
    [true_upto_n_example] work. *)


Fixpoint true_upto_n__true_everywhere (n : nat) (P : nat -> Prop) :=
  match n with
  | 0 => forall n, P n
  | S n' => P (S n') -> true_upto_n__true_everywhere n' P
  end.

Example true_upto_n_example :
    (true_upto_n__true_everywhere 3 (fun n => even n))
  = (even 3 -> even 2 -> even 1 -> forall m : nat, even m).
Proof. reflexivity.  Qed.

(** [] *)


(* $Date: 2014-06-05 07:22:21 -0400 (Thu, 05 Jun 2014) $ *)


