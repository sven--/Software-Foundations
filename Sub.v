(** * Sub: Subtyping *)

Require Export MoreStlc.

(* ###################################################### *)
(** * Concepts *)

(** We now turn to the study of _subtyping_, perhaps the most
    characteristic feature of the static type systems of recently
    designed programming languages and a key feature needed to support
    the object-oriented programming style. *)

(* ###################################################### *)
(** ** A Motivating Example *)

(** Suppose we are writing a program involving two record types
    defined as follows:
<<
    Person  = {name:String, age:Nat}
    Student = {name:String, age:Nat, gpa:Nat}
>>
*)

(** In the simply typed lamdba-calculus with records, the term
<<
    (\r:Person. (r.age)+1) {name="Pat",age=21,gpa=1}
>>
   is not typable: it involves an application of a function that wants
   a one-field record to an argument that actually provides two
   fields, while the [T_App] rule demands that the domain type of the
   function being applied must match the type of the argument
   precisely.  

   But this is silly: we're passing the function a _better_ argument
   than it needs!  The only thing the body of the function can
   possibly do with its record argument [r] is project the field [age]
   from it: nothing else is allowed by the type, and the presence or
   absence of an extra [gpa] field makes no difference at all.  So,
   intuitively, it seems that this function should be applicable to
   any record value that has at least an [age] field.

   Looking at the same thing from another point of view, a record with
   more fields is "at least as good in any context" as one with just a
   subset of these fields, in the sense that any value belonging to
   the longer record type can be used _safely_ in any context
   expecting the shorter record type.  If the context expects
   something with the shorter type but we actually give it something
   with the longer type, nothing bad will happen (formally, the
   program will not get stuck).

   The general principle at work here is called _subtyping_.  We say
   that "[S] is a subtype of [T]", informally written [S <: T], if a
   value of type [S] can safely be used in any context where a value
   of type [T] is expected.  The idea of subtyping applies not only to
   records, but to all of the type constructors in the language --
   functions, pairs, etc. *)

(** ** Subtyping and Object-Oriented Languages *)

(** Subtyping plays a fundamental role in many programming
    languages -- in particular, it is closely related to the notion of
    _subclassing_ in object-oriented languages.

    An _object_ in Java, C[#], etc. can be thought of as a record,
    some of whose fields are functions ("methods") and some of whose
    fields are data values ("fields" or "instance variables").
    Invoking a method [m] of an object [o] on some arguments [a1..an]
    consists of projecting out the [m] field of [o] and applying it to
    [a1..an].

    The type of an object can be given as either a _class_ or an
    _interface_.  Both of these provide a description of which methods
    and which data fields the object offers.

    Classes and interfaces are related by the _subclass_ and
    _subinterface_ relations.  An object belonging to a subclass (or
    subinterface) is required to provide all the methods and fields of
    one belonging to a superclass (or superinterface), plus possibly
    some more.

    The fact that an object from a subclass (or sub-interface) can be
    used in place of one from a superclass (or super-interface)
    provides a degree of flexibility that is is extremely handy for
    organizing complex libraries.  For example, a GUI toolkit like
    Java's Swing framework might define an abstract interface
    [Component] that collects together the common fields and methods
    of all objects having a graphical representation that can be
    displayed on the screen and that can interact with the user.
    Examples of such object would include the buttons, checkboxes, and
    scrollbars of a typical GUI.  A method that relies only on this
    common interface can now be applied to any of these objects.

    Of course, real object-oriented languages include many other
    features besides these.  For example, fields can be updated.
    Fields and methods can be declared [private].  Classes also give
    _code_ that is used when constructing objects and implementing
    their methods, and the code in subclasses cooperate with code in
    superclasses via _inheritance_.  Classes can have static methods
    and fields, initializers, etc., etc.

    To keep things simple here, we won't deal with any of these
    issues -- in fact, we won't even talk any more about objects or
    classes.  (There is a lot of discussion in _Types and Programming
    Languages_, if you are interested.)  Instead, we'll study the core
    concepts behind the subclass / subinterface relation in the
    simplified setting of the STLC. *)

(** *** *)
(** Of course, real OO languages have lots of other features...
       - mutable fields
       - [private] and other visibility modifiers
       - method inheritance
       - static components
       - etc., etc.

    We'll ignore all these and focus on core mechanisms. *)

(** ** The Subsumption Rule *)

(** Our goal for this chapter is to add subtyping to the simply typed
    lambda-calculus (with some of the basic extensions from [MoreStlc]).
    This involves two steps:

      - Defining a binary _subtype relation_ between types.

      - Enriching the typing relation to take subtyping into account.

    The second step is actually very simple.  We add just a single rule
    to the typing relation: the so-called _rule of subsumption_:
                         Gamma |- t : S     S <: T
                         -------------------------                      (T_Sub)
                               Gamma |- t : T
    This rule says, intuitively, that it is OK to "forget" some of
    what we know about a term. *)
(** For example, we may know that [t] is a record with two
    fields (e.g., [S = {x:A->A, y:B->B}]), but choose to forget about
    one of the fields ([T = {y:B->B}]) so that we can pass [t] to a
    function that requires just a single-field record. *)

(** ** The Subtype Relation *)

(** The first step -- the definition of the relation [S <: T] -- is
    where all the action is.  Let's look at each of the clauses of its
    definition.  *)

(** *** Structural Rules *)

(** To start off, we impose two "structural rules" that are
    independent of any particular type constructor: a rule of
    _transitivity_, which says intuitively that, if [S] is better than
    [U] and [U] is better than [T], then [S] is better than [T]...
                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T
    ... and a rule of _reflexivity_, since certainly any type [T] is 
    as good as itself:  
                                   ------                              (S_Refl)
                                   T <: T
*)

(** *** Products *)

(** Now we consider the individual type constructors, one by one,
    beginning with product types.  We consider one pair to be "better
    than" another if each of its components is.
                            S1 <: T1    S2 <: T2
                            --------------------                        (S_Prod)
                             S1 * S2 <: T1 * T2
*)

(** *** Arrows *)

(** Suppose we have two functions [f] and [g] with these types:
       f : C -> Student 
       g : (C->Person) -> D
    That is, [f] is a function that yields a record of type [Student],
    and [g] is a (higher-order) function that expects its (function)
    argument to yield a record of type [Person].  Also suppose, even
    though we haven't yet discussed subtyping for records, that
    [Student] is a subtype of [Person].  Then the application [g f] is
    safe even though their types do not match up precisely, because
    the only thing [g] can do with [f] is to apply it to some
    argument (of type [C]); the result will actually be a [Student],
    while [g] will be expecting a [Person], but this is safe because
    the only thing [g] can then do is to project out the two fields
    that it knows about ([name] and [age]), and these will certainly
    be among the fields that are present.

    This example suggests that the subtyping rule for arrow types
    should say that two arrow types are in the subtype relation if
    their results are:
                                  S2 <: T2
                              ----------------                     (S_Arrow_Co)
                            S1 -> S2 <: S1 -> T2
    We can generalize this to allow the arguments of the two arrow
    types to be in the subtype relation as well:
                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2
    Notice that the argument types are subtypes "the other way round":
    in order to conclude that [S1->S2] to be a subtype of [T1->T2], it
    must be the case that [T1] is a subtype of [S1].  The arrow
    constructor is said to be _contravariant_ in its first argument
    and _covariant_ in its second. 

    Here is an example that illustrates this: 
       f : Person -> C
       g : (Student -> C) -> D
    The application [g f] is safe, because the only thing the body of
    [g] can do with [f] is to apply it to some argument of type
    [Student].  Since [f] requires records having (at least) the
    fields of a [Person], this will always work. So [Person -> C] is a
    subtype of [Student -> C] since [Student] is a subtype of
    [Person].

    The intuition is that, if we have a function [f] of type [S1->S2],
    then we know that [f] accepts elements of type [S1]; clearly, [f]
    will also accept elements of any subtype [T1] of [S1]. The type of
    [f] also tells us that it returns elements of type [S2]; we can
    also view these results belonging to any supertype [T2] of
    [S2]. That is, any function [f] of type [S1->S2] can also be
    viewed as having type [T1->T2]. 
*)

(** *** Records *)

(** What about subtyping for record types? *)

(** The basic intuition about subtyping for record types is that it is
   always safe to use a "bigger" record in place of a "smaller" one.
   That is, given a record type, adding extra fields will always
   result in a subtype.  If some code is expecting a record with
   fields [x] and [y], it is perfectly safe for it to receive a record
   with fields [x], [y], and [z]; the [z] field will simply be ignored.
   For example,
       {name:String, age:Nat, gpa:Nat} <: {name:String, age:Nat}
       {name:String, age:Nat} <: {name:String}
       {name:String} <: {}
   This is known as "width subtyping" for records. *)

(** We can also create a subtype of a record type by replacing the type
   of one of its fields with a subtype.  If some code is expecting a
   record with a field [x] of type [T], it will be happy with a record
   having a field [x] of type [S] as long as [S] is a subtype of
   [T]. For example,
       {x:Student} <: {x:Person}
   This is known as "depth subtyping". *)

(** Finally, although the fields of a record type are written in a
   particular order, the order does not really matter. For example, 
       {name:String,age:Nat} <: {age:Nat,name:String}
   This is known as "permutation subtyping". *)

(** We could formalize these requirements in a single subtyping rule
   for records as follows:
                        for each jk in j1..jn,
                    exists ip in i1..im, such that
                          jk=ip and Sp <: Tk
                  ----------------------------------                    (S_Rcd)
                  {i1:S1...im:Sm} <: {j1:T1...jn:Tn}
   That is, the record on the left should have all the field labels of
   the one on the right (and possibly more), while the types of the
   common fields should be in the subtype relation. However, this rule
   is rather heavy and hard to read.  If we like, we can decompose it
   into three simpler rules, which can be combined using [S_Trans] to
   achieve all the same effects. *)

(** First, adding fields to the end of a record type gives a subtype:
                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm} 
   We can use [S_RcdWidth] to drop later fields of a multi-field
   record while keeping earlier fields, showing for example that
   [{age:Nat,name:String} <: {name:String}]. *)

(** Second, we can apply subtyping inside the components of a compound
   record type:
                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}
   For example, we can use [S_RcdDepth] and [S_RcdWidth] together to
   show that [{y:Student, x:Nat} <: {y:Person}]. *)

(** Third, we need to be able to reorder fields.  For example, we
   might expect that [{name:String, gpa:Nat, age:Nat} <: Person].  We
   haven't quite achieved this yet: using just [S_RcdDepth] and
   [S_RcdWidth] we can only drop fields from the _end_ of a record
   type.  So we need:
         {i1:S1...in:Sn} is a permutation of {i1:T1...in:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}
*)

(** It is worth noting that full-blown language designs may choose not
    to adopt all of these subtyping rules. For example, in Java:

    - A subclass may not change the argument or result types of a
      method of its superclass (i.e., no depth subtyping or no arrow
      subtyping, depending how you look at it).

    - Each class has just one superclass ("single inheritance" of
      classes).

    - Each class member (field or method) can be assigned a single
      index, adding new indices "on the right" as more members are
      added in subclasses (i.e., no permutation for classes).

    - A class may implement multiple interfaces -- so-called "multiple
      inheritance" of interfaces (i.e., permutation is allowed for
      interfaces). *)

(** **** Exercise: 2 stars (arrow_sub_wrong) *)
(** Suppose we had incorrectly defined subtyping as covariant on both
    the right and the left of arrow types:
                            S1 <: T1    S2 <: T2
                            --------------------                (S_Arrow_wrong)
                            S1 -> S2 <: T1 -> T2
    Give a concrete example of functions [f] and [g] with the following types...
       f : Student -> Nat
       g : (Person -> Nat) -> Nat
    ... such that the application [g f] will get stuck during
    execution. *)
(*
Student <: Person && Nat <: Nat
==> (Student -> Nat) <: (Person -> Nat)

(Student -> Nat) <: (Person -> Nat) && Nat <: Nat
==> ((Person -> Nat) -> Nat) <: ((Student -> Nat) -> Nat)

[g f] = [((Person -> Nat) -> Nat) (Student -> Nat)]
==> [((Student -> Nat) -> Nat) (Student -> Nat)]
==> [Nat]

So, by above rule, [g f] should progress.
let f := forall x : Student, x.gpa.
let g := forall y : Person -> Nat, (y {James, 47}).

[g f] ==>
(f {James, 47})
stuck!
------------------------------------
       f : Person -> C
       g : (Student -> C) -> D

Student <: Person
(Person -> C) <: (Student -> C)
[g f] = [((Student -> C) -> D) (Person -> C)]
<: [((Student -> C) -> D) (Student -> C)]
D!

or,
((Student -> C) -> D) <: ((Person -> C) -> D)
[g f] <: [((Person -> C) -> D) (Person -> C)]
D!
*)

(** *** Top *)

(** Finally, it is natural to give the subtype relation a maximal
    element -- a type that lies above every other type and is
    inhabited by all (well-typed) values.  We do this by adding to the
    language one new type constant, called [Top], together with a
    subtyping rule that places it above every other type in the
    subtype relation:
                                   --------                             (S_Top)
                                   S <: Top
    The [Top] type is an analog of the [Object] type in Java and C[#]. *)

(* ############################################### *)
(** *** Summary *)

(** In summary, we form the STLC with subtyping by starting with the
    pure STLC (over some set of base types) and...

    - adding a base type [Top],

    - adding the rule of subsumption 
                         Gamma |- t : S     S <: T
                         -------------------------                      (T_Sub)
                               Gamma |- t : T
      to the typing relation, and

    - defining a subtype relation as follows: 
                              S <: U    U <: T
                              ----------------                        (S_Trans)
                                   S <: T

                                   ------                              (S_Refl)
                                   T <: T

                                   --------                             (S_Top)
                                   S <: Top

                            S1 <: T1    S2 <: T2
                            --------------------                       (S_Prod)
                             S1 * S2 <: T1 * T2

                            T1 <: S1    S2 <: T2
                            --------------------                      (S_Arrow)
                            S1 -> S2 <: T1 -> T2

                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm} 

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}

         {i1:S1...in:Sn} is a permutation of {i1:T1...in:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}
*)



(* ############################################### *)
(** ** Exercises *)

(** **** Exercise: 1 star, optional (subtype_instances_tf_1) *)
(** Suppose we have types [S], [T], [U], and [V] with [S <: T]
    and [U <: V].  Which of the following subtyping assertions
    are then true?  Write _true_ or _false_ after each one.  
    ([A], [B], and [C] here are base types.)
*)
(*
-> can only appear with arrow rule.
    - [T->S <: T->S]
true
    - [Top->U <: S->Top]
true
    - [(C->C) -> (A*B)  <:  (C->C) -> (Top*B)]
true
    - [T->T->U <: S->S->V]
true
    - [(T->T)->U <: (S->S)->V]
false
    - [((T->S)->T)->U <: ((S->T)->S)->V]
<=> ((S->T)->S) <: ((T->S)->T)
<=> T->S <: S->T
<=> S <: T
true
    - [S*V <: T*U]
false
[]
*)
(*
Assoc sound?
-------------------------------------------
T1 <: S1 && S2 <: T2
(S1 -> S2) <: (T1 -> T2)

(S1 -> S2) <: (T1 -> T2) && T3 <: S3
((T1 -> T2) -> T3) <: ((S1 -> S2) -> S3)
-------------------------------------------
S2 <: T2 && T3 <: S3
(T2 -> T3) <: (S2 -> S3)

T1 <: S1 && (T2 -> T3) <: (S2 -> S3)
(S1 -> (T2 -> T3)) <: (T1 -> (S2 -> S3))
*)
(*
(T -> U) <: (S -> V)
T -> (T -> U) <: S -> (S -> V)
T -> (T -> (T -> U)) <: S -> (S -> (S -> V))
*)

(** **** Exercise: 2 stars (subtype_order) *)
(** The following types happen to form a linear order with respect to subtyping:
    - [Top]
    - [Top -> Student]
    - [Student -> Person]
    - [Student -> Top]
    - [Person -> Student]

Write these types in order from the most specific to the most general.

[Top -> Student] <:
[Person -> Student] <:
[Student -> Person] <:
[Student -> Top] <:
[Top]

Where does the type [Top->Top->Student] fit into this order?
[Top->Top->Student] <: [Top]
[Top -> Student] <: [(Top->Top)->Student], but [Top->Top->Student] is not comparable
[Person -> Student], [Top->Top->Student] : not comparable
[Student -> Person], [Top->Top->Student] : not comparable
[Student -> Top], [Top->Top->Student] : not comparable
*)

(** **** Exercise: 1 star (subtype_instances_tf_2) *)
(** Which of the following statements are true?  Write _true_ or
    _false_ after each one.
      forall S T,
          S <: T  ->
          S->S   <:  T->T
false

      forall S,
           S <: A->A ->
           exists T,
              S = T->T  /\  T <: A
false

      forall S T1 T2,
           (S <: T1 -> T2) ->
           exists S1 S2,
              S = S1 -> S2  /\  T1 <: S1  /\  S2 <: T2 
true

      exists S,
           S <: S->S 
false

      exists S,
           S->S <: S   
true, Top

      forall S T1 T2,
           S <: T1*T2 ->
           exists S1 S2,
              S = S1*S2  /\  S1 <: T1  /\  S2 <: T2
true
[] *)

(** **** Exercise: 1 star (subtype_concepts_tf) *)
(** Which of the following statements are true, and which are false?
    - There exists a type that is a supertype of every other type.
true
    - There exists a type that is a subtype of every other type.
false
    - There exists a pair type that is a supertype of every other
      pair type.
true
    - There exists a pair type that is a subtype of every other
      pair type.
false
    - There exists an arrow type that is a supertype of every other
      arrow type.
false
    - There exists an arrow type that is a subtype of every other
      arrow type.
false
    - There is an infinite descending chain of distinct types in the
      subtype relation---that is, an infinite sequence of types
      [S0], [S1], etc., such that all the [Si]'s are different and
      each [S(i+1)] is a subtype of [Si].
true, adding a field inf...
    - There is an infinite _ascending_ chain of distinct types in
      the subtype relation---that is, an infinite sequence of types
      [S0], [S1], etc., such that all the [Si]'s are different and
      each [S(i+1)] is a supertype of [Si].
false, there must be a Top.
[]
*)

(** **** Exercise: 2 stars (proper_subtypes) *)
(** Is the following statement true or false?  Briefly explain your
    answer.
    forall T,
         ~(exists n, T = TBase n) ->
         exists S,
            S <: T  /\  S <> T
]]

What is TBase?
It seems right but not sure.
[]
*)

(** **** Exercise: 2 stars (small_large_1) *)
(** 
   - What is the _smallest_ type [T] ("smallest" in the subtype
     relation) that makes the following assertion true?  (Assume we
     have [Unit] among the base types and [unit] as a constant of this
     type.)
       empty |- (\p:T*Top. p.fst) ((\z:A.z), unit) : A->A

   - What is the _largest_ type [T] that makes the same assertion true?

\z:A.z \in A->A
T <: A->A
smallest : (Top->B) (if there exists, minimal elem s.t. B <: A)
largest : (A->A)
[]
*)

(** **** Exercise: 2 stars (small_large_2) *)
(** 
   - What is the _smallest_ type [T] that makes the following
     assertion true?
       empty |- (\p:(A->A * B->B). p) ((\z:A.z), (\z:B.z)) : T

   - What is the _largest_ type [T] that makes the same assertion true?


T : (A->A * B->B)
smallest : (Top->(min A) * Top->(min B)) <: ~~ <: T
largest : T <: ~~ <: (A->A * B->B)
[]
*)

(** **** Exercise: 2 stars, optional (small_large_3) *)
(** 
   - What is the _smallest_ type [T] that makes the following
     assertion true?
       a:A |- (\p:(A*T). (p.snd) (p.fst)) (a , \z:A.z) : A

   - What is the _largest_ type [T] that makes the same assertion true?

smallest :
p:(A*T) <- (a, \z:A.z)
A -> A <: T

(T A) ==> A

smallest
A -> A
largest
Top -> (min A)
[]
*)




(** **** Exercise: 2 stars (small_large_4) *)
(** 
   - What is the _smallest_ type [T] that makes the following
     assertion true?
       exists S,
         empty |- (\p:(A*T). (p.snd) (p.fst)) : S

   - What is the _largest_ type [T] that makes the same
     assertion true?

(T A) ==> S

T : Ta -> Tb
s.t. A <: Ta && Tb <: S
smallest : Top -> (min S)
largest : A -> S
[]
*)

(** **** Exercise: 2 stars (smallest_1) *)
(** What is the _smallest_ type [T] that makes the following
    assertion true?
      exists S, exists t, 
        empty |- (\x:T. x x) t : S
]]


(x x) : S
x : xa -> xb
x <: xa && xb <: S

x := Top -> S
otherwise, infinite chain?
[]
*)

(** **** Exercise: 2 stars (smallest_2) *)
(** What is the _smallest_ type [T] that makes the following
    assertion true?
      empty |- (\x:Top. x) ((\z:A.z) , (\z:B.z)) : T
]]

(Top -> Top) (A->A * B->B) : T
Top
[]
*)

(** **** Exercise: 3 stars, optional (count_supertypes) *)
(** How many supertypes does the record type [{x:A, y:C->C}] have?  That is,
    how many different types [T] are there such that [{x:A, y:C->C} <:
    T]?  (We consider two types to be different if they are written
    differently, even if each is a subtype of the other.  For example,
    [{x:A,y:B}] and [{y:B,x:A}] are different.)


I considered A and C does not have any other subtype order except with Top.

2-tuple (  *2! for permutation)
A, C->Top
A, Top
Top, C->C
Top, C->Top
Top, Top

1-tuple
Top
A
C->C
C->Top

14?
[]
*)

(** **** Exercise: 2 stars (pair_permutation) *)
(** The subtyping rule for product types
                            S1 <: T1    S2 <: T2
                            --------------------                        (S_Prod)
                               S1*S2 <: T1*T2
intuitively corresponds to the "depth" subtyping rule for records. Extending the analogy, we might consider adding a "permutation" rule 
                                   --------------
                                   T1*T2 <: T2*T1
for products.
Is this a good idea? Briefly explain why or why not.


It seems no problem, quite looks like matter of design..
[]
*)

(* ###################################################### *)
(** * Formal Definitions *)

(** Most of the definitions -- in particular, the syntax and
    operational semantics of the language -- are identical to what we
    saw in the last chapter.  We just need to extend the typing
    relation with the subsumption rule and add a new [Inductive]
    definition for the subtyping relation.  Let's first do the
    identical bits. *)

(* ###################################################### *)
(** ** Core Definitions *)

(* ################################### *)
(** *** Syntax *)

(** For the sake of more interesting examples below, we'll allow an
    arbitrary set of additional base types like [String], [Float],
    etc.  We won't bother adding any constants belonging to these
    types or any operators on them, but we could easily do so. *)

(** In the rest of the chapter, we formalize just base types,
    booleans, arrow types, [Unit], and [Top], omitting record types
    and leaving product types as an exercise. *)

Inductive ty : Type :=
  | TTop   : ty
  | TBool  : ty
  | TBase  : id -> ty
  | TArrow : ty -> ty -> ty
  | TUnit  : ty
  | TProd  : ty -> ty -> ty
  | TRNil : ty
  | TRCons : id -> ty -> ty -> ty.


Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TTop" | Case_aux c "TBool" 
  | Case_aux c "TBase" | Case_aux c "TArrow" 
  | Case_aux c "TUnit"
  | Case_aux c "TProd"
  | Case_aux c "TRNil" | Case_aux c "TRCons"             
  ].

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tunit : tm

  | tpair : tm -> tm -> tm
  | tfst : tm -> tm
  | tsnd : tm -> tm

  | tproj : tm -> id -> tm
  | trnil :  tm
  | trcons : id -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "ttrue" 
  | Case_aux c "tfalse" | Case_aux c "tif"
  | Case_aux c "tunit"
  | Case_aux c "tpair"
  | Case_aux c "tfst"
  | Case_aux c "tsnd"
  | Case_aux c "tproj" | Case_aux c "trnil" | Case_aux c "trcons"             
  ].

(* ################################### *)
(** *** Substitution *)

(** The definition of substitution remains exactly the same as for the
    pure STLC. *)

Inductive record_ty : ty -> Prop :=
  | RTnil : 
        record_ty TRNil
  | RTcons : forall i T1 T2,
        record_ty (TRCons i T1 T2).

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm trnil
  | rtcons : forall i t1 t2,
        record_tm (trcons i t1 t2).

Inductive well_formed_ty : ty -> Prop :=
  | wfTBase : forall i,
        well_formed_ty (TBase i)
  | wfTArrow : forall T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        well_formed_ty (TArrow T1 T2)
  | wfTRNil :
        well_formed_ty TRNil
  | wfTRCons : forall i T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        record_ty T2 ->
        well_formed_ty (TRCons i T1 T2)
  | wfTProd : forall T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        well_formed_ty (TProd T1 T2)
  | wfTTop :
        well_formed_ty TTop
  | wfTUnit :
        well_formed_ty TUnit
  | wfTBool :
        well_formed_ty TBool
.

Hint Constructors record_ty record_tm well_formed_ty.

Fixpoint subst (x:id) (s:tm)  (t:tm) : tm :=
  match t with
  | tvar y => 
      if eq_id_dec x y then s else t
  | tabs y T t1 => 
      tabs y T (if eq_id_dec x y then t1 else (subst x s t1))
  | tapp t1 t2 => 
      tapp (subst x s t1) (subst x s t2)
  | ttrue => 
      ttrue
  | tfalse => 
      tfalse
  | tif t1 t2 t3 => 
      tif (subst x s t1) (subst x s t2) (subst x s t3)
  | tunit => 
      tunit

  | tpair t1 t2 => 
      tpair (subst x s t1) (subst x s t2)
  | tfst t1 => 
      tfst (subst x s t1)
  | tsnd t1 => 
      tsnd (subst x s t1)

  | tproj t1 i => tproj (subst x s t1) i
  | trnil => trnil
  | trcons i t1 tr1 => trcons i (subst x s t1) (subst x s tr1)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(* ################################### *)
(** *** Reduction *)

(** Likewise the definitions of the [value] property and the [step]
    relation. *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true : 
      value ttrue
  | v_false : 
      value tfalse
  | v_unit : 
      value tunit

  | v_rnil : value trnil
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value (trcons i v1 vr)

  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value (tpair v1 v2)
.


Hint Constructors value.


Fixpoint Tlookup (i:id) (Tr:ty) : option ty :=
  match Tr with
  | TRCons i' T Tr' => if eq_id_dec i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Fixpoint tlookup (i:id) (tr:tm) : option tm :=
  match tr with
  | trcons i' t tr' => if eq_id_dec i i' then Some t else tlookup i tr'
  | _ => None
  end.


Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (tapp t1 t2) ==> (tapp t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (tapp v1 t2) ==> (tapp v1  t2')
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
                     
  | ST_Pair1 : forall t1 t1' t2,
        t1 ==> t1' ->
        (tpair t1 t2) ==> (tpair t1' t2)
  | ST_Pair2 : forall v1 t2 t2',
        value v1 ->
        t2 ==> t2' ->
        (tpair v1 t2) ==> (tpair v1 t2')
  | ST_Fst1 : forall t1 t1',
        t1 ==> t1' ->
        (tfst t1) ==> (tfst t1')
  | ST_FstPair : forall v1 v2,
        value v1 ->
        value v2 ->
        (tfst (tpair v1 v2)) ==> v1
  | ST_Snd1 : forall t1 t1',
        t1 ==> t1' ->
        (tsnd t1) ==> (tsnd t1')
  | ST_SndPair : forall v1 v2,
        value v1 ->
        value v2 ->
        (tsnd (tpair v1 v2)) ==> v2


  | ST_Proj1 : forall t1 t1' i,
        t1 ==> t1' ->
        (tproj t1 i) ==> (tproj t1' i)
  | ST_ProjRcd : forall tr i vi,
        value tr ->
        tlookup i tr = Some vi ->
        (tproj tr i) ==> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
        t1 ==> t1' ->
        (trcons i t1 tr2) ==> (trcons i t1' tr2)
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
        value v1 ->
        tr2 ==> tr2' ->
        (trcons i v1 tr2) ==> (trcons i v1 tr2')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" 
  | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue" 
  | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"
  | Case_aux c "ST_Pair1"
  | Case_aux c "ST_Pair2"
  | Case_aux c "ST_Fst1"
  | Case_aux c "ST_FstPair"
  | Case_aux c "ST_Snd1"
  | Case_aux c "ST_SndPair"
  | Case_aux c "ST_Proj1" | Case_aux c "ST_ProjRcd"
  | Case_aux c "ST_Rcd_Head" | Case_aux c "ST_Rcd_Tail"
  ].

Hint Constructors step.


(* from MoreStlc.v *)



(* ###################################################################### *)
(** ** Records *)

(** As a final example of a basic extension of the STLC, let's
    look briefly at how to define _records_ and their types.
    Intuitively, records can be obtained from pairs by two kinds of
    generalization: they are n-ary products (rather than just binary)
    and their fields are accessed by _label_ (rather than position).

    Conceptually, this extension is a straightforward generalization
    of pairs and product types, but notationally it becomes a little
    heavier; for this reason, we postpone its formal treatment to a
    separate chapter ([Records]). *)

(** Records are not included in the extended exercise below, but
    they will be useful to motivate the [Sub] chapter. *)

(** Syntax:
<<
       t ::=                          Terms
           | ...
           | {i1=t1, ..., in=tn}         record 
           | t.i                         projection

       v ::=                          Values
           | ...
           | {i1=v1, ..., in=vn}         record value

       T ::=                          Types
           | ...
           | {i1:T1, ..., in:Tn}         record type
>> 
   Intuitively, the generalization is pretty obvious.  But it's worth
   noticing that what we've actually written is rather informal: in
   particular, we've written "[...]" in several places to mean "any
   number of these," and we've omitted explicit mention of the usual
   side-condition that the labels of a record should not contain
   repetitions. *)
(* It is possible to devise informal notations that are
   more precise, but these tend to be quite heavy and to obscure the
   main points of the definitions.  So we'll leave these a bit loose
   here (they are informal anyway, after all) and do the work of
   tightening things up elsewhere (in chapter [Records]). *)

(**
   Reduction:
                              ti ==> ti'
                 ------------------------------------                  (ST_Rcd)
                     {i1=v1, ..., im=vm, in=ti, ...}
                 ==> {i1=v1, ..., im=vm, in=ti', ...}

                              t1 ==> t1'
                            --------------                           (ST_Proj1)
                            t1.i ==> t1'.i

                      -------------------------                    (ST_ProjRcd)
                      {..., i=vi, ...}.i ==> vi
   Again, these rules are a bit informal.  For example, the first rule
   is intended to be read "if [ti] is the leftmost field that is not a
   value and if [ti] steps to [ti'], then the whole record steps..."
   In the last rule, the intention is that there should only be one
   field called i, and that all the other fields must contain values. *)

(**
   Typing:
            Gamma |- t1 : T1     ...     Gamma |- tn : Tn
          --------------------------------------------------            (T_Rcd)
          Gamma |- {i1=t1, ..., in=tn} : {i1:T1, ..., in:Tn}

                    Gamma |- t : {..., i:Ti, ...}
                    -----------------------------                      (T_Proj)
                          Gamma |- t.i : Ti

*)

(* ###################################################################### *)
(** *** Encoding Records (Optional) *)

(** There are several ways to make the above definitions precise.  

      - We can directly formalize the syntactic forms and inference
        rules, staying as close as possible to the form we've given
        them above.  This is conceptually straightforward, and it's
        probably what we'd want to do if we were building a real
        compiler -- in particular, it will allow is to print error
        messages in the form that programmers will find easy to
        understand.  But the formal versions of the rules will not be
        pretty at all!

      - We could look for a smoother way of presenting records -- for
        example, a binary presentation with one constructor for the
        empty record and another constructor for adding a single field
        to an existing record, instead of a single monolithic
        constructor that builds a whole record at once.  This is the
        right way to go if we are primarily interested in studying the
        metatheory of the calculi with records, since it leads to
        clean and elegant definitions and proofs.  Chapter [Records]
        shows how this can be done.

      - Alternatively, if we like, we can avoid formalizing records
        altogether, by stipulating that record notations are just
        informal shorthands for more complex expressions involving
        pairs and product types.  We sketch this approach here.

    First, observe that we can encode arbitrary-size tuples using
    nested pairs and the [unit] value.  To avoid overloading the pair
    notation [(t1,t2)], we'll use curly braces without labels to write
    down tuples, so [{}] is the empty tuple, [{5}] is a singleton
    tuple, [{5,6}] is a 2-tuple (morally the same as a pair),
    [{5,6,7}] is a triple, etc.  
<<
    {}                 ---->  unit
    {t1, t2, ..., tn}  ---->  (t1, trest)
                              where {t2, ..., tn} ----> trest
>>
    Similarly, we can encode tuple types using nested product types:
<<
    {}                 ---->  Unit
    {T1, T2, ..., Tn}  ---->  T1 * TRest
                              where {T2, ..., Tn} ----> TRest
>>
    The operation of projecting a field from a tuple can be encoded
    using a sequence of second projections followed by a first projection: 
<<
    t.0        ---->  t.fst
    t.(n+1)    ---->  (t.snd).n
>>

    Next, suppose that there is some total ordering on record labels,
    so that we can associate each label with a unique natural number.
    This number is called the _position_ of the label.  For example,
    we might assign positions like this:
<<
      LABEL   POSITION
      a       0
      b       1
      c       2
      ...     ...
      foo     1004
      ...     ...
      bar     10562
      ...     ...
>>       

    We use these positions to encode record values as tuples (i.e., as
    nested pairs) by sorting the fields according to their positions.
    For example:
<<
      {a=5, b=6}      ---->   {5,6}
      {a=5, c=7}      ---->   {5,unit,7}
      {c=7, a=5}      ---->   {5,unit,7}
      {c=5, b=3}      ---->   {unit,3,5}
      {f=8,c=5,a=7}   ---->   {7,unit,5,unit,unit,8}
      {f=8,c=5}       ---->   {unit,unit,5,unit,unit,8}
>>
    Note that each field appears in the position associated with its
    label, that the size of the tuple is determined by the label with
    the highest position, and that we fill in unused positions with
    [unit].  

    We do exactly the same thing with record types:
<<
      {a:Nat, b:Nat}      ---->   {Nat,Nat}
      {c:Nat, a:Nat}      ---->   {Nat,Unit,Nat}
      {f:Nat,c:Nat}       ---->   {Unit,Unit,Nat,Unit,Unit,Nat}
>>

    Finally, record projection is encoded as a tuple projection from
    the appropriate position:
<<
      t.l  ---->  t.(position of l)
>>    

    It is not hard to check that all the typing rules for the original
    "direct" presentation of records are validated by this
    encoding.  (The reduction rules are "almost validated" -- not
    quite, because the encoding reorders fields.) *)

(** Of course, this encoding will not be very efficient if we
    happen to use a record with label [bar]!  But things are not
    actually as bad as they might seem: for example, if we assume that
    our compiler can see the whole program at the same time, we can
    _choose_ the numbering of labels so that we assign small positions
    to the most frequently used labels.  Indeed, there are industrial
    compilers that essentially do this! *)

(** *** Variants (Optional Reading) *)

(** Just as products can be generalized to records, sums can be
    generalized to n-ary labeled types called _variants_.  Instead of
    [T1+T2], we can write something like [<l1:T1,l2:T2,...ln:Tn>]
    where [l1],[l2],... are field labels which are used both to build
    instances and as case arm labels.  

    These n-ary variants give us almost enough mechanism to build
    arbitrary inductive data types like lists and trees from
    scratch -- the only thing missing is a way to allow _recursion_ in
    type definitions.  We won't cover this here, but detailed
    treatments can be found in many textbooks -- e.g., Types and
    Programming Languages. *)












(* ###################################################################### *)
(** ** Subtyping *)

(** Now we come to the most interesting part.  We begin by
    defining the subtyping relation and developing some of its
    important technical properties. *)

(** The definition of subtyping is just what we sketched in the
    motivating discussion. *)

Reserved Notation "T '<:' U" (at level 40).

(* well_formed_ty ??? *)

Inductive is_sublist : ty -> ty -> Prop :=
  | sub_nil : forall l,
      is_sublist TRNil l
  | sub_append : forall i Ti l1 l2,
      is_sublist l1 l2 ->
      Tlookup i l2 = Some Ti ->
      is_sublist (TRCons i Ti l1) l2
.
(*
  S <: T ->
  Tlookup i T = Some T1 ->
(*  Tlookup i S = Some T1. *)
  exists T2, (Tlookup i S = Some T2) /\ (T2 <: T1).
*)

Hint Constructors is_sublist.

Example is_sublist_ex0 :
  (is_sublist TRNil TRNil).
Proof. auto. Qed.

Example is_sublist_ex1 :
  (is_sublist TRNil (TRCons (Id 20) (TBase (Id 25)) TRNil)).
Proof. auto. Qed.

Example is_sublist_ex2 :
  (is_sublist 
     (TRCons (Id 30) (TBase (Id 35)) (TRCons (Id 20) (TBase (Id 25)) TRNil))
     (TRCons (Id 20) (TBase (Id 25)) (TRCons (Id 30) (TBase (Id 35)) TRNil))
  ).
Proof. auto. Qed.


(*
Set Implicit Arguments.

Local Notation "[ ]" := nil.
(* Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..). *)

Section Permutation.

Variable A:Type.

Inductive Permutation : list A -> list A -> Prop :=
| perm_nil: Permutation [] []
| perm_skip x l l' : Permutation l l' -> Permutation (x::l) (x::l')
| perm_swap x y l : Permutation (y::x::l) (x::y::l)
| perm_trans l l' l'' : Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Local Hint Constructors Permutation.

Theorem Permutation_nil : forall (l : list A), Permutation [] l -> l = nil.

Theorem Permutation_nil_cons : forall (l : list A) (x : A), ~ Permutation nil (x::l).

Permutation over lists is a equivalence relation

Theorem Permutation_refl : forall l : list A, Permutation l l.

Theorem Permutation_sym : forall l l' : list A, Permutation l l' -> Permutation l' l.

Theorem Permutation_trans : forall l l' l'' : list A, Permutation l l' -> Permutation l' l'' -> Permutation l l''.

End Permutation.

Hint Resolve Permutation_refl perm_nil perm_skip.


Local Hint Resolve perm_swap perm_trans.
Local Hint Resolve Permutation_sym Permutation_trans.


Instance Permutation_Equivalence A : Equivalence (@Permutation A) | 10 := {
  Equivalence_Reflexive := @Permutation_refl A ;
  Equivalence_Symmetric := @Permutation_sym A ;
  Equivalence_Transitive := @Permutation_trans A }.

Add Parametric Morphism A (a:A) : (cons a)
  with signature @Permutation A ==> @Permutation A
  as Permutation_cons.

Section Permutation_properties.

Variable A:Type.

Implicit Types a b : A.
Implicit Types l m : list A.

Compatibility with others operations on lists

Theorem Permutation_in : forall (l l' : list A) (x : A), Permutation l l' -> In x l -> In x l'.

Lemma Permutation_app_tail : forall (l l' tl : list A), Permutation l l' -> Permutation (l++tl) (l'++tl).

Lemma Permutation_app_head : forall (l tl tl' : list A), Permutation tl tl' -> Permutation (l++tl) (l++tl').

Theorem Permutation_app : forall (l m l' m' : list A), Permutation l l' -> Permutation m m' -> Permutation (l++m) (l'++m').

Add Parametric Morphism : (@app A)
  with signature @Permutation A ==> @Permutation A ==> @Permutation A
  as Permutation_app'.
Qed.

Lemma Permutation_add_inside : forall a (l l' tl tl' : list A),
  Permutation l l' -> Permutation tl tl' ->
  Permutation (l ++ a :: tl) (l' ++ a :: tl').

Lemma Permutation_cons_append : forall (l : list A) x,
  Permutation (x :: l) (l ++ x :: nil).
Local Hint Resolve Permutation_cons_append.

Theorem Permutation_app_comm : forall (l l' : list A),
  Permutation (l ++ l') (l' ++ l).
Local Hint Resolve Permutation_app_comm.

Theorem Permutation_cons_app : forall (l l1 l2:list A) a,
  Permutation l (l1 ++ l2) -> Permutation (a :: l) (l1 ++ a :: l2).
Local Hint Resolve Permutation_cons_app.

Theorem Permutation_middle : forall (l1 l2:list A) a,
  Permutation (a :: l1 ++ l2) (l1 ++ a :: l2).
Local Hint Resolve Permutation_middle.

Theorem Permutation_rev : forall (l : list A), Permutation l (rev l).

Add Parametric Morphism : (@rev A)
  with signature @Permutation A ==> @Permutation A as Permutation_rev'.

Theorem Permutation_length : forall (l l' : list A), Permutation l l' -> length l = length l'.

Theorem Permutation_ind_bis :
 forall P : list A -> list A -> Prop,
   P [] [] ->
   (forall x l l', Permutation l l' -> P l l' -> P (x :: l) (x :: l')) ->
   (forall x y l l', Permutation l l' -> P l l' -> P (y :: x :: l) (x :: y :: l')) ->
   (forall l l' l'', Permutation l l' -> P l l' -> Permutation l' l'' -> P l' l'' -> P l l'') ->
   forall l l', Permutation l l' -> P l l'.

Ltac break_list l x l' H :=
  destruct l as [|x l']; simpl in *;
  injection H; intros; subst; clear H.

Theorem Permutation_nil_app_cons : forall (l l' : list A) (x : A), ~ Permutation nil (l++x::l').

Theorem Permutation_app_inv : forall (l1 l2 l3 l4:list A) a,
  Permutation (l1++a::l2) (l3++a::l4) -> Permutation (l1++l2) (l3 ++ l4).

Theorem Permutation_cons_inv :
   forall l l' a, Permutation (a::l) (a::l') -> Permutation l l'.

Theorem Permutation_cons_app_inv :
   forall l l1 l2 a, Permutation (a :: l) (l1 ++ a :: l2) -> Permutation l (l1 ++ l2).

Theorem Permutation_app_inv_l :
    forall l l1 l2, Permutation (l ++ l1) (l ++ l2) -> Permutation l1 l2.

Theorem Permutation_app_inv_r :
   forall l l1 l2, Permutation (l1 ++ l) (l2 ++ l) -> Permutation l1 l2.

Lemma Permutation_length_1_inv: forall a l, Permutation [a] l -> l = [a].

Lemma Permutation_length_1: forall a b, Permutation [a] [b] -> a = b.

Lemma Permutation_length_2_inv :
  forall a1 a2 l, Permutation [a1;a2] l -> l = [a1;a2] \/ l = [a2;a1].

Lemma Permutation_length_2 :
  forall a1 a2 b1 b2, Permutation [a1;a2] [b1;b2] ->
    a1 = b1 /\ a2 = b2 \/ a1 = b2 /\ a2 = b1.

Lemma NoDup_Permutation : forall l l',
  NoDup l -> NoDup l' -> (forall x:A, In x l <-> In x l') -> Permutation l l'.

End Permutation_properties.

Section Permutation_map.

Variable A B : Type.
Variable f : A -> B.

Add Parametric Morphism : (map f)
  with signature (@Permutation A) ==> (@Permutation B) as Permutation_map_aux.

Lemma Permutation_map :
  forall l l', Permutation l l' -> Permutation (map f l) (map f l').

End Permutation_map.
*)

Inductive subtype : ty -> ty -> Prop :=
  | S_Refl : forall T,
      well_formed_ty T ->
      T <: T
  | S_Trans : forall S U T,
      S <: U ->
      U <: T ->
      S <: T
  | S_Top : forall S,
      well_formed_ty S ->
      S <: TTop
  | S_Arrow : forall S1 S2 T1 T2,
      T1 <: S1 ->
      S2 <: T2 ->
      (TArrow S1 S2) <: (TArrow T1 T2)

  | S_Prod : forall S1 S2 T1 T2,
      S1 <: T1 ->
      S2 <: T2 ->
      (TProd S1 S2) <: (TProd T1 T2)

  | S_RcdWidthBoth : forall i Ti T1 T2,
      well_formed_ty Ti ->
      record_ty T1 ->
      record_ty T2 ->
      T1 <: T2 ->
      TRCons i Ti T1 <: TRCons i Ti T2
  | S_RcdWidthNil : forall T,
      well_formed_ty T ->
      record_ty T ->
      T <: TRNil
                               (*
  | S_RcdWidthSub : forall i Ti T1 T2,
      record_ty T1 ->
      record_ty T2 ->
      T1 <: T2 ->
      TRCons i Ti T1 <: T2
*)
  | S_RcdDepth : forall i T1 T2 T,
      well_formed_ty T ->
      record_ty T ->
      T1 <: T2 ->
      TRCons i T1 T <: TRCons i T2 T

  | S_RcdPerm : forall T1 T2,
      well_formed_ty T1 ->
      well_formed_ty T2 ->
      record_ty T1 ->
      record_ty T2 ->
      is_sublist T1 T2 -> is_sublist T2 T1 ->
      T1 <: T2
                         (*
  | S_ProdWidth1 : forall S1 S2,
      (TProd S1 S2) <: S1
  | S_ProdWidth2 : forall S1 S2,
      (TProd S1 S2) <: S2
*)
(*
  | S_ProdPerm : forall S1 S2,
      (TProd S1 S2) <: (TProd S2 S1)
*)
                         (*
  | S_RcdWidth : 
  | S_RcdDepth : 
  | S_RcdPerm :
*)

where "T '<:' U" := (subtype T U).


(*

                        for each jk in j1..jn,
                    exists ip in i1..im, such that
                          jk=ip and Sp <: Tk
                  ----------------------------------                    (S_Rcd)
                  {i1:S1...im:Sm} <: {j1:T1...jn:Tn}


                               n > m
                 ---------------------------------                 (S_RcdWidth)
                 {i1:T1...in:Tn} <: {i1:T1...im:Tm} 

                       S1 <: T1  ...  Sn <: Tn
                  ----------------------------------               (S_RcdDepth)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}

         {i1:S1...in:Sn} is a permutation of {i1:T1...in:Tn}
         ---------------------------------------------------        (S_RcdPerm)
                  {i1:S1...in:Sn} <: {i1:T1...in:Tn}
*)

(** Note that we don't need any special rules for base types: they are
    automatically subtypes of themselves (by [S_Refl]) and [Top] (by
    [S_Top]), and that's all we want. *)

Hint Constructors well_formed_ty subtype.

Tactic Notation "subtype_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "S_Refl" | Case_aux c "S_Trans"
  | Case_aux c "S_Top" | Case_aux c "S_Arrow"
  | Case_aux c "S_Prod"
  | Case_aux c "S_RcdWidthBoth"
  | Case_aux c "S_RcdWidthNil"
(*  | Case_aux c "S_RcdWidthSub" *)
  | Case_aux c "S_RcdDepth"
  | Case_aux c "S_RcdPerm"

(*
  | Case_aux c "S_ProdWidth1"
  | Case_aux c "S_ProdWidth2"
*)
(*  | Case_aux c "S_ProdPerm" *)
  ].

Lemma has_subtype__wf : forall S T,
  S <: T ->
  well_formed_ty S /\ well_formed_ty T.
Proof with eauto.
(*  T_cases (induction S) Case; intros; eauto; try solve by inversion. *)
  (*
  intros.
  remember T as rem. generalize dependent T. 
  subtype_cases (induction H) Case; intros; eauto; try solve by inversion.
  *)
  
  intros.
  subtype_cases (induction H) Case; eauto; try solve by inversion...
  inv IHsubtype1... inv IHsubtype2...
  inv IHsubtype1... inv IHsubtype2...
  inv IHsubtype1... inv IHsubtype2...
  inv IHsubtype...
  inv IHsubtype...
Qed.

  (*
Lemma has_type__wf : forall Gamma t T,
  Gamma |- t \in T -> well_formed_ty T.
  *)

Module Examples.

Notation x := (Id 0).
Notation y := (Id 1).
Notation z := (Id 2).

Notation A := (TBase (Id 6)).
Notation B := (TBase (Id 7)).
Notation C := (TBase (Id 8)).

Notation String := (TBase (Id 9)).
Notation Float := (TBase (Id 10)).
Notation Integer := (TBase (Id 11)).
Notation Department := (TBase (Id 12)).

(** **** Exercise: 2 stars, optional (subtyping_judgements) *)

(** (Do this exercise after you have added product types to the
    language, at least up to this point in the file).

    Using the encoding of records into pairs, define pair types
    representing the record types
    Person   := { name : String }
    Student  := { name : String ; 
                  gpa  : Float }
    Employee := { name : String ;
                  ssn  : Integer }
*)

Definition name := (Id 10).
Notation gpa := (Id 11).
Notation ssn := (Id 12).

Definition Person : ty := 
  (TRCons name String TRNil).
Definition Student : ty := 
  (TRCons name String (TRCons gpa Float TRNil)).
Definition Student' : ty := 
  (TRCons gpa Float (TRCons name String TRNil)).
Definition Employee : ty := 
  (TRCons name String (TRCons ssn Integer TRNil)).

Definition perm_xyz : ty :=
  (TRCons x A (TRCons y B (TRCons z C TRNil))).
Definition perm_xzy : ty :=
  (TRCons x A (TRCons z C (TRCons y B TRNil))).
Definition perm_yxz : ty :=
  (TRCons y B (TRCons x A (TRCons z C TRNil))).
Definition perm_yzx : ty :=
  (TRCons y B (TRCons z C (TRCons x A TRNil))).
Definition perm_zxy : ty :=
  (TRCons z C (TRCons x A (TRCons y B TRNil))).
Definition perm_zyx : ty :=
  (TRCons z C (TRCons y B (TRCons x A TRNil))).

Example perm_xyz_xyz : 
  perm_xyz <: perm_xyz.
Proof with eauto.
  unfold perm_xyz, perm_xzy, perm_yxz, perm_yzx, perm_zxy, perm_zyx...
Qed.
Example perm_xyz_xzy : 
  perm_xyz <: perm_xzy.
Proof with eauto.
  unfold perm_xyz, perm_xzy, perm_yxz, perm_yzx, perm_zxy, perm_zyx. apply S_RcdPerm...
Qed.
Example perm_xyz_yxz : 
  perm_xyz <: perm_yxz.
Proof with eauto.
  unfold perm_xyz, perm_xzy, perm_yxz, perm_yzx, perm_zxy, perm_zyx. apply S_RcdPerm...
Qed.
Example perm_xyz_yzx : 
  perm_xyz <: perm_yzx.
Proof with eauto.
  unfold perm_xyz, perm_xzy, perm_yxz, perm_yzx, perm_zxy, perm_zyx. apply S_RcdPerm...
Qed.
Example perm_xyz_zxy : 
  perm_xyz <: perm_zxy.
Proof with eauto.
  unfold perm_xyz, perm_xzy, perm_yxz, perm_yzx, perm_zxy, perm_zyx. apply S_RcdPerm...
Qed.
Example perm_xyz_zyx : 
  perm_xyz <: perm_zyx.
Proof with eauto.
  unfold perm_xyz, perm_xzy, perm_yxz, perm_yzx, perm_zxy, perm_zyx. apply S_RcdPerm...
Qed.

Example sub_student_person :
  Student <: Person.
Proof.
  unfold Student, Person.
  auto.
Qed.

Example sub_student_student' : 
  Student <: Student'.
Proof with eauto.
  unfold Student', Student. apply S_RcdPerm...
Qed.

Example sub_student'_student : 
  Student' <: Student.
Proof with eauto.
  unfold Student', Student. apply S_RcdPerm...
Qed.

Example sub_student'_person :
  Student' <: Person.
Proof with eauto.
  eapply S_Trans.
  apply sub_student'_student.
  apply sub_student_person.
Qed.

Example sub_employee_person :
  Employee <: Person.
Proof.
  unfold Employee, Person.
  auto.
Qed.
(** [] *)

Example subtyping_example_0 :
  (TArrow C Person) <: (TArrow C TTop).
  (* C->Person <: C->Top *)
Proof.
  unfold Person.
  apply S_Arrow.
    apply S_Refl. auto.
    apply S_Top. eauto.
Qed.

(** The following facts are mostly easy to prove in Coq.  To get
    full benefit from the exercises, make sure you also
    understand how to prove them on paper! *)

(** **** Exercise: 1 star, optional (subtyping_example_1) *)
Example subtyping_example_1 :
  (TArrow TTop Student) <: (TArrow (TArrow C C) Person).
  (* Top->Student <: (C->C)->Person *)
Proof with eauto.
  unfold Student, Person.
  eapply S_Arrow.
  apply S_Top.


  auto.
  apply sub_student_person.
Qed.
(** [] *)

(** **** Exercise: 1 star, optional (subtyping_example_2) *)
Example subtyping_example_2 :
  (TArrow TTop Person) <: (TArrow Person TTop).
  (* Top->Person <: Person->Top *)
Proof with eauto.
  unfold Person.
  auto.
Qed.

End Examples.


(* ###################################################################### *)
(** ** Typing *)

(** The only change to the typing relation is the addition of the rule
    of subsumption, [T_Sub]. *)

Definition context := id -> (option ty).
Definition empty : context := (fun _ => None). 
Definition extend (Gamma : context) (x:id) (T : ty) :=
  fun x' => if eq_id_dec x x' then Some T else Gamma x'.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Same as before *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- (tvar x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      (extend Gamma x T11) |- t12 \in T12 -> 
      Gamma |- (tabs x T11 t12) \in (TArrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (TArrow T1 T2) -> 
      Gamma |- t2 \in T1 -> 
      Gamma |- (tapp t1 t2) \in T2
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- (tif t1 t2 t3) \in T
  | T_Unit : forall Gamma,
      Gamma |- tunit \in TUnit
  (* New rule of subsumption *)
  | T_Sub : forall Gamma t S T,
      well_formed_ty T ->
      Gamma |- t \in S ->
      S <: T ->
      Gamma |- t \in T

  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |- t1 \in T1 ->
      Gamma |- t2 \in T2 ->
      Gamma |- (tpair t1 t2) \in (TProd T1 T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |- t \in (TProd T1 T2) ->
      Gamma |- (tfst t) \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |- t \in (TProd T1 T2) ->
      Gamma |- (tsnd t) \in T2                       

  | T_Proj : forall Gamma i t Ti Tr,
      Gamma |- t \in Tr ->
      Tlookup i Tr = Some Ti ->
      Gamma |- (tproj t i) \in Ti
  | T_RNil : forall Gamma,
      Gamma |- trnil \in TRNil
  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- (trcons i t tr) \in (TRCons i T Tr)                              
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_True" 
  | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Unit"     
  | Case_aux c "T_Sub"
  | Case_aux c "T_Pair"
  | Case_aux c "T_Fst"
  | Case_aux c "T_Snd"
  | Case_aux c "T_Proj"
  | Case_aux c "T_RNil"
  | Case_aux c "T_RCons"
  ].
















Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof with eauto.
  intros i T.
  T_cases (induction T) Case; intros; try solve by inversion.
  Case "TRCons".
    inversion H. subst. unfold Tlookup in H0.
    destruct (eq_id_dec i i0)...
    inversion H0. subst...  Qed.

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr ==> tr' ->
  record_tm tr'.
Proof.
  intros tr tr' Hrt Hstp.
  inversion Hrt; subst; inversion Hstp; subst; auto.
Qed.

Lemma has_type__wf : forall Gamma t T,
  Gamma |- t \in T -> well_formed_ty T.
Proof with eauto.
  intros Gamma t T Htyp.
  has_type_cases (induction Htyp) Case; eauto; try solve by inversion...
  Case "T_App".
    inversion IHHtyp1...
  Case "T_Fst".
    inv IHHtyp...
  Case "T_Snd".
    inv IHHtyp...
  Case "T_Proj".
    eapply wf_rcd_lookup...
Qed.

Lemma lookup_in_sublist : forall Ti T1 T2 i,
  is_sublist T2 T1 ->
  Tlookup i T2 = Some Ti ->
  Tlookup i T1 = Some Ti.
Proof with eauto.
  intros.
  generalize dependent i.
  induction H; intros. inv H0.
  inv H1...
  destruct (eq_id_dec i0 i). subst...
  generalize H3; intro.
  apply IHis_sublist in H1.
  rewrite H1. rewrite H3. reflexivity.
Qed.

Lemma lookup_in_subtype : forall S T i T1,
(*  well_formed_ty T -> *)
  S <: T ->
  Tlookup i T = Some T1 ->
(*  Tlookup i S = Some T1. *)
  exists T2, (Tlookup i S = Some T2) /\ (T2 <: T1).
Proof with eauto.
  intros.
  generalize dependent T1.
  generalize dependent i.
  subtype_cases (induction H) Case; intros; eauto; try solve by inversion...
  Case "S_Refl". exists T1... split... eapply wf_rcd_lookup in H...
  Case "S_Trans".
  generalize (IHsubtype2 i T1); intro Tmp; exploit Tmp; eauto; intro; clear Tmp.
  inv H2. inv H3.
  generalize (IHsubtype1 i x); intro Tmp; exploit Tmp; eauto; intro; clear Tmp.
  inv H3. inv H5.
  eexists; eauto.
  Case "S_RcdWidthBoth".
  destruct (eq_id_dec i i0); inv H3; simpl in *.
  repeat rewrite eq_id in *... inv H5. exists T0...
  rewrite neq_id in *...
(*
  destruct (eq_id_dec i i0); inv H2; simpl in *. repeat rewrite eq_id in *...
  rewrite neq_id in *...   rewrite neq_id in *...
  generalize (IHsubtype i0 Ti0); intro T; exploit T; eauto; intro; clear T.
  rewrite H4. rewrite H2...
*)
  Case "S_RcdDepth".
  simpl in *.
  destruct (eq_id_dec i0 i)... inv H2...
  eapply wf_rcd_lookup in H...
  Case "S_RcdPerm".
  exists T0; split...
  eapply lookup_in_sublist...
  eapply wf_rcd_lookup in H0...
(*  
  inv H2... inv H3...
  repeat simpl in *.
  destruct (eq_id_dec i i0). subst... inv H3...
  inv H4... inv H3...
  destruct (eq_id_dec i i1). subst... simpl in H3. rewrite eq_id in H3... inv H3...
  simpl in H3. rewrite neq_id in H3...
  
  inv H1... inv H2... inv H4...
  inv H... eexists T0; split...
  inv H0; intros; eauto; try solve by inversion.
(*  induction H0; intros; eauto; try solve by inversion. *)
  inv H2...

  
  inv H3...
  destruct (eq_id_dec i i0)... subst...
  simpl in H8. rewrite neq_id in H8... simpl.
  destruct (eq_id_dec i i1)... subst... inv H5. rewrite neq_id in *...
  destruct (eq_id_dec i0 i1)... subst... simpl in H5. rewrite eq_id in H5...
  admit. admit. admit.
*)
Qed.

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |- v \in T ->
  Tlookup i T = Some Ti ->
(*  exists ti, tlookup i v = Some ti /\ empty |- ti \in Ti. *)
  exists ti S, tlookup i v = Some ti /\ empty |- ti \in S /\ S <: Ti.
Proof with eauto.
  intros v T i Ti Hval Htyp Hget.
  remember empty as Gamma.
  generalize dependent Ti.
  has_type_cases (induction Htyp) Case; intros; subst; try solve by inversion...
  Case "T_Sub".
    generalize H0; intro.
    eapply lookup_in_subtype in H0... inv H0. inv H2.
    edestruct (IHHtyp Hval)... inv H2... inv H4. inv H5.
    exists x0. exists x1. eauto.
  Case "T_RCons".
    simpl in Hget. simpl. destruct (eq_id_dec i i0).
    SCase "i is first".
      simpl. inversion Hget. subst.
      exists t... exists Ti... split... split... apply has_type__wf in Htyp1...
    SCase "get tail".
      apply IHHtyp2... inv Hval...
(*      destruct IHHtyp2 as [vi [Hgeti Htypi]]...
      inversion Hval... Qed.
*)
Qed.







(* ############################################### *)
(** ** Typing examples *)

Module Examples2.
Import Examples.

(** Do the following exercises after you have added product types to
    the language.  For each informal typing judgement, write it as a
    formal statement in Coq and prove it. *)

(** **** Exercise: 1 star, optional (typing_example_0) *)
(* empty |- ((\z:A.z), (\z:B.z)) 
          : (A->A * B->B) *)
Example typing_example_0 : forall A B,
  well_formed_ty A ->
  well_formed_ty B ->
  empty |- (tpair (tabs z A (tvar z)) (tabs z B (tvar z))) \in (TProd (TArrow A A) (TArrow B B)).
Proof with eauto.
  intros...
  apply T_Pair...
Qed.

(** **** Exercise: 2 stars, optional (typing_example_1) *)
(* empty |- (\x:(Top * B->B). x.snd) ((\z:A.z), (\z:B.z)) 
          : B->B *)
Example typing_example_1 : forall A B,
  well_formed_ty A ->
  well_formed_ty B ->
  empty |- (tapp (tabs x (TProd TTop (TArrow B B)) (tsnd (tvar x))) (tpair (tabs z A (tvar z)) (tabs z B (tvar z)))) \in (TArrow B B).
Proof with eauto.
  intros...
  eapply T_App. 
  eapply T_Abs...

  eapply T_Pair.
  eapply T_Sub...
  eapply T_Abs...
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (typing_example_2) *)
(* empty |- (\z:(C->C)->(Top * B->B). (z (\x:C.x)).snd)
              (\z:C->C. ((\z:A.z), (\z:B.z)))
          : B->B *)
Example typing_example_2 : forall A B C,
  well_formed_ty A ->
  well_formed_ty B ->
  well_formed_ty C ->
  empty |- (tapp (tabs z (TArrow (TArrow C C) (TProd TTop (TArrow B B)))
                 (tsnd (tapp (tvar z) (tabs x C (tvar x)))))
                 (tabs z (TArrow C C)
                       (tpair
                          (tabs z A (tvar z))
                          (tabs z B (tvar z))
                       )
                 )
           ) \in (TArrow B B).
Proof with eauto.
  intros...
  eapply T_App.
  eapply T_Abs...
  eapply T_Snd.
  eapply T_App. eapply T_Var...
  eapply T_Abs...
  eapply T_Abs...
  eapply T_Pair.
  eapply T_Sub...
  eapply T_Abs...
Qed.

(** [] *)

End Examples2.

(* ###################################################################### *)
(** * Properties *)

(** The fundamental properties of the system that we want to check are
    the same as always: progress and preservation.  Unlike the
    extension of the STLC with references, we don't need to change the
    _statements_ of these properties to take subtyping into account.
    However, their proofs do become a little bit more involved. *)

(* ###################################################################### *)
(** ** Inversion Lemmas for Subtyping *)

(** Before we look at the properties of the typing relation, we need
    to record a couple of critical structural properties of the subtype
    relation: 
       - [Bool] is the only subtype of [Bool]
       - every subtype of an arrow type is itself an arrow type. *)
    
(** These are called _inversion lemmas_ because they play the same
    role in later proofs as the built-in [inversion] tactic: given a
    hypothesis that there exists a derivation of some subtyping
    statement [S <: T] and some constraints on the shape of [S] and/or
    [T], each one reasons about what this derivation must look like to
    tell us something further about the shapes of [S] and [T] and the
    existence of subtype relations between their parts. *)

(** **** Exercise: 2 stars, optional (sub_inversion_Bool) *)
Lemma sub_inversion_Bool : forall U,
     U <: TBool ->
       U = TBool.
Proof with auto.
  intros U Hs.
  remember TBool as V.

  induction Hs; inv HeqV...
  apply IHHs2 in H. apply IHHs1 in H. subst. apply IHHs2...
  inv H0.
(*  inv H0. *)
  inv H3... inv H4...
  inv H6...
Qed.

Lemma sub_inversion_Top : forall T,
     TTop <: T ->
     T = TTop.
Proof with eauto.
  intros.
  remember (TTop) as rem.
  subtype_cases (induction H) Case; subst; simpl; eauto; try solve by inversion.
  exploit IHsubtype1; eauto; intro; subst...
Qed.

(*
Lemma sub_inversion_Unit : forall T,
     TUnit <: T ->
     T = TUnit.
Proof.
  intros.
  remember (TUnit) as rem.
  subtype_cases (induction H) Case; subst; simpl; eauto; try solve by inversion.
  exploit IHsubtype1; eauto; intro; subst...
Qed.
*)


(** **** Exercise: 3 stars, optional (sub_inversion_arrow) *)
Lemma sub_inversion_arrow : forall U V1 V2,
     U <: (TArrow V1 V2) ->
     exists U1, exists U2, 
       U = (TArrow U1 U2) /\ (V1 <: U1) /\ (U2 <: V2).
Proof with eauto.
  intros U V1 V2 Hs.
  remember (TArrow V1 V2) as V.
  generalize dependent V2. generalize dependent V1.

  subtype_cases (induction Hs) Case; intros; subst; try solve by inversion.
  inv H...
  exists V1; exists V2... 

  assert(G : S <: TArrow V1 V2) by eauto.
  generalize (IHHs2 V1 V2); intros T; exploit T; eauto; intro; clear T.
  inv H... inv H0... inv H. inv H1.
  generalize (IHHs1 x x0); intros T; exploit T; eauto; intro; clear T.
  inv H1. inv H2. inv H1. inv H3.
  exists x1; exists x2...
  inv HeqV...
Qed.


Lemma sub_inversion_prod : forall U V1 V2,
     U <: (TProd V1 V2) ->
     exists U1, exists U2, 
       U = (TProd U1 U2) /\ (U1 <: V1) /\ (U2 <: V2).
Proof with eauto.
  intros.
  remember (TProd V1 V2) as V.
  generalize dependent V2. generalize dependent V1.
  subtype_cases (induction H) Case; intros; subst; simpl; try solve by inversion.
  Case "S_Refl".
  inv H...
  exists V1; exists V2...
  edestruct IHsubtype2... inv H1. inv H2. inv H3.
  edestruct IHsubtype1... inv H3. inv H4. inv H5.
  exists x1; exists x2...
  Case "S_Prod".
  inv HeqV.
  inv H0; eexists... (* ???????????????? MAGIC????????????????? *)
Qed.


(** [] *)

(* ########################################## *)
(** ** Canonical Forms *)

(** We'll see first that the proof of the progress theorem doesn't
    change too much -- we just need one small refinement.  When we're
    considering the case where the term in question is an application
    [t1 t2] where both [t1] and [t2] are values, we need to know that
    [t1] has the _form_ of a lambda-abstraction, so that we can apply
    the [ST_AppAbs] reduction rule.  In the ordinary STLC, this is
    obvious: we know that [t1] has a function type [T11->T12], and
    there is only one rule that can be used to give a function type to
    a value -- rule [T_Abs] -- and the form of the conclusion of this
    rule forces [t1] to be an abstraction.

    In the STLC with subtyping, this reasoning doesn't quite work
    because there's another rule that can be used to show that a value
    has a function type: subsumption.  Fortunately, this possibility
    doesn't change things much: if the last rule used to show [Gamma
    |- t1 : T11->T12] is subsumption, then there is some
    _sub_-derivation whose subject is also [t1], and we can reason by
    induction until we finally bottom out at a use of [T_Abs].

    This bit of reasoning is packaged up in the following lemma, which
    tells us the possible "canonical forms" (i.e. values) of function
    type. *)

(** **** Exercise: 3 stars, optional (canonical_forms_of_arrow_types) *)
Lemma canonical_forms_of_arrow_types : forall Gamma s T1 T2,
  Gamma |- s \in (TArrow T1 T2) ->
  value s ->
  exists x, exists S1, exists s2,
     s = tabs x S1 s2.
Proof with eauto.
(*  
  t_cases (induction s) Case; intros; try solve by inversion.
  inv H...
  inv H... inv H1...
*)
  intros.
  remember (TArrow T1 T2) as T.
  generalize dependent T1.
  generalize dependent T2.
  induction H; intros; subst; simpl; eauto; try solve by inversion.
  apply sub_inversion_arrow in H2. inv H2. inv H3. inv H2.
  generalize (IHhas_type H0 x0 x); intro T; exploit T...
Qed.
(** [] *)

(** Similarly, the canonical forms of type [Bool] are the constants
    [true] and [false]. *)

Lemma canonical_forms_of_Bool : forall Gamma s,
  Gamma |- s \in TBool ->
  value s ->
  (s = ttrue \/ s = tfalse).
Proof with eauto.
  intros Gamma s Hty Hv.
  remember TBool as T.
  has_type_cases (induction Hty) Case; try solve by inversion...
  Case "T_Sub".
    subst. apply sub_inversion_Bool in H0. subst...
Qed.

(*
Lemma canonical_forms_of_pair_types : forall Gamma s T1 T2,
  Gamma |- s \in (TProd T1 T2) ->
  value s ->
  exists x y, s = (tpair x y).
*)
Lemma canonical_forms_of_pair_types : forall s T1 T2,
  empty |- s \in (TProd T1 T2) ->
  value s ->
  exists x y, s = (tpair x y).
Proof with eauto.
  intros.
  remember (empty) as Gamma.
  remember (TProd T1 T2) as rem.
  generalize dependent T1.
  generalize dependent T2.
  has_type_cases (induction H) Case; intros; subst; simpl; eauto; try solve by inversion...
  Case "T_Sub".
(*  
  remember (TProd T1 T2) as rem.
  clear IHhas_type. 
  subtype_cases (induction H2) SCase; subst; simpl; eauto; try solve by inversion...
  SCase "S_Refl". 
  SCase "S_Trans". admit.
  SCase "S_Prod". 
*)
  generalize H2; intro.
  apply sub_inversion_prod in H2. inv H2. inv H4. inv H2. inv H5. 
  subst...
  (*
  remember (empty) as Gamma.
  remember (TProd x x0) as rem.
  has_type_cases (induction H1) SCase; subst; simpl; eauto; try solve by inversion...
  
  inv H1. inv H5. inv H0. inv H0. admit.
  inv H0. exists t1; exists t2...
  inv H0. inv H0.
  inv H0.
*)
Qed.


(* ########################################## *)
(** ** Progress *)

(** The proof of progress proceeds like the one for the pure
    STLC, except that in several places we invoke canonical forms
    lemmas... *)

(** _Theorem_ (Progress): For any term [t] and type [T], if [empty |-
    t : T] then [t] is a value or [t ==> t'] for some term [t'].
 
    _Proof_: Let [t] and [T] be given, with [empty |- t : T].  Proceed
    by induction on the typing derivation.  

    The cases for [T_Abs], [T_Unit], [T_True] and [T_False] are
    immediate because abstractions, [unit], [true], and [false] are
    already values.  The [T_Var] case is vacuous because variables
    cannot be typed in the empty context.  The remaining cases are
    more interesting:

    - If the last step in the typing derivation uses rule [T_App],
      then there are terms [t1] [t2] and types [T1] and [T2] such that
      [t = t1 t2], [T = T2], [empty |- t1 : T1 -> T2], and [empty |-
      t2 : T1].  Moreover, by the induction hypothesis, either [t1] is
      a value or it steps, and either [t2] is a value or it steps.
      There are three possibilities to consider:

      - Suppose [t1 ==> t1'] for some term [t1'].  Then [t1 t2 ==> t1' t2] 
        by [ST_App1].

      - Suppose [t1] is a value and [t2 ==> t2'] for some term [t2'].
        Then [t1 t2 ==> t1 t2'] by rule [ST_App2] because [t1] is a
        value.

      - Finally, suppose [t1] and [t2] are both values.  By Lemma
        [canonical_forms_for_arrow_types], we know that [t1] has the
        form [\x:S1.s2] for some [x], [S1], and [s2].  But then
        [(\x:S1.s2) t2 ==> [x:=t2]s2] by [ST_AppAbs], since [t2] is a
        value.

    - If the final step of the derivation uses rule [T_If], then there
      are terms [t1], [t2], and [t3] such that [t = if t1 then t2 else
      t3], with [empty |- t1 : Bool] and with [empty |- t2 : T] and
      [empty |- t3 : T].  Moreover, by the induction hypothesis,
      either [t1] is a value or it steps.  
      
       - If [t1] is a value, then by the canonical forms lemma for
         booleans, either [t1 = true] or [t1 = false].  In either
         case, [t] can step, using rule [ST_IfTrue] or [ST_IfFalse].

       - If [t1] can step, then so can [t], by rule [ST_If].

    - If the final step of the derivation is by [T_Sub], then there is
      a type [S] such that [S <: T] and [empty |- t : S].  The desired
      result is exactly the induction hypothesis for the typing
      subderivation.
*)

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'. 
Proof with eauto.
  intros t T Ht.
  remember empty as Gamma.
  revert HeqGamma.
  has_type_cases (induction Ht) Case; 
    intros HeqGamma; subst...
  Case "T_Var".
    inversion H.
  Case "T_App".
    right.
    destruct IHHt1; subst...
    SCase "t1 is a value".
      destruct IHHt2; subst...
      SSCase "t2 is a value".
        destruct (canonical_forms_of_arrow_types empty t1 T1 T2)
          as [x [S1 [t12 Heqt1]]]...
        subst. exists ([x:=t2]t12)...
      SSCase "t2 steps".
        inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...
    SCase "t1 steps".
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...
  Case "T_If".
    right.
    destruct IHHt1.
    SCase "t1 is a value"...
      assert (t1 = ttrue \/ t1 = tfalse) 
        by (eapply canonical_forms_of_Bool; eauto).
      inversion H0; subst...
      inversion H. rename x into t1'. eauto.

  Case "T_Pair".
    destruct IHHt1; destruct IHHt2...
(*    exploit IHHt1; eauto; intro. exploit IHHt2; eauto; intro. *)
    inv H; inv H0...
    inv H. right. eexists...
    inv H. right. eexists...
  Case "T_Fst".
    destruct IHHt...
    apply canonical_forms_of_pair_types in Ht... inv Ht. inv H0. inv H.
    right. eexists...
    inv H. right. eexists... 
  Case "T_Snd".
    destruct IHHt...
    apply canonical_forms_of_pair_types in Ht... inv Ht. inv H0. inv H.
    right. eexists...
    inv H. right. eexists... 
  Case "T_Proj".
    destruct IHHt...
    right.
    apply lookup_field_in_value with (v:=t) in H... inv H. inv H1. inv H. inv H2.
    eexists...
    inv H0. right. eexists...
  Case "T_RCons".
    destruct IHHt1; destruct IHHt2...
    inv H2. right. eexists...
    inv H1. right. eexists...
    inv H1; inv H2. right. eexists...
Qed.

(* ########################################## *)
(** ** Inversion Lemmas for Typing *)

(** The proof of the preservation theorem also becomes a little more
    complex with the addition of subtyping.  The reason is that, as
    with the "inversion lemmas for subtyping" above, there are a
    number of facts about the typing relation that are "obvious from
    the definition" in the pure STLC (and hence can be obtained
    directly from the [inversion] tactic) but that require real proofs
    in the presence of subtyping because there are multiple ways to
    derive the same [has_type] statement.

    The following "inversion lemma" tells us that, if we have a
    derivation of some typing statement [Gamma |- \x:S1.t2 : T] whose
    subject is an abstraction, then there must be some subderivation
    giving a type to the body [t2]. *)

(** _Lemma_: If [Gamma |- \x:S1.t2 : T], then there is a type [S2]
    such that [Gamma, x:S1 |- t2 : S2] and [S1 -> S2 <: T].

    (Notice that the lemma does _not_ say, "then [T] itself is an arrow
    type" -- this is tempting, but false!)

    _Proof_: Let [Gamma], [x], [S1], [t2] and [T] be given as
     described.  Proceed by induction on the derivation of [Gamma |-
     \x:S1.t2 : T].  Cases [T_Var], [T_App], are vacuous as those
     rules cannot be used to give a type to a syntactic abstraction.

     - If the last step of the derivation is a use of [T_Abs] then
       there is a type [T12] such that [T = S1 -> T12] and [Gamma,
       x:S1 |- t2 : T12].  Picking [T12] for [S2] gives us what we
       need: [S1 -> T12 <: S1 -> T12] follows from [S_Refl].

     - If the last step of the derivation is a use of [T_Sub] then
       there is a type [S] such that [S <: T] and [Gamma |- \x:S1.t2 :
       S].  The IH for the typing subderivation tell us that there is
       some type [S2] with [S1 -> S2 <: S] and [Gamma, x:S1 |- t2 :
       S2].  Picking type [S2] gives us what we need, since [S1 -> S2
       <: T] then follows by [S_Trans]. *)

Lemma typing_inversion_abs : forall Gamma x S1 t2 T,
     Gamma |- (tabs x S1 t2) \in T ->
     (exists S2, (TArrow S1 S2) <: T
              /\ (extend Gamma x S1) |- t2 \in S2).
Proof with eauto.
  intros Gamma x S1 t2 T H.
  remember (tabs x S1 t2) as t.
  has_type_cases (induction H) Case; 
    inversion Heqt; subst; intros; try solve by inversion.
  Case "T_Abs".
    exists T12... split... apply S_Refl... econstructor... apply has_type__wf in H0...
  Case "T_Sub".
    destruct IHhas_type as [S2 [Hsub Hty]]...
  Qed.

(** Similarly... *)

Lemma typing_inversion_var : forall Gamma x T,
  Gamma |- (tvar x) \in T ->
  exists S,
    Gamma x = Some S /\ S <: T.
Proof with eauto.
  intros Gamma x T Hty.
  remember (tvar x) as t.
  has_type_cases (induction Hty) Case; intros; 
    inversion Heqt; subst; try solve by inversion.
  Case "T_Var".
    exists T...
  Case "T_Sub".
    destruct IHHty as [U [Hctx HsubU]]... Qed.

Lemma typing_inversion_app : forall Gamma t1 t2 T2,
  Gamma |- (tapp t1 t2) \in T2 ->
  exists T1,
    Gamma |- t1 \in (TArrow T1 T2) /\
    Gamma |- t2 \in T1.
Proof with eauto.
  intros Gamma t1 t2 T2 Hty.
  remember (tapp t1 t2) as t.
  has_type_cases (induction Hty) Case; intros;
    inversion Heqt; subst; try solve by inversion.
  Case "T_App".
    exists T1...
  Case "T_Sub".
(*    provided script broken *)  
(*    destruct IHHty as [U1 [Hty1 Hty2]]... *)
    destruct IHHty as [U1 [Hty1 Hty2]]...
    exists U1. split... apply T_Sub with (S:=(TArrow U1 S))...
    econstructor... apply has_type__wf in Hty2...
    eapply S_Arrow... eapply has_type__wf in Hty2... 
Qed.

Lemma typing_inversion_true : forall Gamma T,
  Gamma |- ttrue \in T ->
  TBool <: T.
Proof with eauto.
  intros Gamma T Htyp. remember ttrue as tu.
  has_type_cases (induction Htyp) Case;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_false : forall Gamma T,
  Gamma |- tfalse \in T ->
  TBool <: T.
Proof with eauto.
  intros Gamma T Htyp. remember tfalse as tu.
  has_type_cases (induction Htyp) Case;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_if : forall Gamma t1 t2 t3 T,
  Gamma |- (tif t1 t2 t3) \in T ->
  Gamma |- t1 \in TBool 
  /\ Gamma |- t2 \in T
  /\ Gamma |- t3 \in T.
Proof with eauto.
  intros Gamma t1 t2 t3 T Hty.
  remember (tif t1 t2 t3) as t.
  has_type_cases (induction Hty) Case; intros;
    inversion Heqt; subst; try solve by inversion.
  Case "T_If".
    auto.
  Case "T_Sub".
(*    provided script broken *)
(*    destruct (IHHty H0) as [H1 [H2 H3]]... *)
  destruct IHHty... 
  inv H3.
  split...
Qed.

Lemma typing_inversion_unit : forall Gamma T,
  Gamma |- tunit \in T ->
    TUnit <: T.
Proof with eauto.
  intros Gamma T Htyp. remember tunit as tu.
  has_type_cases (induction Htyp) Case;
    inversion Heqtu; subst; intros...
Qed.

Lemma typing_inversion_pair : forall Gamma t1 t2 T,
  Gamma |- tpair t1 t2 \in T ->
  (exists S1 S2,
    Gamma |- t1 \in S1 /\
    Gamma |- t2 \in S2
(* below is crucial *)
                    /\
    TProd S1 S2 <: T
  ).
                           (*
  exists T1 T2, T = TProd T1 T2 /\
  (exists S1 S2,
    Gamma |- t1 \in S1 /\
    Gamma |- t2 \in S2)
.
*)
Proof with eauto.
  intros Gamma t1 t2 T Htyp. remember (tpair t1 t2) as tu.
  has_type_cases (induction Htyp) Case;
    inversion Heqtu; subst; intros...
  (*
  clear H1. destruct IHHtyp... inv H1... inv H2... inv H3... inv H1... inv H2...
  eexists
*)
  destruct IHHtyp... clear H1.
  inv H2. inv H1. inv H3.
  exists x; exists x0...

  exists T1; exists T2... split... split...
  apply S_Refl. apply has_type__wf in Htyp2. apply has_type__wf in Htyp1...
Qed.
(*  
Lemma typing_inversion_pair : forall Gamma t1 t2 T,
  Gamma |- tpair t1 t2 \in T ->
  exists T1 T2, Gamma |- tpair t1 t2 \in TProd T1 T2.
Proof with eauto.
  intros Gamma t1 t2 T Htyp. remember (tpair t1 t2) as tu.
  has_type_cases (induction Htyp) Case;
    inversion Heqtu; subst; intros...  
Qed.
*)

Lemma typing_inversion_fst : forall Gamma t T,
  Gamma |- tfst t \in T ->
  (exists S1 S2,
    Gamma |- t \in (TProd S1 S2) /\
    S1 <: T
  ).  
Proof with eauto.
  intros Gamma t T Htyp. remember (tfst t) as rem.
  has_type_cases (induction Htyp) Case;
    inversion Heqrem; subst; intros...
  clear H1. destruct IHHtyp... inv H1. inv H2.
  exists x; exists x0...

  exists T1; exists T2; split...
  apply has_type__wf in Htyp; inv Htyp...
Qed.

Lemma typing_inversion_snd : forall Gamma t T,
  Gamma |- tsnd t \in T ->
  (exists S1 S2,
    Gamma |- t \in (TProd S1 S2) /\
    S2 <: T
  ).  
Proof with eauto.
  intros Gamma t T Htyp. remember (tsnd t) as rem.
  has_type_cases (induction Htyp) Case;
    inversion Heqrem; subst; intros...
  clear H1. destruct IHHtyp... inv H1. inv H2.
  exists x; exists x0...

  exists T1; exists T2; split...
  apply has_type__wf in Htyp; inv Htyp...
Qed.

Lemma typing_inversion_tproj : forall Gamma tr i Ti,
  Gamma |- tproj tr i \in Ti ->
  exists Tr S,
    Tlookup i Tr = Some S /\
    S <: Ti /\
    Gamma |- tr \in Tr.
Proof with eauto.
  intros Gamma tr i Ti Htyp. remember (tproj tr i) as rem.
  has_type_cases (induction Htyp) Case;
    inversion Heqrem; subst; intros...
  destruct IHHtyp...
  inv H2. inv H3. inv H4.
  exists x; exists x0; split... 

  exists Tr; exists Ti; split... split...
  apply wf_rcd_lookup in H... apply has_type__wf in Htyp...
Qed.

Lemma typing_inversion_trnil : forall Gamma T,
  Gamma |- trnil \in T ->
  TRNil <: T.
Proof with eauto.
  intros Gamma T Htyp. remember (trnil) as rem.
  has_type_cases (induction Htyp) Case;
    inversion Heqrem; subst; intros...
Qed.

Lemma typing_inversion_trcons : forall Gamma i t tr U,
  Gamma |- trcons i t tr \in U ->
  (exists T Tr,
    Gamma |- t \in T /\
    Gamma |- tr \in Tr /\
    record_ty Tr /\
    record_tm tr /\
    TRCons i T Tr <: U).
Proof with eauto.
  intros Gamma i t tr U Htyp. remember (trcons i t tr) as rem.
  has_type_cases (induction Htyp) Case;
    inversion Heqrem; subst; intros...
  destruct IHHtyp... inv H2. inv H3. inv H4. inv H5. inv H6.
  exists x; exists x0... split...
  exists T; exists Tr... split... split... split... split... apply S_Refl.
  constructor...
  apply has_type__wf in Htyp1...
  apply has_type__wf in Htyp2...
Qed.

(** The inversion lemmas for typing and for subtyping between arrow
    types can be packaged up as a useful "combination lemma" telling
    us exactly what we'll actually require below. *)

Lemma abs_arrow : forall x S1 s2 T1 T2, 
  empty |- (tabs x S1 s2) \in (TArrow T1 T2) ->
     T1 <: S1 
  /\ (extend empty x S1) |- s2 \in T2.
Proof with eauto.
  intros x S1 s2 T1 T2 Hty.
  apply typing_inversion_abs in Hty.
  inversion Hty as [S2 [Hsub Hty1]].
  apply sub_inversion_arrow in Hsub.
  inversion Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
  inversion Heq; subst...
  (* provided script broken *)
  split... (* apply T_Sub with (S:=U2)... *) eapply T_Sub...
  apply has_subtype__wf in Hsub2. inv Hsub2...
  (*
  inv Hty. inv Hsub. inv H0. inv H1. inv H. inv H2.
  admit.
*)
(*  
has_type__wf:
  forall (Gamma : context) (t : tm) (T : ty),
  Gamma |- t \in T -> well_formed_ty T
wf_rcd_lookup:
  forall (i : id) (T Ti : ty),
  well_formed_ty T -> Tlookup i T = Some Ti -> well_formed_ty Ti
*)
Qed.

(* ########################################## *)
(** ** Context Invariance *)

(** The context invariance lemma follows the same pattern as in the
    pure STLC. *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x (tabs y T11 t12)
  | afi_if1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_if3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif t1 t2 t3)
  | afi_pair1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tpair t1 t2)
  | afi_pair2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tpair t1 t2)
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x (tfst t)
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x (tsnd t)
  | afi_proj : forall x tr i,
      appears_free_in x tr ->
      appears_free_in x (tproj tr i)
(*
  | afi_rcons_new : forall x i t tr,
      appears_free_in x t ->
      appears_free_in x (trcons i t tr)
  | afi_rcons_already : forall x i t tr,
      appears_free_in x tr ->
      appears_free_in x (trcons i t tr)
*)
  | afi_rcons : forall x i t tr,
      appears_free_in x tr \/ appears_free_in x t ->
      appears_free_in x (trcons i t tr)
.

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     Gamma' |- t \in S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  has_type_cases (induction H) Case; 
    intros Gamma' Heqv...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs... apply IHhas_type. intros x0 Hafi.
    unfold extend. destruct (eq_id_dec x x0)...

  Case "T_App".
    apply T_App with T1...
  Case "T_If".
    apply T_If...
  Case "T_Pair".
    apply T_Pair...
  Case "T_RCons".
    apply T_RCons... 
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  has_type_cases (induction Htyp) Case; 
      subst; inversion Hafi; subst...
  Case "T_Abs".
(*    destruct (IHHtyp H4) as [T Hctx]. exists T. *)  
    destruct (IHHtyp H5) as [T Hctx]. exists T.
    unfold extend in Hctx. rewrite neq_id in Hctx...
(* provided  script broken *)
  Case "T_RCons".
    inv H3. eapply IHHtyp2... eapply IHHtyp1...
Qed.

(* ########################################## *)
(** ** Substitution *)

(** The _substitution lemma_ is proved along the same lines as
    for the pure STLC.  The only significant change is that there are
    several places where, instead of the built-in [inversion] tactic,
    we need to use the inversion lemmas that we proved above to
    extract structural information from assumptions about the
    well-typedness of subterms. *)


(*
Lemma extend_var_subtype : forall Gamma S x U y,
  extend Gamma x U |- tvar y \in S ->
  x <> y ->
  Gamma |- tvar y \in S.
Proof with eauto.
  intros.

  remember (Gamma) as gam.
  generalize dependent Gamma.

  has_type_cases (induction H) Case; intros; try solve by inversion.
  apply T_Var...
Abort.
*)


(*
  S : ty
  Htypt : extend Gamma x U |- tvar y \in S
  T : ty
  n : x <> y
  Hctx : Gamma y = Some T
  Hsub : T <: S
  ============================
   Gamma |- tvar y \in S
*)

(*
Lemma has_type__wf_abs : forall S Gamma x T t,
  Gamma |- tabs x T t \in S ->
  well_formed_ty T.
Proof with eauto.
  induction S; intros; try solve by inversion.

  intros.
  (*
  remember Gamma as gam.
  generalize dependent Gamma.
*)
(*
  remember (tabs x T t) as tm.
  generalize dependent x.
  generalize dependent T.
  generalize dependent t.
*)
  has_type_cases (induction H) Case; intros;
  subst; eauto; try solve by inversion.

  inv Heqtm.
Qed.
*)

(*
  Case := "tabs" : String.string
  x : id
  U : ty
  v : tm
  y : id
  T1 : ty
  t0 : tm
  Htypv : empty |- v \in U
  IHt : forall (Gamma : context) (S : ty),
        extend Gamma x U |- t0 \in S -> Gamma |- [x := v]t0 \in S
  Gamma : context
  S : ty
  Htypt : extend Gamma x U |- tabs y T1 t0 \in S
  T2 : ty
  Hsub : TArrow T1 T2 <: S
  Htypt2 : extend (extend Gamma x U) y T1 |- t0 \in T2
  ============================
   well_formed_ty T1


     : forall (Gamma : context) (t : tm) (T : ty),
       Gamma |- t \in T -> well_formed_ty T

T_Abs:
  forall (Gamma : context) (x : id) (T11 T12 : ty) (t12 : tm),
  well_formed_ty T11 ->
  extend Gamma x T11 |- t12 \in T12 ->
  Gamma |- tabs x T11 t12 \in TArrow T11 T12
*)


Lemma subst_keeps_record_tm : forall x v t,
  record_tm t ->
  record_tm ([x := v] t).
Proof with eauto.
  induction t; intros; simpl; eauto; try solve by inversion...
Qed.

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (extend Gamma x U) |- t \in S  ->
     empty |- v \in U   ->
     Gamma |- ([x:=v]t) \in S.
Proof with eauto. (* using has_type__wf, has_subtype__wf.  too slow*)
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent S. generalize dependent Gamma.
  t_cases (induction t) Case; intros; simpl.
  Case "tvar".
    rename i into y.
    destruct (typing_inversion_var _ _ _ Htypt) 
        as [T [Hctx Hsub]].
    unfold extend in Hctx.
    destruct (eq_id_dec x y)...
    SCase "x=y".
      subst.
      inversion Hctx; subst. clear Hctx.
      apply context_invariance with empty...
      (* provided script broken *)
      eapply T_Sub... apply has_type__wf in Htypt... 
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) 
          as [T' HT']...
      (* provided script broken *)
      eapply T_Sub... apply has_type__wf in Htypt... 
      inversion HT'.
    SCase "x<>y".
      apply T_Sub with (T)... apply has_subtype__wf in Hsub. inv Hsub...
      econstructor... apply has_subtype__wf in Hsub. inv Hsub...
(*      
      generalize Htypt; intro G.
      apply typing_inversion_var in G. inv G. inv H.
      unfold extend in H0. rewrite neq_id in H0...

      rewrite Hctx in H0. inv H0...
      
      inv Htypt. unfold extend in H0. rewrite neq_id in H0...
      apply T_Sub with (S0)... inv H0.
      unfold extend in H3. rewrite neq_id in H3...
*)

  Case "tapp".
    destruct (typing_inversion_app _ _ _ _ Htypt) 
        as [T1 [Htypt1 Htypt2]].
    eapply T_App...
  Case "tabs".
    rename i into y. rename t into T1.
    destruct (typing_inversion_abs _ _ _ _ _ Htypt) 
      as [T2 [Hsub Htypt2]].
    apply T_Sub with (TArrow T1 T2)... apply has_type__wf in Htypt...
    apply T_Abs...
    apply has_subtype__wf in Hsub. inv Hsub. inv H...

(*
    apply canonical_forms_of_arrow_types in Hsub.
    
     : forall (s : tm) (T1 T2 : ty),
       empty |- s \in TProd T1 T2 ->
       value s -> exists x y : tm, s = tpair x y

       U <: TArrow V1 V2 ->
       exists U1 U2 : ty, U = TArrow U1 U2 /\ V1 <: U1 /\ U2 <: V2
*)
                                                                  
    destruct (eq_id_dec x y).
    SCase "x=y".
      eapply context_invariance...
      subst.
      intros x Hafi. unfold extend.
      destruct (eq_id_dec y x)...
    SCase "x<>y".
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      destruct (eq_id_dec y z)...
      subst. rewrite neq_id... 
  Case "ttrue".
      assert (TBool <: S) 
        by apply (typing_inversion_true _ _  Htypt)...
      eapply T_Sub... apply has_type__wf in Htypt... 
  Case "tfalse".
      assert (TBool <: S) 
        by apply (typing_inversion_false _ _  Htypt)...
      eapply T_Sub... apply has_type__wf in Htypt... 
  Case "tif".
    assert ((extend Gamma x U) |- t1 \in TBool 
            /\ (extend Gamma x U) |- t2 \in S
            /\ (extend Gamma x U) |- t3 \in S) 
      by apply (typing_inversion_if _ _ _ _ _ Htypt).
    inversion H as [H1 [H2 H3]].
    apply IHt1 in H1. apply IHt2 in H2. apply IHt3 in H3.
    auto.
  Case "tunit".
    assert (TUnit <: S) 
      by apply (typing_inversion_unit _ _  Htypt)...
    inv Htypt...
  Case "tpair".
    generalize Htypt; intro G.
    apply typing_inversion_pair in G.
    inv G. inv H. inv H0. inv H1.

    apply IHt1 in H. apply IHt2 in H0.
    inv Htypt...
(*             
    apply has_type__wf in Htypt.
    inv H0. inv H1. inv H3. inv H5.

       empty |- s \in TProd T1 T2 ->
       value s -> exists x y : tm, s = tpair x y    
    econstructor. auto.
    eapply T_Pair...
    econstructor...
*)
  Case "tfst".
    generalize Htypt; intro G.
    apply typing_inversion_fst in G.
    inv G. inv H. inv H0.
    inv Htypt...
  Case "tsnd".
    generalize Htypt; intro G.
    apply typing_inversion_snd in G.
    inv G. inv H. inv H0.
    inv Htypt...
  Case "tproj".
    generalize Htypt; intro G.
    apply typing_inversion_tproj in G.
    inv G. inv H. inv H0. inv H1.
    econstructor...
    apply has_type__wf in Htypt...
  Case "trnil".
    generalize Htypt; intro G.
    apply typing_inversion_trnil in G.
    econstructor... apply has_type__wf in Htypt...
  Case "trcons".
    generalize Htypt; intro G.
    apply typing_inversion_trcons in G.
    inv G. inv H. inv H0. inv H1. inv H2. inv H3.
    econstructor. apply has_subtype__wf in H4... inv H4...
    constructor...
    generalize (IHt2 Gamma x1 H0); intro G.
    eapply subst_keeps_record_tm in H2...
    auto.
Qed.

(* ########################################## *)
(** ** Preservation *)

(** The proof of preservation now proceeds pretty much as in earlier
    chapters, using the substitution lemma at the appropriate point
    and again using inversion lemmas from above to extract structural
    information from typing assumptions. *)

(** _Theorem_ (Preservation): If [t], [t'] are terms and [T] is a type
    such that [empty |- t : T] and [t ==> t'], then [empty |- t' :
    T].

    _Proof_: Let [t] and [T] be given such that [empty |- t : T].  We
    proceed by induction on the structure of this typing derivation,
    leaving [t'] general.  The cases [T_Abs], [T_Unit], [T_True], and
    [T_False] cases are vacuous because abstractions and constants
    don't step.  Case [T_Var] is vacuous as well, since the context is
    empty.

     - If the final step of the derivation is by [T_App], then there
       are terms [t1] and [t2] and types [T1] and [T2] such that 
       [t = t1 t2], [T = T2], [empty |- t1 : T1 -> T2], and 
       [empty |- t2 : T1].

       By the definition of the step relation, there are three ways
       [t1 t2] can step.  Cases [ST_App1] and [ST_App2] follow
       immediately by the induction hypotheses for the typing
       subderivations and a use of [T_App].

       Suppose instead [t1 t2] steps by [ST_AppAbs].  Then [t1 =
       \x:S.t12] for some type [S] and term [t12], and [t' =
       [x:=t2]t12].
       
       By lemma [abs_arrow], we have [T1 <: S] and [x:S1 |- s2 : T2].
       It then follows by the substitution lemma 
       ([substitution_preserves_typing]) that [empty |- [x:=t2]
       t12 : T2] as desired.

      - If the final step of the derivation uses rule [T_If], then
        there are terms [t1], [t2], and [t3] such that [t = if t1 then
        t2 else t3], with [empty |- t1 : Bool] and with [empty |- t2 :
        T] and [empty |- t3 : T].  Moreover, by the induction
        hypothesis, if [t1] steps to [t1'] then [empty |- t1' : Bool].
        There are three cases to consider, depending on which rule was
        used to show [t ==> t'].

           - If [t ==> t'] by rule [ST_If], then [t' = if t1' then t2
             else t3] with [t1 ==> t1'].  By the induction hypothesis,
             [empty |- t1' : Bool], and so [empty |- t' : T] by [T_If].
          
           - If [t ==> t'] by rule [ST_IfTrue] or [ST_IfFalse], then
             either [t' = t2] or [t' = t3], and [empty |- t' : T]
             follows by assumption.

     - If the final step of the derivation is by [T_Sub], then there
       is a type [S] such that [S <: T] and [empty |- t : S].  The
       result is immediate by the induction hypothesis for the typing
       subderivation and an application of [T_Sub].  [] *)

(*
  Case := "T_Fst" : String.string
  T1 : ty
  T2 : ty
  t' : tm
  v2 : tm
  H0 : value t'
  H1 : value v2
  HE : tfst (tpair t' v2) ==> t'
  IHHT : forall t'0 : tm,
         empty = empty -> tpair t' v2 ==> t'0 -> empty |- t'0 \in TProd T1 T2
  S : ty
  H : well_formed_ty (TProd T1 T2)
  H3 : S <: TProd T1 T2
  x : ty
  x0 : ty
  H4 : empty |- t' \in x
  H2 : empty |- v2 \in x0
  H6 : TProd x x0 <: S
  G : TProd x x0 <: TProd T1 T2
  ============================
   empty |- t' \in T1
*)

Lemma prod_order : forall T1 T2 U1 U2,
(*
  TProd T1 T2 <: TProd U1 U2 ->
  T1 <: U1 /\ T2 <: U2.
*)
  well_formed_ty (TProd T1 T2) ->
  well_formed_ty (TProd U1 U2) ->
  TProd T1 T2 <: TProd U1 U2 ->
  T1 <: U1 /\ T2 <: U2.
Proof with eauto.
(*  
  T_cases (induction T1) Case;
  intros; subst; simpl; eauto; try solve by inversion...
  inv H1... split... inv H... admit. admit.
*)
  intros.
  generalize H1; intro G.
  apply sub_inversion_prod in G...
  inv G. inv H2. inv H3. inv H4.
  inv H2...
(*  
  intros.
  remember (TProd U1 U2) as rem.
  generalize dependent T1.
  generalize dependent T2.
  generalize dependent U1.
  generalize dependent U2.
  induction H0; intros; subst; simpl; eauto; try solve by inversion.
  inv Heqrem...
  
  intros.
  remember (TProd T1 T2) as rem1.
  remember (TProd U1 U2) as rem2.  
  generalize dependent T1.
  generalize dependent T2.
  generalize dependent U1.
  generalize dependent U2.  
  subtype_cases (induction H1) Case;
    intros; subst; simpl; eauto; try solve by inversion...
  inv Heqrem1... inv H...
*)
Qed.
  
Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  remember empty as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  has_type_cases (induction HT) Case; 
    intros t' HeqGamma HE; subst; inversion HE; subst...
  Case "T_App".
    inversion HE; subst...
    SCase "ST_AppAbs".
      destruct (abs_arrow _ _ _ _ _ HT1) as [HA1 HA2].
      apply substitution_preserves_typing with T...
      econstructor. apply has_subtype__wf in HA1... inv HA1... apply HT2. auto.
  Case "T_Fst".
    inv HT... apply typing_inversion_pair in H2... inv H2. inv H4. inv H2. inv H5.
    assert(G : TProd x x0 <: TProd T1 T2) by eauto.
    apply prod_order in G. inv G.
    econstructor... apply has_subtype__wf in H5. inv H5...
    econstructor; eauto using has_type__wf. apply has_subtype__wf in G. inv G...
  Case "T_Snd".
    inv HT... apply typing_inversion_pair in H2... inv H2. inv H4. inv H2. inv H5.
    assert(G : TProd x x0 <: TProd T1 T2) by eauto.
    apply prod_order in G. inv G.
    econstructor... apply has_subtype__wf in H7. inv H7...
    econstructor; eauto using has_type__wf. apply has_subtype__wf in G. inv G...
  Case "T_Proj".
    apply lookup_field_in_value with (T:=Tr) (i:=i) (Ti:= Ti) in H2...
    inv H2. inv H0. inv H1. inv H2.
    rewrite H4 in H0. inv H0. eapply T_Sub...
    apply has_subtype__wf in H3. inv H3...
  Case "T_RCons".
    constructor...
    eapply step_preserves_record_tm...
Qed.
    
(** ** Records, via Products and Top *)

(** This formalization of the STLC with subtyping has omitted record
    types, for brevity.  If we want to deal with them more seriously,
    we have two choices.  

    First, we can treat them as part of the core language, writing
    down proper syntax, typing, and subtyping rules for them.  Chapter
    [RecordSub] shows how this extension works.

    On the other hand, if we are treating them as a derived form that
    is desugared in the parser, then we shouldn't need any new rules:
    we should just check that the existing rules for subtyping product
    and [Unit] types give rise to reasonable rules for record
    subtyping via this encoding. To do this, we just need to make one
    small change to the encoding described earlier: instead of using
    [Unit] as the base case in the encoding of tuples and the "don't
    care" placeholder in the encoding of records, we use [Top].  So:
<<
    {a:Nat, b:Nat} ----> {Nat,Nat}       i.e. (Nat,(Nat,Top))
    {c:Nat, a:Nat} ----> {Nat,Top,Nat}   i.e. (Nat,(Top,(Nat,Top)))
>>
    The encoding of record values doesn't change at all.  It is
    easy (and instructive) to check that the subtyping rules above are
    validated by the encoding.  For the rest of this chapter, we'll
    follow this encoding-based approach. *)

(* ###################################################### *)
(** ** Exercises *)

(** **** Exercise: 2 stars (variations) *)
(** Each part of this problem suggests a different way of
    changing the definition of the STLC with Unit and
    subtyping.  (These changes are not cumulative: each part
    starts from the original language.)  In each part, list which
    properties (Progress, Preservation, both, or neither) become
    false.  If a property becomes false, give a counterexample.
    - Suppose we add the following typing rule:
                            Gamma |- t : S1->S2
                    S1 <: T1      T1 <: S1     S2 <: T2
                    -----------------------------------              (T_Funny1)
                            Gamma |- t : T1->T2

    - Suppose we add the following reduction rule:
                             ------------------                     (ST_Funny21)
                             unit ==> (\x:Top. x)

    - Suppose we add the following subtyping rule:
                               --------------                        (S_Funny3)
                               Unit <: Top->Top

    - Suppose we add the following subtyping rule:
                               --------------                        (S_Funny4)
                               Top->Top <: Unit

    - Suppose we add the following evaluation rule:
                             -----------------                      (ST_Funny5)
                             (unit t) ==> (t unit)

    - Suppose we add the same evaluation rule _and_ a new typing rule:
                             -----------------                      (ST_Funny5)
                             (unit t) ==> (t unit)

                           ----------------------                    (T_Funny6)
                           empty |- Unit : Top->Top

    - Suppose we _change_ the arrow subtyping rule to:
                          S1 <: T1       S2 <: T2
                          -----------------------                    (S_Arrow')
                               S1->S2 <: T1->T2

[]
*) 
(* Gonna skip this *)

(* ###################################################################### *)
(** * Exercise: Adding Products *)

(** **** Exercise: 4 stars, optional (products) *)
(** Adding pairs, projections, and product types to the system we have
    defined is a relatively straightforward matter.  Carry out this
    extension:

    - Add constructors for pairs, first and second projections, and
      product types to the definitions of [ty] and [tm].  (Don't
      forget to add corresponding cases to [T_cases] and [t_cases].)

    - Extend the well-formedness relation in the obvious way.

    - Extend the operational semantics with the same reduction rules
      as in the last chapter.

    - Extend the subtyping relation with this rule:
                        S1 <: T1     S2 <: T2
                        ---------------------                     (Sub_Prod)
                          S1 * S2 <: T1 * T2
    - Extend the typing relation with the same rules for pairs and
      projections as in the last chapter.

    - Extend the proofs of progress, preservation, and all their
      supporting lemmas to deal with the new constructs.  (You'll also
      need to add some completely new lemmas.)  []
*)


(* $Date: 2013-12-05 11:55:09 -0500 (Thu, 05 Dec 2013) $ *)

