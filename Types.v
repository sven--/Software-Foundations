(** * Types: Type Systems *)

Require Export Smallstep.
Ltac inv H := inversion H; subst; clear H.

Hint Constructors multi.  

(** Our next major topic is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of a very simple
    language with just booleans and numbers, to introduce the basic
    ideas of types, typing rules, and the fundamental theorems about
    type systems: _type preservation_ and _progress_.  Then we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Coq). *)

(* ###################################################################### *)
(** * Typed Arithmetic Expressions *)

(** To motivate the discussion of type systems, let's begin as
    usual with an extremely simple toy language.  We want it to have
    the potential for programs "going wrong" because of runtime type
    errors, so we need something a tiny bit more complex than the
    language of constants and addition that we used in chapter
    [Smallstep]: a single kind of data (just numbers) is too simple,
    but just two kinds (numbers and booleans) already gives us enough
    material to tell an interesting story.

    The language definition is completely routine.  The only thing to
    notice is that we are _not_ using the [asnum]/[aslist] trick that
    we used in chapter [HoareList] to make all the operations total by
    forcibly coercing the arguments to [+] (for example) into numbers.
    Instead, we simply let terms get stuck if they try to use an
    operator with the wrong kind of operands: the [step] relation
    doesn't relate them to anything. *)

(* ###################################################################### *)
(** ** Syntax *)

(** Informally:
    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t
    Formally:
*)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.

(** _Values_ are [true], [false], and numeric values... *)

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : forall t, nvalue t -> nvalue (tsucc t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.  
Hint Unfold extend.

(* ###################################################################### *)
(** ** Operational Semantics *)

(** Informally: *)
(**
                    ------------------------------                  (ST_IfTrue)
                    if true then t1 else t2 ==> t1

                   -------------------------------                 (ST_IfFalse)
                   if false then t1 else t2 ==> t2

                              t1 ==> t1'
                      -------------------------                         (ST_If)
                      if t1 then t2 else t3 ==>
                        if t1' then t2 else t3

                              t1 ==> t1'
                         --------------------                         (ST_Succ)
                         succ t1 ==> succ t1'

                             ------------                         (ST_PredZero)
                             pred 0 ==> 0

                           numeric value v1
                        ---------------------                     (ST_PredSucc)
                        pred (succ v1) ==> v1

                              t1 ==> t1'
                         --------------------                         (ST_Pred)
                         pred t1 ==> pred t1'

                          -----------------                     (ST_IszeroZero)
                          iszero 0 ==> true

                           numeric value v1
                      --------------------------                (ST_IszeroSucc)
                      iszero (succ v1) ==> false

                              t1 ==> t1'
                       ------------------------                     (ST_Iszero)
                       iszero t1 ==> iszero t1'
*)

(** Formally: *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" 
  | Case_aux c "ST_Succ" | Case_aux c "ST_PredZero"
  | Case_aux c "ST_PredSucc" | Case_aux c "ST_Pred" 
  | Case_aux c "ST_IszeroZero" | Case_aux c "ST_IszeroSucc"
  | Case_aux c "ST_Iszero" ].

Hint Constructors step.
(** Notice that the [step] relation doesn't care about whether
    expressions make global sense -- it just checks that the operation
    in the _next_ reduction step is being applied to the right kinds
    of operands.  

    For example, the term [succ true] (i.e., [tsucc ttrue] in the
    formal syntax) cannot take a step, but the almost as obviously
    nonsensical term
       succ (if true then true else true) 
    can take a step (once, before becoming stuck). *)

(* ###################################################################### *)
(** ** Normal Forms and Values *)

(** The first interesting thing about the [step] relation in this
    language is that the strong progress theorem from the Smallstep
    chapter fails!  That is, there are terms that are normal
    forms (they can't take a step) but not values (because we have not
    included them in our definition of possible "results of
    evaluation").  Such terms are _stuck_. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(** **** Exercise: 2 stars (some_term_is_stuck) *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tif tzero tzero tzero).
  split.
  unfold normal_form, not.
  intros.
  inv H.
  inv H0.
  inv H4.

  unfold not.
  intros.
  inv H.
  inv H0.
  inv H0.
Qed.

(** However, although values and normal forms are not the same in this
    language, the former set is included in the latter.  This is
    important because it shows we did not accidentally define things
    so that some value could still take a step. *)

(** **** Exercise: 3 stars, advanced (value_is_nf) *)
(** Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways. *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros.
  inv H;
  unfold normal_form, not;
  intros;
  inv H. inv H0. inv H1. inv H1.
  generalize dependent x.
  induction H0; intros.
  inv H1.
  inv H1.
  generalize (IHnvalue t1'); intro T.
  apply T. auto.
Qed.


(** **** Exercise: 3 stars, optional (step_deterministic) *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)


Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R, H2: ?P ?X |- _ => 
         rewrite (H1 X H2) in * 
  end.
Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2. 
Ltac find_rwinv :=
  match goal with
    H1: ?E = true, H2: ?E = false |- _ => rwinv H1 H2
  end.

Ltac value_pre_fail :=
  match goal with
    H1: ?E ==> _, H2: value ?E |- _ => inv H1
  end.

Ltac value_pre :=
  match goal with
    | H1: ttrue ==> _             |- _ => inv H1
    | H1: tfalse ==> _            |- _ => inv H1
    | H1: tzero ==> _             |- _ => inv H1
  (*  | H1: tsucc ?t ==> _         |- _ => inv H1 *)
                                              (*
    | H1: ?t ==> _, H2: nvalue ?t |- _ => inv H2; inv H1
    | H1: ?t ==> _, H2: bvalue ?t |- _ => inv H2; inv H1
*)
  end.
(*
Ltac value_inv :=
  match goal with
    | H1: nvalue ?t |- _ => inv H1
    | H1: bvalue ?t |- _ => inv H1
  end.
*)
(*
Hint Constructors nvalue.
Hint Constructors bvalue.
*)
(*
Ltac apply_subst :=
  match goal with
    | H1 : forall x, ?P x -> ?L = ?R, H2: ?P
*)
(*
Lemma nvalue_succ_pred : (forall t1 t2,
  nvalue t1 ->
  tsucc t1 ==> t2 ->
  t1 = tpred t2).
Proof.
(*
  unfold not; intros.
  generalize (H tzero (tsucc tzero)); intro T.
  assert(G : nvalue tzero) by constructor.
  apply T in G. inv G.
  inv G.
*)
  
  intros. generalize dependent t2.
  induction H; intros.
  inv H0. inv H1.
  inv H0. generalize (IHnvalue t1' H2); intro T.
  rewrite T.
  inv H2.
  inv H.
(*
   tsucc (tpred (tsucc t1'0)) = tpred (tsucc (tsucc t1'0))
                                      
  t1 : tm
  H : nvalue t1
  t1' : tm
  H1 : tsucc t1 ==> t1'
  ============================
   t1 = tpred t1'
*)
  (* pred -> not nvalue *)
Qed.
*)
Lemma nvalue_not_succ : forall t1 t2,
(*
  ~(nvalue t1 ->
  tsucc t1 ==> t2).
*)
  nvalue t1 ->
(*  ~(tsucc t1 ==> t2). *)
  tsucc t1 ==> t2 ->
  False.
Proof.
(*  unfold not. *)
  induction t1; intros; inv H.
  inv H0; inv H1.
  inv H0.
  generalize (IHt1 t1' H2 H1); intro T. auto.
Qed.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros.
  generalize dependent y2.
  induction H; intros st H2; inv H2;
  auto; try value_pre; try find_eqn; try value_pre; auto.

  assert(G : False) by (apply (nvalue_not_succ t1 t1' H H1)). inv G.
  assert(G : False) by (apply (nvalue_not_succ st t1' H1 H)). inv G.  
  eapply nvalue_not_succ in H. inv H. eauto.
  eapply nvalue_not_succ in H1. inv H1. eauto.
(*
  apply nvalue_succ_pred; auto.
  symmetry. apply nvalue_succ_pred; auto.
  eapply nvalue_not_succ in H. unfold not in H. apply H in H1. inv H1.
  eapply nvalue_not_succ in H. inv H. assumption.
*)
(*
  inv H1. symmetry. apply ST_IszeroSucc. constructor.
  
  generalize dependent t1'.
  induction H; intros. inv H1. inv H0.
  inv H1. generalize (IHnvalue t1'0 H2); intro T. rewrite T.



  inv H1.
  generalize dependent t1'0.
  induction t1; inv H; intros. inv H2. inv H2.
  generalize (IHt1 H1 t1' H0); intro T. rewrite T. 
*)  
Qed.


(* ###################################################################### *)
(** ** Typing *)

(** The next critical observation about this language is that,
    although there are stuck terms, they are all "nonsensical", mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)

Inductive ty : Type := 
  | TBool : ty
  | TNat : ty.

(** In informal notation, the typing relation is often written
    [|- t \in T], pronounced "[t] has type [T]."  The [|-] symbol is
    called a "turnstile".  (Below, we're going to see richer typing
    relations where an additional "context" argument is written to the
    left of the turnstile.  Here, the context is always empty.) *)
(** 
                           ----------------                            (T_True)
                           |- true \in Bool

                          -----------------                           (T_False)
                          |- false \in Bool

             |- t1 \in Bool    |- t2 \in T    |- t3 \in T
             --------------------------------------------                (T_If)
                    |- if t1 then t2 else t3 \in T

                             ------------                              (T_Zero)
                             |- 0 \in Nat
                              
                            |- t1 \in Nat
                          ------------------                           (T_Succ)
                          |- succ t1 \in Nat

                            |- t1 \in Nat
                          ------------------                           (T_Pred)
                          |- pred t1 \in Nat

                            |- t1 \in Nat
                        ---------------------                        (T_IsZero)
                        |- iszero t1 \in Bool
*)

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True : 
       |- ttrue \in TBool
  | T_False : 
       |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in TBool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- tif t1 t2 t3 \in T
  | T_Zero : 
       |- tzero \in TNat
  | T_Succ : forall t1,
       |- t1 \in TNat ->
       |- tsucc t1 \in TNat
  | T_Pred : forall t1,
       |- t1 \in TNat ->
       |- tpred t1 \in TNat
  | T_Iszero : forall t1,
       |- t1 \in TNat ->
       |- tiszero t1 \in TBool

where "'|-' t '\in' T" := (has_type t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Zero" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Iszero" ].

Hint Constructors has_type.

(* ###################################################################### *)
(** *** Examples *)

(** It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not calculate
    the type of the normal form of a term. *)

Example has_type_1 : 
  |- tif tfalse tzero (tsucc tzero) \in TNat.
Proof. 
  apply T_If. 
    apply T_False.
    apply T_Zero.
    apply T_Succ.
      apply T_Zero.  
Qed.

(** (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)

Example has_type_not : 
  ~ (|- tif tfalse tzero ttrue \in TBool).
Proof.
  intros Contra. solve by inversion 2.  Qed.

(** **** Exercise: 1 star, optional (succ_hastype_nat__hastype_nat) *)
Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.  
Proof.
  intros.
  induction t; inv H; assumption.
Qed.

(* ###################################################################### *)
(** ** Canonical forms *)

(** The following two lemmas capture the basic property that defines
    the shape of well-typed values.  They say that the definition of value
    and the typing relation agree. *)

Lemma bool_canonical : forall t,
  |- t \in TBool -> value t -> bvalue t.
Proof.
  intros t HT HV.
  inversion HV; auto.

  induction H; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
  |- t \in TNat -> value t -> nvalue t.
Proof.
  intros t HT HV.
  inversion HV.
  inversion H; subst; inversion HT.   

  auto.  
Qed.

Lemma not_TNat_implies_nvalue : 
  ~(forall t,
  |- t \in TNat -> nvalue t).
Proof.
  unfold not; intros.
  generalize (H (tif ttrue tzero tzero)); intro T.
  assert(G : (|-tif ttrue tzero tzero \in TNat)) by repeat constructor.
  apply T in G. inv G.
Qed.
(* ###################################################################### *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are values (i.e., not stuck). *)
(*
Lemma bvalue_is_value : forall t,
  bvalue t ->
  value t.
Proof. intros. constructor. assumption. Qed.

Lemma nvalue_is_value : forall t,
  nvalue t ->
  value t.
Proof. intros. unfold value. right. assumption. Qed.
*)
Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.

(** **** Exercise: 3 stars (finish_progress) *)
(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the informal proof fragment in the following
    exercise before starting -- this will save you a lot of time.) *)

Proof with auto.
  intros t T HT.
  has_type_cases (induction HT) Case...
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  Case "T_If".
    right. inversion IHHT1; clear IHHT1.
    SCase "t1 is a value".
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2...
      exists t3...
    SCase "t1 can take a step".
      inversion H as [t1' H1].
      exists (tif t1' t2 t3)...
  Case "T_Succ".
    inv IHHT.
    SCase "left".
    left. apply nat_canonical in H. induction H.
    unfold value; right. repeat constructor.
    unfold value; right. constructor. constructor. assumption. assumption.

    SCase "right".
    inv H. right. exists (tsucc x)...
  Case "T_Pred".
    inv IHHT.
    SCase "left".
    apply nat_canonical in H.
      inv H. right. exists tzero...
      right. exists t... assumption.
    SCase "right".
      inv H. right. exists (tpred x)...
  Case "T_Iszero".
    right. inv IHHT.
    SCase "left".
      apply nat_canonical in H; auto.
      inv H. exists ttrue... exists tfalse...
      inv H.
      exists (tiszero x)...
Qed.
    
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_progress_informal) *)
(** Complete the corresponding informal proof: *)

(** _Theorem_: If [|- t \in T], then either [t] is a value or else 
    [t ==> t'] for some [t']. *)

(** _Proof_: By induction on a derivation of [|- t \in T].

      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
        \in T].  By the IH, either [t1] is a value or else [t1] can step
        to some [t1'].  

            - If [t1] is a value, then by the canonical forms lemmas
              and the fact that [|- t1 \in Bool] we have that [t1] 
              is a [bvalue] -- i.e., it is either [true] or [false].
              If [t1 = true], then [t] steps to [t2] by [ST_IfTrue],
              while if [t1 = false], then [t] steps to [t3] by
              [ST_IfFalse].  Either way, [t] can step, which is what
              we wanted to show.

            - If [t1] itself can take a step, then, by [ST_If], so can
              [t].

    (* FILL IN HERE *)
[]
*)

(** This is more interesting than the strong progress theorem that we
    saw in the Smallstep chapter, where _all_ normal forms were
    values.  Here, a term can be stuck, but only if it is ill
    typed. *)

(** **** Exercise: 1 star (step_review) *)
(** Quick review.  Answer _true_ or _false_.  In this language...
      - Every well-typed normal form is a value.

      - Every value is a normal form.

      - The single-step evaluation relation is
        a partial function (i.e., it is deterministic).

      - The single-step evaluation relation is a _total_ function.

*)
(** [] *)

(*
- Every well-typed normal form is a value.
*)
Example nf_is_not_always_value : 
  ~(forall t, step_normal_form t -> value t).
Proof.
  unfold normal_form, not.
  intros.
  generalize (H (tif tzero tzero tzero)); intro T.
  assert(G : (exists t', tif tzero tzero tzero ==> t') -> False).
  intros. inv H0. inv H1. inv H5.
  apply T in G.
  inv G. inv H0. inv H0.
Qed.

(*
- Every value is a normal form.
value_is_nf
     : forall t : tm, value t -> step_normal_form t
*)

(*
- The single-step evaluation relation is
  a partial function (i.e., it is deterministic).

Theorem step_deterministic:
  deterministic step.

*)

(*
- The single-step evaluation relation is a _total_ function.

Theorem step_deterministic:
  deterministic step.
*)





(* ###################################################################### *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is also a well-typed term.

    This theorem is often called the _subject reduction_ property,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.

(** **** Exercise: 2 stars (finish_preservation) *)
(** Complete the formal proof of the [preservation] property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.) *)

Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  has_type_cases (induction HT) Case; 
         (* every case needs to introduce a couple of things *)
         intros t' HE; 
         (* and we can deal with several impossible
            cases all at once *)
         try (solve by inversion).
    Case "T_If". inversion HE; subst; clear HE.
      SCase "ST_IFTrue". assumption.
      SCase "ST_IfFalse". assumption.
      SCase "ST_If". apply T_If; try assumption.
        apply IHHT1; assumption.
    Case "T_Succ". inv HE. apply T_Succ. apply IHHT...
    Case "T_Pred". inv HE... inv HT...
    Case "T_Iszero". inv HE...
Qed.

(** **** Exercise: 3 stars, advanced (finish_preservation_informal) *)
(** Complete the following proof: *)

(** _Theorem_: If [|- t \in T] and [t ==> t'], then [|- t' \in T]. *)

(** _Proof_: By induction on a derivation of [|- t \in T].

      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 \in Bool], [|- t2 \in T] and [|- t3
        \in T].  

        Inspecting the rules for the small-step reduction relation and
        remembering that [t] has the form [if ...], we see that the
        only ones that could have been used to prove [t ==> t'] are
        [ST_IfTrue], [ST_IfFalse], or [ST_If].

           - If the last rule was [ST_IfTrue], then [t' = t2].  But we
             know that [|- t2 \in T], so we are done.

           - If the last rule was [ST_IfFalse], then [t' = t3].  But we
             know that [|- t3 \in T], so we are done.

           - If the last rule was [ST_If], then [t' = if t1' then t2
             else t3], where [t1 ==> t1'].  We know [|- t1 \in Bool] so,
             by the IH, [|- t1' \in Bool].  The [T_If] rule then gives us
             [|- if t1' then t2 else t3 \in T], as required.

    (* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars (preservation_alternate_proof) *)
(** Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proof to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)

Theorem preservation' : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with eauto.
  intros.
  generalize dependent T.
  induction H0; intros; inv H...

  inv H0. inv H1. assumption.
  inv H0. inv H2. assumption.
  inv H0. constructor.
  inv H0. constructor.

  (*
  intros.
  generalize dependent t'.
  induction H; intros; inv H0...
*)
Qed.

(* ###################################################################### *)
(** ** Type Soundness *)

(** Putting progress and preservation together, we can see that a
    well-typed term can _never_ reach a stuck state.  *)

Definition multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof with auto.
  (*
  unfold stuck, not; intros.
  induction H0; inv H1.
  apply H2.
  apply progress in H.
  inv H... inv H1. unfold normal_form, not in H0. contradiction H0. exists x0...

  apply IHmulti... eapply preservation in H0. apply H0. apply H.
  *)
  intros t t' T HT P. induction P; intros [R S].
  destruct (progress x T HT); auto.   
  apply IHP.  apply (preservation x y T HT H).
  unfold stuck. split; auto.   Qed.


(* ###################################################################### *)
(** * Aside: the [normalize] Tactic *)

(** When experimenting with definitions of programming languages in
    Coq, we often want to see what a particular concrete term steps
    to -- i.e., we want to find proofs for goals of the form [t ==>*
    t'], where [t] is a completely concrete term and [t'] is unknown.
    These proofs are simple but repetitive to do by hand. Consider for
    example reducing an arithmetic expression using the small-step
    relation [astep]. *)


Definition amultistep st := multi (astep st). 
Notation " t '/' st '==>a*' t' " := (amultistep st t t')
  (at level 40, st at level 39).

Example astep_example1 : 
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state 
  ==>a* (ANum 15).
Proof.
  apply multi_step with (APlus (ANum 3) (ANum 12)).
    apply AS_Plus2. 
      apply av_num. 
      apply AS_Mult.
  apply multi_step with (ANum 15).
    apply AS_Plus.
  apply multi_refl.
Qed.

(** We repeatedly apply [multi_step] until we get to a normal
    form. The proofs that the intermediate steps are possible are
    simple enough that [auto], with appropriate hints, can solve
    them. *)

(* Hint Constructors astep aval.*)
Hint Constructors astep.
Hint Constructors aval.
Example astep_example1' : 
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state 
  ==>a* (ANum 15).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.


(** The following custom [Tactic Notation] definition captures this
    pattern.  In addition, before each [multi_step] we print out the
    current goal, so that the user can follow how the term is being
    evaluated. *)

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" := 
   repeat (print_goal; eapply multi_step ; 
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply multi_refl.


Example astep_example1'' : 
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state 
  ==>a* (ANum 15).
Proof.
  normalize.
  (* At this point in the proof script, the Coq response shows 
     a trace of how the expression evaluated. 

   (APlus (ANum 3) (AMult (ANum 3) (ANum 4)) / empty_state ==>a* ANum 15)
   (multi (astep empty_state) (APlus (ANum 3) (ANum 12)) (ANum 15))
   (multi (astep empty_state) (ANum 15) (ANum 15))
*)
Qed.


(** The [normalize] tactic also provides a simple way to calculate
    what the normal form of a term is, by proving a goal with an
    existential variable in it. *)

Example astep_example1''' : exists e',
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state 
  ==>a* e'.
Proof.
  eapply ex_intro. normalize.

(* This time, the trace will be:

    (APlus (ANum 3) (AMult (ANum 3) (ANum 4)) / empty_state ==>a* ??)
    (multi (astep empty_state) (APlus (ANum 3) (ANum 12)) ??)
    (multi (astep empty_state) (ANum 15) ??)

   where ?? is the variable ``guessed'' by eapply.
*)
Qed.


(** **** Exercise: 1 star (normalize_ex) *)
Theorem normalize_ex : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.
Proof.
  eexists.
  normalize.
Qed.

(** **** Exercise: 1 star, optional (normalize_ex') *)
(** For comparison, prove it using [apply] instead of [eapply]. *)

Theorem normalize_ex' : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.
Proof.
  eexists. normalize.
Qed.


(* ###################################################################### *)
(** ** Additional Exercises *)

(** **** Exercise: 2 stars (subject_expansion) *)
(** Having seen the subject reduction property, it is reasonable to
    wonder whether the opposity property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t ==> t']
    and [|- t' \in T], then [|- t \in T]?  If so, prove it.  If
    not, give a counter-example.  (You do not need to prove your
    counter-example in Coq, but feel free to do so if you like.)

    (* FILL IN HERE *)
[]
*)

Theorem not_subject_expansion :
  ~(forall t t' T,
  |- t' \in T -> 
  t ==> t' ->
  |- t \in T).
Proof with auto.
  unfold not; intros.
  assert(G : |-tzero \in TNat) by constructor.
  assert(G2 : tif ttrue tzero tfalse ==> tzero) by constructor.
  generalize (H (tif ttrue tzero tfalse) tzero TNat G G2); intro T.
  inv T.
  inv H6.
Qed.

(** **** Exercise: 2 stars (variation1) *)
(** Suppose, that we add this new rule to the typing relation: 
      | T_SuccBool : forall t,
           |- t \in TBool ->
           |- tsucc t \in TBool
   Which of the following properties remain true in the presence of
   this rule?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinism of [step]

      - Progress

      - Preservation

[]
*)

Module variation1.
Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True : 
       |- ttrue \in TBool
  | T_False : 
       |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in TBool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- tif t1 t2 t3 \in T
  | T_Zero : 
       |- tzero \in TNat
  | T_Succ : forall t1,
       |- t1 \in TNat ->
       |- tsucc t1 \in TNat
  | T_Pred : forall t1,
       |- t1 \in TNat ->
       |- tpred t1 \in TNat
  | T_Iszero : forall t1,
       |- t1 \in TNat ->
       |- tiszero t1 \in TBool
  | T_SuccBool : forall t,
       |- t \in TBool ->
       |- tsucc t \in TBool
where "'|-' t '\in' T" := (has_type t T).

(*
      - Determinism of [step]
: not related to type
*)

(*
      - Progress
*)

Theorem not_progress :
  ~(forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t').
Proof.
  unfold not; intros.
  assert(G : |-tsucc tfalse \in TBool) by repeat constructor.
  generalize (H (tsucc tfalse) TBool G); intro T.
  inv T.
  inv H0. inv H1. inv H1. inv H2. inv H0. inv H1. inv H2.
Qed.

(*
      - Preservation

added one more case in "has_type"
effect on conclusion (|- t' \in T) : more choice. no need to consider
effect on premise (t ==> t') : no effect
effect on premise (|- t \in T) : more choice,
but it is all eliminated in conclusion.

| T_SuccBool : forall tt,
    |- tt \in TBool ->
    |- tsucc tt \in TBool

Newly introduced case must be form of
t := (tsucc tt)
T := TBool

t' \in TBool.
| ST_Succ : forall t1 t1' : tm, t1 ==> t1' -> tsucc t1 ==> tsucc t1'

####################### TODO : It is provable, but simple explanation??????????????? #############################################
*)

Lemma pres : forall tt t',
  |- (tsucc tt) \in TBool ->
  (tsucc tt) ==> t' ->
  |- t' \in TBool.
Proof with eauto.
  (*
  intros. generalize dependent t'.
  induction H; intros; inv H0; try auto.
  inv H2... constructor... constructor...
  inv H2... constructor...
  constructor... constructor.
  inv H2. constructor... auto.
  constructor.
*)
  intros. inv H0.
  induction H2; inv H.
  constructor. inv H1...
  constructor. inv H1...
  inv H1. constructor. constructor... generalize (T_SuccBool t1 H4); intro T. apply IHstep in T. inv T. auto.
  constructor. apply IHstep in H1. auto.
  inv H1. inv H2. inv H1.
  apply T_SuccBool. constructor.
  apply T_SuccBool. constructor.

  Abort.
  (*
  induction H2; intros.
  inv H1; inv H0; repeat constructor; auto.
  inv H1; inv H0; repeat constructor; auto.
  inv H1; inv H0; repeat constructor; auto.
*)
  (*
  induction H2; intros; inv H1; repeat constructor; auto;
  try inv H0; auto.
  *)
(*  
  apply T_SuccBool.
  constructor. inv H1.
  induction H2.
  inv H0; auto.
  inv H0; auto.
  inv H0; auto.
  constructor; auto. 
  
  generalize dependent t1'.
  induction H0; intros; inv H2.
  *)

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with eauto.
  intros.
  generalize dependent T.
  induction H0; intros; inv H...

  constructor...
  constructor...
  constructor...
  inv H0; constructor...
  inv H0; constructor...
  inv H2. inv H0...
  constructor...
  constructor...
  inv H0. constructor...
  inv H0. constructor...
  constructor...
Qed.

Theorem not_preservation : ~(forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T).
Proof with eauto.
  unfold not; intros.
  intros.
  assert(G: |-tsucc (tif ttrue tfalse tfalse) \in TBool).
  repeat constructor...
  assert(G2: tsucc (tif ttrue tfalse tfalse) ==> tsucc tfalse).
  repeat constructor...
  generalize (H (tsucc (tif ttrue tfalse tfalse)) (tsucc tfalse) TBool G G2); intro T.
Abort.
(*
Lemma T_SuccBool_cannot_step : forall t,
  |- t \in TBool ->
  ~(exists t', (tsucc t) ==> t').
Proof with eauto.
  unfold not; intros.
  inv H0. inv H1.

  generalize dependent t1'.
  induction H; intros...
  inv H2. inv H2. inv H2.
Qed.
*)
End variation1.

(** **** Exercise: 2 stars (variation2) *)
(** Suppose, instead, that we add this new rule to the [step] relation: 
      | ST_Funny1 : forall t2 t3,
           (tif ttrue t2 t3) ==> t3
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)
Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. intros. apply H0. assumption. Qed.
Ltac exploit x :=
    refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).



Module variation2.
Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')
  | ST_Funny1 : forall t2 t3,
      (tif ttrue t2 t3) ==> t3
where "t1 '==>' t2" := (step t1 t2).

Theorem not_step_deterministic:
  ~(deterministic step).
Proof.
  unfold deterministic, not.
  intros.
  generalize (H (tif ttrue tzero tfalse) tzero tfalse); intro T.
  exploit T.
  constructor. constructor. intros. inv H0.
Qed.

Theorem progress :
  (forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t').
Proof with eauto.
  induction t; intros.
  left...
  left...
  inv H.
  generalize (IHt1 TBool H3); intro T1.
  generalize (IHt2 T H5); intro T2.
  generalize (IHt3 T H6); intro T3.
  inv T1. apply bool_canonical in H...
  inv H; right. exists t2; constructor. exists t3; constructor.
  inv H; right. exists (tif x t2 t3); constructor...

  left...
  inv H. generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H. right. exists (tsucc x). constructor...

  inv H. generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H; right. exists (tzero). constructor...
  exists t0; constructor...

  inv H.
  right. exists (tpred x). constructor...
  
  inv H.
  generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H; right. exists ttrue; constructor. exists tfalse; constructor...
  inv H. right. exists (tiszero x); constructor...
Qed.

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with eauto.
  intros.
  generalize dependent T.
  induction H0; intros; inv H...

  inv H0. inv H1. assumption.
  inv H0. inv H2. assumption.
  inv H0. constructor.
  inv H0. constructor.

  (*
  intros.
  generalize dependent t'.
  induction H; intros; inv H0...
*)
Qed.

End variation2.

(** **** Exercise: 2 stars, optional (variation3) *)
(** Suppose instead that we add this rule:
      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 ==> t2' ->
           (tif t1 t2 t3) ==> (tif t1 t2' t3)
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)

Module variation3.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')
  | ST_Funny2 : forall t1 t2 t2' t3,
      t2 ==> t2' ->
      (tif t1 t2 t3) ==> (tif t1 t2' t3)
where "t1 '==>' t2" := (step t1 t2).

Theorem not_step_deterministic:
  ~(deterministic step).
Proof.
  unfold deterministic, not.
  intros.
  generalize (H (tif ttrue (tpred tzero) tfalse) (tpred tzero)
                (tif ttrue tzero tfalse)); intro T.
  exploit T.
  constructor. constructor. constructor. intros. inv H0.
Qed.

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with eauto.
  induction t; intros.
  left...
  left...
  inv H.
  generalize (IHt1 TBool H3); intro T1.
  generalize (IHt2 T H5); intro T2.
  generalize (IHt3 T H6); intro T3.
  inv T1. apply bool_canonical in H...
  inv H; right. exists t2; constructor. exists t3; constructor.
  inv H; right. exists (tif x t2 t3); constructor...

  left...
  inv H. generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H. right. exists (tsucc x). constructor...

  inv H. generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H; right. exists (tzero). constructor...
  exists t0; constructor...

  inv H.
  right. exists (tpred x). constructor...
  
  inv H.
  generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H; right. exists ttrue; constructor. exists tfalse; constructor...
  inv H. right. exists (tiszero x); constructor...
Qed.

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with eauto.
  intros.
  generalize dependent T.
  induction H0; intros; inv H...

  inv H0. inv H1. assumption.
  inv H0. inv H2. assumption.
  inv H0. constructor.
  inv H0. constructor.
Qed.

End variation3.


(** **** Exercise: 2 stars, optional (variation4) *)
(** Suppose instead that we add this rule:
      | ST_Funny3 : 
          (tpred tfalse) ==> (tpred (tpred tfalse))
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)

Module variation4.
Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')
  | ST_Funny3 : 
      (tpred tfalse) ==> (tpred (tpred tfalse))
where "t1 '==>' t2" := (step t1 t2).

Ltac value_pre :=
  match goal with
    | H1: ttrue ==> _             |- _ => inv H1
    | H1: tfalse ==> _            |- _ => inv H1
    | H1: tzero ==> _             |- _ => inv H1
  end.

Lemma nvalue_not_succ : forall t1 t2,
  nvalue t1 ->
  tsucc t1 ==> t2 ->
  False.
Proof.
  induction t1; intros; inv H.
  inv H0; inv H1.
  inv H0.
  generalize (IHt1 t1' H2 H1); intro T. auto.
Qed.

Theorem step_deterministic :
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros.
  generalize dependent y2.
  induction H; intros st H2; inv H2;
  auto; try value_pre; try find_eqn; try value_pre; auto.

  generalize (nvalue_not_succ t1 t1'); intro T; exploit T... intros Tmp; inv Tmp.

  generalize (nvalue_not_succ st t1'); intro T; exploit T... intros Tmp; inv Tmp.

  eapply nvalue_not_succ in H; inv H...
  eapply nvalue_not_succ in H1; inv H1...  
Qed.

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with eauto.
  induction t; intros.
  left...
  left...
  inv H...
  generalize (IHt1 TBool H3); intro T1.
  generalize (IHt2 T H5); intro T2.
  generalize (IHt3 T H6); intro T3.
  inv T1. apply bool_canonical in H...
  inv H; right. exists t2; constructor. exists t3; constructor.
  inv H; right. exists (tif x t2 t3); constructor...

  left...
  inv H. generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H. right. exists (tsucc x). constructor...

  inv H. generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H; right. exists (tzero). constructor...
  exists t0; constructor...

  inv H.
  right. exists (tpred x). constructor...
  
  inv H.
  generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H; right. exists ttrue; constructor. exists tfalse; constructor...
  inv H. right. exists (tiszero x); constructor...
Qed.

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with eauto.
  intros.
  generalize dependent T.
  induction H0; intros; inv H...

  inv H0. inv H1. assumption.
  inv H0. inv H2. assumption.
  inv H0. constructor.
  inv H0. constructor.
Qed.

End variation4.

(** **** Exercise: 2 stars, optional (variation5) *)
(** Suppose instead that we add this rule:
   
      | T_Funny4 : 
            |- tzero \in TBool
   ]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)


Module variation5.

Reserved Notation "'|-' t '\in' T" (at level 40).
Inductive has_type : tm -> ty -> Prop :=
  | T_True : 
       |- ttrue \in TBool
  | T_False : 
       |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in TBool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- tif t1 t2 t3 \in T
  | T_Zero : 
       |- tzero \in TNat
  | T_Succ : forall t1,
       |- t1 \in TNat ->
       |- tsucc t1 \in TNat
  | T_Pred : forall t1,
       |- t1 \in TNat ->
       |- tpred t1 \in TNat
  | T_Iszero : forall t1,
       |- t1 \in TNat ->
       |- tiszero t1 \in TBool
  | T_Funny4 : 
       |- tzero \in TBool
where "'|-' t '\in' T" := (has_type t T).

(* step deterministic : same *)

Theorem not_progress :
  ~(forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t').
Proof with auto.
  unfold not.
  intros.
  generalize (H ((tif tzero ttrue ttrue)) (TBool)); intro T; exploit T.
  constructor. constructor. constructor. constructor.
  intros.
  inv H0.
  inv H1. inv H0. inv H0.
  inv H1. inv H0. inv H5.
Qed.

  
(*
Lemma bool_canonical : forall t,
  |- t \in TBool -> value t -> bvalue t.
Proof.
  intros t HT HV.
  inversion HV; auto.

  induction H; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
  |- t \in TNat -> value t -> nvalue t.
Proof.
  intros t HT HV.
  inversion HV.
  inversion H; subst; inversion HT.   

  auto.  
Qed.

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with eauto.
  induction t; intros.
  left...
  left...
  inv H...
  generalize (IHt1 TBool H3); intro T1.
  generalize (IHt2 T H5); intro T2.
  generalize (IHt3 T H6); intro T3.
  inv T1. apply bool_canonical in H...
  inv H; right. exists t2; constructor. exists t3; constructor.
  inv H; right. exists (tif x t2 t3); constructor...

  left...
  inv H. generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H. right. exists (tsucc x). constructor...

  inv H. generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H; right. exists (tzero). constructor...
  exists t0; constructor...

  inv H.
  right. exists (tpred x). constructor...
  
  inv H.
  generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H; right. exists ttrue; constructor. exists tfalse; constructor...
  inv H. right. exists (tiszero x); constructor...
Qed.
*)

(*
Theorem preservation :
  ~(forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T).
Proof with eauto.
  unfold not. intros.
  generalize (H (tpred (tsucc tzero)) 
Qed.

  T : ty
  H0 : |-tpred (tsucc tzero) \in T
  ============================
   |-tzero \in T
*)

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.
Proof with eauto.
  intros.
  generalize dependent T.
  induction H0; intros; inv H...

  constructor...
  constructor. apply IHstep...

  inv H0. inv H1. assumption.
  inv H0. inv H2. assumption.
  constructor. apply IHstep...
  constructor.
  inv H0. constructor.
  inv H0. constructor.
  constructor. apply IHstep...
Qed.

End variation5.


(** **** Exercise: 2 stars, optional (variation6) *)
(** Suppose instead that we add this rule:
   
      | T_Funny5 : 
            |- tpred tzero \in TBool
   ]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)

Module variation6.

Reserved Notation "'|-' t '\in' T" (at level 40).
Inductive has_type : tm -> ty -> Prop :=
  | T_True : 
       |- ttrue \in TBool
  | T_False : 
       |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in TBool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- tif t1 t2 t3 \in T
  | T_Zero : 
       |- tzero \in TNat
  | T_Succ : forall t1,
       |- t1 \in TNat ->
       |- tsucc t1 \in TNat
  | T_Pred : forall t1,
       |- t1 \in TNat ->
       |- tpred t1 \in TNat
  | T_Iszero : forall t1,
       |- t1 \in TNat ->
       |- tiszero t1 \in TBool
  | T_Funny5 : 
       |- (tpred tzero) \in TBool
where "'|-' t '\in' T" := (has_type t T).  

(* step deterministic : same *)

Lemma bool_canonical : forall t,
  |- t \in TBool -> value t -> bvalue t.
Proof.
  intros t HT HV.
  inversion HV; auto.

  induction H; inversion HT; auto.
Qed.

Lemma nat_canonical : forall t,
  |- t \in TNat -> value t -> nvalue t.
Proof.
  intros t HT HV.
  inversion HV.
  inversion H; subst; inversion HT.   

  auto.  
Qed.

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with eauto.
  induction t; intros.
  left...
  left...
  inv H.
  generalize (IHt1 TBool H3); intro T1.
  generalize (IHt2 T H5); intro T2.
  generalize (IHt3 T H6); intro T3.
  inv T1. apply bool_canonical in H...
  inv H; right. exists t2; constructor. exists t3; constructor.
  inv H; right. exists (tif x t2 t3); constructor...

  left...
  inv H. generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H. right. exists (tsucc x). constructor...

  inv H. generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H; right. exists (tzero). constructor...
  exists t0; constructor...

  inv H.
  right. exists (tpred x). constructor...

(* right. eexists. constructor. *)
  right. eexists. constructor.

  right.
  inv H.
  generalize (IHt TNat H1); intro T.
  inv T.
  apply nat_canonical in H...
  destruct H. eexists; constructor. eexists; constructor...

  inv H.
  eexists; constructor...
  (*
  exists (tiszero x). constructor...

  
  right.
  eexists. constructor.
  
  apply IHt in H.
  inv H. apply nat_canonical in H1.
  apply IHt in H1. inv H1.
  inv H. inv H0. 
  inv H.
  generalize (IHt TNat H1); intro T.
  inv T. apply nat_canonical in H...
  inv H; right. exists ttrue; constructor. exists tfalse; constructor...
  inv H. right. exists (tiszero x); constructor...
*)
Qed.

Theorem not_preservation :
  ~(forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T).
Proof with eauto.
  unfold not; intros.
  generalize (H (tpred tzero) tzero TBool); intro T; exploit T.
  constructor.
  constructor.
  intros.
  inv H0.
Qed.


(*
Theorem not_progress :
  ~(forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t').
Proof with auto.
  unfold not.
  intros.
  generalize (H (tpred tzero) (TBool)); intro T; exploit T.
  constructor.
  intros. inv H0. inv H1. inv H0. inv H0. inv H1.
  remember x as xx.
  inv H0. admit.
  
  unfold not.
  intros.
  generalize (H ((tif (tpred tzero) ttrue ttrue)) (TBool)); intro T; exploit T.
  constructor. constructor. constructor. constructor.
  intros.
  inv H0.
  inv H1. inv H0. inv H0.
  inv H1. inv H0. inv H5.
Qed.

  | T_Funny5 : 
       |- (tpred tzero) \in TBool
*)


End variation6.


(** **** Exercise: 3 stars, optional (more_variations) *)
(** Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
    [] 
*)

(** **** Exercise: 1 star (remove_predzero) *)
(** The evaluation rule [E_PredZero] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of zero to
    be undefined, rather than being defined to be zero.  Can we
    achieve this simply by removing the rule from the definition of
    [step]?  Would doing so create any problems elsewhere? 

(* FILL IN HERE *)
[] *)

Module remove_predzero.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : forall t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
(*  | ST_PredZero :
      (tpred tzero) ==> tzero *)
  | ST_PredSucc : forall t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : forall t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : forall t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : forall t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True : 
       |- ttrue \in TBool
  | T_False : 
       |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T,
       |- t1 \in TBool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- tif t1 t2 t3 \in T
  | T_Zero : 
       |- tzero \in TNat
  | T_Succ : forall t1,
       |- t1 \in TNat ->
       |- tsucc t1 \in TNat
  | T_Pred : forall t1,
       |- t1 \in TNat ->
       |- tpred t1 \in TNat
  | T_Iszero : forall t1,
       |- t1 \in TNat ->
       |- tiszero t1 \in TBool

where "'|-' t '\in' T" := (has_type t T).

Theorem not_progress :
  ~(forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t').
Proof with eauto.
  unfold not; intros.
  generalize (H (tpred tzero) TNat); intro T; exploit T...
  constructor. constructor.
  intros.
  inv H0. inv H1. inv H0. inv H0. inv H1. inv H0. inv H2.
Qed.

End remove_predzero.


(** **** Exercise: 4 stars, advanced (prog_pres_bigstep) *)
(** Suppose our evaluation relation is defined in the big-step style.
    What are the appropriate analogs of the progress and preservation
    properties?

(* FILL IN HERE *)
[]
*)

(* progress ~= bigstep itself *)
(* preservation ~= aexp, bexp itself *)

(* $Date: 2014-04-08 23:31:16 -0400 (Tue, 08 Apr 2014) $ *)
