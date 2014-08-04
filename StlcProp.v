(** * StlcProp: Properties of STLC *)

Require Export Stlc.

Module STLCProp.
Import STLC.

(** In this chapter, we develop the fundamental theory of the Simply
    Typed Lambda Calculus -- in particular, the type safety
    theorem. *)

(* ###################################################################### *)
(** * Canonical Forms *)

Lemma canonical_forms_bool : forall t,
  empty |- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x0. exists t0.  auto.
Qed.
   

(* ###################################################################### *)
(** * Progress *)

(** As before, the _progress_ theorem tells us that closed, well-typed
    terms are not stuck: either a well-typed term is a value, or it
    can take an evaluation step.  The proof is a relatively
    straightforward extension of the progress proof we saw in the
    [Types] chapter. *)

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.

(** _Proof_: by induction on the derivation of [|- t \in T].

    - The last rule of the derivation cannot be [T_Var], since a
      variable is never well typed in an empty context.

    - The [T_True], [T_False], and [T_Abs] cases are trivial, since in
      each of these cases we know immediately that [t] is a value.

    - If the last rule of the derivation was [T_App], then [t = t1
      t2], and we know that [t1] and [t2] are also well typed in the
      empty context; in particular, there exists a type [T2] such that
      [|- t1 \in T2 -> T] and [|- t2 \in T2].  By the induction
      hypothesis, either [t1] is a value or it can take an evaluation
      step.

        - If [t1] is a value, we now consider [t2], which by the other
          induction hypothesis must also either be a value or take an
          evaluation step.

            - Suppose [t2] is a value.  Since [t1] is a value with an
              arrow type, it must be a lambda abstraction; hence [t1
              t2] can take a step by [ST_AppAbs].

            - Otherwise, [t2] can take a step, and hence so can [t1
              t2] by [ST_App2].

        - If [t1] can take a step, then so can [t1 t2] by [ST_App1].

    - If the last rule of the derivation was [T_If], then [t = if t1
      then t2 else t3], where [t1] has type [Bool].  By the IH, [t1]
      either is a value or takes a step.

        - If [t1] is a value, then since it has type [Bool] it must be
          either [true] or [false].  If it is [true], then [t] steps
          to [t2]; otherwise it steps to [t3].

        - Otherwise, [t1] takes a step, and therefore so does [t] (by
          [ST_If]).
*)

Proof with eauto.
  intros t T Ht.
  remember (empty) as Gamma.
(*  remember (@empty ty) as Gamma. *)
  has_type_cases (induction Ht) Case; subst Gamma...
  Case "T_Var".
    (* contradictory: variables cannot be typed in an 
       empty context *)
    inversion H. 

  Case "T_App". 
    (* [t] = [t1 t2].  Proceed by cases on whether [t1] is a 
       value or steps... *)
    right. destruct IHHt1...
    SCase "t1 is a value".
      destruct IHHt2...
      SSCase "t2 is also a value".
        assert (exists x0 t0, t1 = tabs x0 T11 t0).
        eapply canonical_forms_fun; eauto.
        destruct H1 as [x0 [t0 Heq]]. subst.
        exists ([x0:=t2]t0)...

      SSCase "t2 steps".
        inversion H0 as [t2' Hstp]. exists (tapp t1 t2')...

    SCase "t1 steps".
      inversion H as [t1' Hstp]. exists (tapp t1' t2)...

  Case "T_If".
    right. destruct IHHt1...
    
    SCase "t1 is a value".
      destruct (canonical_forms_bool t1); subst; eauto.

    SCase "t1 also steps".
      inversion H as [t1' Hstp]. exists (tif t1' t2 t3)...
Qed.

(** **** Exercise: 3 stars, optional (progress_from_term_ind) *)
(** Show that progress can also be proved by induction on terms
    instead of induction on typing derivations. *)

Theorem progress' : forall t T,
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
Proof with eauto.
  intros t.
  t_cases (induction t) Case; intros T Ht; auto.

  inv Ht. inversion H1.
  inv Ht.
  generalize H2; intro H1.
  generalize H4; intro H3.
  apply IHt1 in H2.
  apply IHt2 in H4.
  right.
  inv H4. inv H2.
  inv H1; inv H0.
  eexists. (*using it to early, right after right, will make next line not work *)
  apply ST_AppAbs...
  inv H0. eexists. apply ST_App1...
  inv H2. inv H. eexists. apply ST_App2...
  inv H. inv H0. eexists. apply ST_App1...

  inv Ht.
  generalize H3; intro T1.
  generalize H5; intro T2.
  generalize H6; intro T3.  
  apply IHt1 in H3.
  apply IHt2 in H5.
  apply IHt3 in H6.
  right.
  inv H3. inv H. inv T1. eexists; constructor. eexists; constructor.
  inv H. eexists; constructor...
Qed.
                                 
(** [] *)

(* ###################################################################### *)
(** * Preservation *)

(** The other half of the type soundness property is the preservation
    of types during reduction.  For this, we need to develop some
    technical machinery for reasoning about variables and
    substitution.  Working from top to bottom (the high-level property
    we are actually interested in to the lowest-level technical lemmas
    that are needed by various cases of the more interesting proofs),
    the story goes like this:

      - The _preservation theorem_ is proved by induction on a typing
        derivation, pretty much as we did in the [Types] chapter.  The
        one case that is significantly different is the one for the
        [ST_AppAbs] rule, which is defined using the substitution
        operation.  To see that this step preserves typing, we need to
        know that the substitution itself does.  So we prove a...

      - _substitution lemma_, stating that substituting a (closed)
        term [s] for a variable [x] in a term [t] preserves the type
        of [t].  The proof goes by induction on the form of [t] and
        requires looking at all the different cases in the definition
        of substitition.  This time, the tricky cases are the ones for
        variables and for function abstractions.  In both cases, we
        discover that we need to take a term [s] that has been shown
        to be well-typed in some context [Gamma] and consider the same
        term [s] in a slightly different context [Gamma'].  For this
        we prove a...

      - _context invariance_ lemma, showing that typing is preserved
        under "inessential changes" to the context [Gamma] -- in
        particular, changes that do not affect any of the free
        variables of the term.  For this, we need a careful definition
        of

      - the _free variables_ of a term -- i.e., the variables occuring
        in the term that are not in the scope of a function
        abstraction that binds them.
*)

(* ###################################################################### *)
(** ** Free Occurrences *)

(** A variable [x] _appears free in_ a term _t_ if [t] contains some
    occurrence of [x] that is not under an abstraction labeled [x].  For example: 
      - [y] appears free, but [x] does not, in [\x:T->U. x y] 
      - both [x] and [y] appear free in [(\x:T->U. x y) x] 
      - no variables appear free in [\x:T->U. \y:T. x y]  *)

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
      appears_free_in x (tif t1 t2 t3).

Tactic Notation "afi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "afi_var"
  | Case_aux c "afi_app1" | Case_aux c "afi_app2" 
  | Case_aux c "afi_abs" 
  | Case_aux c "afi_if1" | Case_aux c "afi_if2" 
  | Case_aux c "afi_if3" ].

Hint Constructors appears_free_in.

(** A term in which no variables appear free is said to be _closed_. *)

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

(* ###################################################################### *)
(** ** Substitution *)

(** We first need a technical lemma connecting free variables and
    typing contexts.  If a variable [x] appears free in a term [t],
    and if we know [t] is well typed in context [Gamma], then it must
    be the case that [Gamma] assigns a type to [x]. *)

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.

(** _Proof_: We show, by induction on the proof that [x] appears free
      in [t], that, for all contexts [Gamma], if [t] is well typed
      under [Gamma], then [Gamma] assigns some type to [x].

      - If the last rule used was [afi_var], then [t = x], and from
        the assumption that [t] is well typed under [Gamma] we have
        immediately that [Gamma] assigns a type to [x].

      - If the last rule used was [afi_app1], then [t = t1 t2] and [x]
        appears free in [t1].  Since [t] is well typed under [Gamma],
        we can see from the typing rules that [t1] must also be, and
        the IH then tells us that [Gamma] assigns [x] a type.

      - Almost all the other cases are similar: [x] appears free in a
        subterm of [t], and since [t] is well typed under [Gamma], we
        know the subterm of [t] in which [x] appears is well typed
        under [Gamma] as well, and the IH gives us exactly the
        conclusion we want.

      - The only remaining case is [afi_abs].  In this case [t =
        \y:T11.t12], and [x] appears free in [t12]; we also know that
        [x] is different from [y].  The difference from the previous
        cases is that whereas [t] is well typed under [Gamma], its
        body [t12] is well typed under [(Gamma, y:T11)], so the IH
        allows us to conclude that [x] is assigned some type by the
        extended context [(Gamma, y:T11)].  To conclude that [Gamma]
        assigns a type to [x], we appeal to lemma [extend_neq], noting
        that [x] and [y] are different variables. *)

Proof.
  intros x t T Gamma H H0. generalize dependent Gamma. 
  generalize dependent T. 
  afi_cases (induction H) Case; 
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
Qed.

(** Next, we'll need the fact that any term [t] which is well typed in
    the empty context is closed -- that is, it has no free variables. *)

(** **** Exercise: 2 stars, optional (typable_empty__closed) *)
Corollary typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.
Proof.
  unfold closed, not.
  intros.
  apply free_in_context with (Gamma:=empty) (T:=T) in H0.
  inv H0. inv H1. assumption.
Qed.

(** Sometimes, when we have a proof [Gamma |- t : T], we will need to
    replace [Gamma] by a different context [Gamma'].  When is it safe
    to do this?  Intuitively, it must at least be the case that
    [Gamma'] assigns the same types as [Gamma] to all the variables
    that appear free in [t]. In fact, this is the only condition that
    is needed. *)

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.

(** _Proof_: By induction on the derivation of [Gamma |- t \in T].

      - If the last rule in the derivation was [T_Var], then [t = x]
        and [Gamma x = T].  By assumption, [Gamma' x = T] as well, and
        hence [Gamma' |- t \in T] by [T_Var].

      - If the last rule was [T_Abs], then [t = \y:T11. t12], with [T
        = T11 -> T12] and [Gamma, y:T11 |- t12 \in T12].  The induction
        hypothesis is that for any context [Gamma''], if [Gamma,
        y:T11] and [Gamma''] assign the same types to all the free
        variables in [t12], then [t12] has type [T12] under [Gamma''].
        Let [Gamma'] be a context which agrees with [Gamma] on the
        free variables in [t]; we must show [Gamma' |- \y:T11. t12 \in
        T11 -> T12].

        By [T_Abs], it suffices to show that [Gamma', y:T11 |- t12 \in
        T12].  By the IH (setting [Gamma'' = Gamma', y:T11]), it
        suffices to show that [Gamma, y:T11] and [Gamma', y:T11] agree
        on all the variables that appear free in [t12].  

        Any variable occurring free in [t12] must either be [y], or
        some other variable.  [Gamma, y:T11] and [Gamma', y:T11]
        clearly agree on [y].  Otherwise, we note that any variable
        other than [y] which occurs free in [t12] also occurs free in
        [t = \y:T11. t12], and by assumption [Gamma] and [Gamma']
        agree on all such variables, and hence so do [Gamma, y:T11]
        and [Gamma', y:T11].

      - If the last rule was [T_App], then [t = t1 t2], with [Gamma |-
        t1 \in T2 -> T] and [Gamma |- t2 \in T2].  One induction
        hypothesis states that for all contexts [Gamma'], if [Gamma']
        agrees with [Gamma] on the free variables in [t1], then [t1]
        has type [T2 -> T] under [Gamma']; there is a similar IH for
        [t2].  We must show that [t1 t2] also has type [T] under
        [Gamma'], given the assumption that [Gamma'] agrees with
        [Gamma] on all the free variables in [t1 t2].  By [T_App], it
        suffices to show that [t1] and [t2] each have the same type
        under [Gamma'] as under [Gamma].  However, we note that all
        free variables in [t1] are also free in [t1 t2], and similarly
        for free variables in [t2]; hence the desired result follows
        by the two IHs.
*)

Proof with eauto.
  intros. 
  generalize dependent Gamma'.
  has_type_cases (induction H) Case; intros; auto.
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to 
       instantiate is [extend Gamma x T11] *)
    unfold extend. destruct (eq_id_dec x0 x1)... 
  Case "T_App".
    apply T_App with T11...  
Qed.

(** Now we come to the conceptual heart of the proof that reduction
    preserves types -- namely, the observation that _substitution_
    preserves types.

    Formally, the so-called _Substitution Lemma_ says this: suppose we
    have a term [t] with a free variable [x], and suppose we've been
    able to assign a type [T] to [t] under the assumption that [x] has
    some type [U].  Also, suppose that we have some other term [v] and
    that we've shown that [v] has type [U].  Then, since [v] satisfies
    the assumption we made about [x] when typing [t], we should be
    able to substitute [v] for each of the occurrences of [x] in [t]
    and obtain a new term that still has type [T]. *)

(** _Lemma_: If [Gamma,x:U |- t \in T] and [|- v \in U], then [Gamma |-
    [x:=v]t \in T]. *)

Lemma substitution_preserves_typing : forall Gamma x U t v T,
     extend Gamma x U |- t \in T ->
     empty |- v \in U   ->
     Gamma |- [x:=v]t \in T.

(** One technical subtlety in the statement of the lemma is that we
    assign [v] the type [U] in the _empty_ context -- in other words,
    we assume [v] is closed.  This assumption considerably simplifies
    the [T_Abs] case of the proof (compared to assuming [Gamma |- v \in
    U], which would be the other reasonable assumption at this point)
    because the context invariance lemma then tells us that [v] has
    type [U] in any context at all -- we don't have to worry about
    free variables in [v] clashing with the variable being introduced
    into the context by [T_Abs].

    _Proof_: We prove, by induction on [t], that, for all [T] and
    [Gamma], if [Gamma,x:U |- t \in T] and [|- v \in U], then [Gamma |-
    [x:=v]t \in T].
 
      - If [t] is a variable, there are two cases to consider, depending
        on whether [t] is [x] or some other variable.

          - If [t = x], then from the fact that [Gamma, x:U |- x \in T] we
            conclude that [U = T].  We must show that [[x:=v]x = v] has
            type [T] under [Gamma], given the assumption that [v] has
            type [U = T] under the empty context.  This follows from
            context invariance: if a closed term has type [T] in the
            empty context, it has that type in any context.

          - If [t] is some variable [y] that is not equal to [x], then
            we need only note that [y] has the same type under [Gamma,
            x:U] as under [Gamma].

      - If [t] is an abstraction [\y:T11. t12], then the IH tells us,
        for all [Gamma'] and [T'], that if [Gamma',x:U |- t12 \in T']
        and [|- v \in U], then [Gamma' |- [x:=v]t12 \in T'].

        The substitution in the conclusion behaves differently,
        depending on whether [x] and [y] are the same variable name.

        First, suppose [x = y].  Then, by the definition of
        substitution, [[x:=v]t = t], so we just need to show [Gamma |-
        t \in T].  But we know [Gamma,x:U |- t : T], and since the
        variable [y] does not appear free in [\y:T11. t12], the
        context invariance lemma yields [Gamma |- t \in T].

        Second, suppose [x <> y].  We know [Gamma,x:U,y:T11 |- t12 \in
        T12] by inversion of the typing relation, and [Gamma,y:T11,x:U
        |- t12 \in T12] follows from this by the context invariance
        lemma, so the IH applies, giving us [Gamma,y:T11 |- [x:=v]t12 \in
        T12].  By [T_Abs], [Gamma |- \y:T11. [x:=v]t12 \in T11->T12], and
        by the definition of substitution (noting that [x <> y]),
        [Gamma |- \y:T11. [x:=v]t12 \in T11->T12] as required.

      - If [t] is an application [t1 t2], the result follows
        straightforwardly from the definition of substitution and the
        induction hypotheses.

      - The remaining cases are similar to the application case.

    Another technical note: This proof is a rare case where an
    induction on terms, rather than typing derivations, yields a
    simpler argument.  The reason for this is that the assumption
    [extend Gamma x U |- t \in T] is not completely generic, in
    the sense that one of the "slots" in the typing relation -- namely
    the context -- is not just a variable, and this means that Coq's
    native induction tactic does not give us the induction hypothesis
    that we want.  It is possible to work around this, but the needed
    generalization is a little tricky.  The term [t], on the other
    hand, _is_ completely generic. *)

Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T. 
  t_cases (induction t) Case; intros T Gamma H;
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tvar".
    rename i into y. destruct (eq_id_dec x y).
    SCase "x=y".
      subst. 
      rewrite extend_eq in H2.
      inversion H2; subst. clear H2.
                  eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ T empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      apply T_Var. rewrite extend_neq in H2... 
  Case "tabs".
    rename i into y. apply T_Abs.
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
Qed.

(** The substitution lemma can be viewed as a kind of "commutation"
    property.  Intuitively, it says that substitution and typing can
    be done in either order: we can either assign types to the terms
    [t] and [v] separately (under suitable contexts) and then combine
    them using substitution, or we can substitute first and then
    assign a type to [ [x:=v] t ] -- the result is the same either
    way. *)

(* ###################################################################### *)
(** ** Main Theorem *)

(** We now have the tools we need to prove preservation: if a closed
    term [t] has type [T], and takes an evaluation step to [t'], then [t']
    is also a closed term with type [T].  In other words, the small-step
    evaluation relation preserves types.
*)

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.

(** _Proof_: by induction on the derivation of [|- t \in T].

    - We can immediately rule out [T_Var], [T_Abs], [T_True], and
      [T_False] as the final rules in the derivation, since in each of
      these cases [t] cannot take a step.

    - If the last rule in the derivation was [T_App], then [t = t1
      t2].  There are three cases to consider, one for each rule that
      could have been used to show that [t1 t2] takes a step to [t'].

        - If [t1 t2] takes a step by [ST_App1], with [t1] stepping to
          [t1'], then by the IH [t1'] has the same type as [t1], and
          hence [t1' t2] has the same type as [t1 t2].

        - The [ST_App2] case is similar.

        - If [t1 t2] takes a step by [ST_AppAbs], then [t1 =
          \x:T11.t12] and [t1 t2] steps to [[x:=t2]t12]; the
          desired result now follows from the fact that substitution
          preserves types.

    - If the last rule in the derivation was [T_If], then [t = if t1
      then t2 else t3], and there are again three cases depending on
      how [t] steps.

        - If [t] steps to [t2] or [t3], the result is immediate, since
          [t2] and [t3] have the same type as [t].

        - Otherwise, [t] steps by [ST_If], and the desired conclusion
          follows directly from the induction hypothesis.
*)

Proof with eauto.
  remember (@empty ty) as Gamma. 
  intros t t' T HT. generalize dependent t'.   
  has_type_cases (induction HT) Case;
       intros t' HE; subst Gamma; subst; 
       try solve [inversion HE; subst; auto].
  Case "T_App".
    inversion HE; subst...
    (* Most of the cases are immediate by induction, 
       and [eauto] takes care of them *)
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T11...
      inversion HT1...  
Qed.

(** **** Exercise: 2 stars (subject_expansion_stlc) *)
(** An exercise in the [Types] chapter asked about the subject
    expansion property for the simple language of arithmetic and
    boolean expressions.  Does this property hold for STLC?  That is,
    is it always the case that, if [t ==> t'] and [has_type t' T],
    then [empty |- t \in T]?  If so, prove it.  If not, give a
    counter-example not involving conditionals.

(* FILL IN HERE *)
[]
*)


(* ###################################################################### *)
(** * Type Soundness *)

(** **** Exercise: 2 stars, optional (type_soundness) *)

(** Put progress and preservation together and show that a well-typed
    term can _never_ reach a stuck state.  *)

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.


  unfold not in Hnf.
  unfold not in Hnot_val.
  apply progress in Hhas_type.
  inv Hhas_type. apply Hnot_val in H. inv H.
  apply Hnf in H. inv H.

  generalize (preservation x0 y0 T Hhas_type H); intro.
  apply IHHmulti in H0. inv H0.
  assumption.
  assumption.
  (*
  unfold not in Hnf.
  generalize (progress x0 T Hhas_type); intro.
  inv H0.
  inv H.
  inv Hhas_type.
  *)
(*  
  destruct T.
  apply canonical_forms_bool in Hhas_type.
  inv Hhas_type.
  apply Hnot_val. auto.
  apply Hnot_val. auto.

  
  destruct x0 eqn:eq.
  inv Hhas_type. inv H1.
  inv Hhas_type.
  apply Hnf. eexists. constructor. 
*)  
Qed.

(*
Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
  
Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'.
  
Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
  
Corollary typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
  
Lemma substitution_preserves_typing : forall Gamma x U t v T,
     extend Gamma x U |- t \in T ->
     empty |- v \in U   ->
     Gamma |- [x:=v]t \in T.
  
Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.
*)



(* ###################################################################### *)
(** * Uniqueness of Types *)

(** **** Exercise: 3 stars (types_unique) *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)
(** Formalize this statement and prove it. *)

Lemma neq_type_arrow : forall Ta Tb Tc,
                         TArrow Ta Tb <> TArrow Ta Tc ->
                         Tb <> Tc.
Proof with eauto.
  intros.
  unfold not.
  intro.
  subst.
  contradiction H.
  reflexivity.
Qed.

(*
Lemma lem : forall Gamma i t t' T,
              extend Gamma i t |- t' \in T ->
              Gamma |- t' \in T -> False.
*)

Theorem types_unique : forall Gamma t T T',
  T <> T' ->
  Gamma |- t \in T ->
  Gamma |- t \in T' ->
  False.
Proof with auto.
  (*
  intros.
  generalize dependent T'.
  induction H0; intros.

  inv H1. rewrite H in H4. inversion H4. auto.

  inv H1. unfold not in H. apply neq_type_arrow in H. apply (IHhas_type T1 H H7).

  inv H1.

  inv H1. inv H4; inv H0_.
  rewrite H0 in H3. inversion H3...


  eapply IHhas_type.
*)


  intros Gamma t.
  induction t; intros; inv H0; inv H1.

  rewrite H4 in H3. inversion H3...

  generalize (IHt1 (TArrow T11 T) (TArrow T0 T')); intro H9;
  exploit H9... unfold not; intros; inversion H0; auto.

  apply neq_type_arrow in H.
  admit.


(*  
  apply IHt in H...
  destruct t0; inv H7; inv H6. rewrite H2 in H3. inversion H3. contradiction H.
  
  inv H7; inv H6.
  rewrite H0 in H3. inversion H3. contradiction H.
*)  
  

  auto. auto.

  eapply IHt2. eauto. auto. auto.

(*

  generalize (substitution_preserves_typing Gamma i t t0 (tvar i) T12); intro T.
  exploit T... 
  apply substitution_preserves_typing with (v:=t0) in H7.





  apply IHt in H... 
  
  apply IHt1 with (T:=(TArrow T11 T)) in H5. inv H5. 
  
  intros.
  generalize dependent T'.
  induction H0; intros.
  
     : forall (Gamma : partial_map ty) (x : id) (U : ty) (t v : tm) (T : ty),
       extend Gamma x U |- t \in T ->
       \empty |- v \in U -> Gamma |- [x := v]t \in T
                                                     
Lemma substitution_preserves_typing : forall Gamma x U t v T,
     extend Gamma x U |- t \in T ->
     empty |- v \in U   ->
     Gamma |- [x:=v]t \in T.
  
T_Abs:
  forall (Gamma : partial_map ty) (x : id) (T11 T12 : ty) (t12 : tm),
  extend Gamma x T11 |- t12 \in T12 ->
  Gamma |- tabs x T11 t12 \in TArrow T11 T12
*)
Qed.

(* ####################
peeked
https://github.com/panx/SF/blob/master/StlcProp.v
I don't see why only this method works...
########!!!!!!!!!!!!!!!!!! ***********)

Theorem types_unique' : forall Gamma t T,
  Gamma |- t \in T ->
  forall T', Gamma |- t \in T' ->
  T = T'.
Proof with eauto.
  intros.
  generalize dependent T'.
  induction H; intros...; inv H0.
  inv H0. rewrite H in H3. inversion H3...
  inv H0. apply IHhas_type in H6. subst...
  inv H1. apply IHhas_type1 in H5. inversion H5...
  inv H0...
  inv H0...
  inv H2. apply IHhas_type2 in H9...

(*  
  intros.
  generalize dependent T'.
  induction H; intros.
  inv H0. admit.
  apply IHhas_type in H. 
  
  induction t; intros;
  inv H; inv H0.
  admit.
  apply IHt1 with (T:=TArrow T0 T') in H4... inversion H4...
*)
Qed.
  

Theorem types_unique'' : forall Gamma t T,
  Gamma |- t \in T ->
  forall T', Gamma |- t \in T' ->
  T = T'.
Proof with eauto. 
  intros Gamma t. generalize dependent Gamma.
  induction t; intros; inv H; inv H0...
  rewrite H3 in H2. inversion H2...

  generalize (IHt1 Gamma (TArrow T11 T) H4 (TArrow T0 T') H3); intro. inversion H...

  generalize (IHt (extend Gamma i t) T12 H6 T0 H5); intro. inversion H...
Qed.

Theorem types_unique''' : forall Gamma t T T',
  T <> T' ->
  Gamma |- t \in T ->
  Gamma |- t \in T' ->
  False.
Proof with eauto.
(*  intros. apply (types_unique'' Gamma t T') in H0. auto. auto. *)
  intros Gamma t. generalize dependent Gamma.
  induction t; intros; inv H0; inv H1...
  rewrite H4 in H3. inversion H3...
  generalize (IHt1 Gamma (TArrow T11 T) (TArrow T0 T')); intro G; exploit G...
  unfold not; intro. inversion H0. rewrite H3 in H...

  generalize (IHt (extend Gamma i t) T12 T0); intro G; exploit G...
  unfold not; intros. rewrite H0 in H...
Qed.


                            
(* ###################################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 1 star (progress_preservation_statement) *)
(** Without peeking, write down the progress and preservation
    theorems for the simply typed lambda-calculus. *)

(*
progress : if some "tm" "has_type", then it is "value" or "step"s to another "tm".
preservation : if some "tm" has "step"ed to another "tm", the latter one has same "ty" with former one.

*)
(*
Ans :
     : forall (t : tm) (T : ty),
       \empty |- t \in T -> value t \/ (exists t' : tm, t ==> t')

     : forall (t t' : tm) (T : ty),
       \empty |- t \in T -> t ==> t' -> \empty |- t' \in T
*)
(* above theorems were defiend in only "empty" gamma? *)



(** **** Exercise: 2 stars (stlc_variation1) *)
(** Suppose we add a new term [zap] with the following reduction rule:
                         ---------                  (ST_Zap)
                         t ==> zap
and the following typing rule:
                      ----------------               (T_Zap)
                      Gamma |- zap : T
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

      - Progress

      - Preservation
*)

Module stlc_variation1.

Inductive tm : Type :=
    tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | zap : tm.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if eq_id_dec x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1)) 
  | tapp t1 t2 => 
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue => 
      ttrue
  | tfalse => 
      tfalse
  | tif t1 t2 t3 => 
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  | zap => zap
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true : 
      value ttrue
  | v_false : 
      value tfalse.

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' -> 
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Zap : forall t,
      t ==> zap
where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" 
  | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue" 
  | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T
  | T_Zap : forall Gamma T,
       Gamma |- zap \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_True" 
  | Case_aux c "T_False" | Case_aux c "T_If" ].

Hint Constructors has_type.

Theorem not_step_deterministic:
  ~(deterministic step).
Proof with eauto.
  unfold deterministic, not; intro.
  generalize (H (tif ttrue tfalse tfalse) tfalse zap); intro T; exploit T...
  intro. inv H0.
Qed.

Theorem progress :
  forall t T,
      \empty |- t \in T ->
      value t \/ (exists t', t ==> t').
Proof with eauto.
  induction t; intros...
Qed.

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
      appears_free_in x (tif t1 t2 t3).

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof with eauto.
  intros. 
  generalize dependent Gamma'.
  induction H; intros; auto.
(*  has_type_cases (induction H) Case; intros; auto. *)
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to 
       instantiate is [extend Gamma x T11] *)
    unfold extend. destruct (eq_id_dec x0 x1)... 
  Case "T_App".
    apply T_App with T11...  
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma. 
  generalize dependent T. 
  afi_cases (induction H) Case; 
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
Qed.

Theorem substitution_preserves_typing : forall Gamma x U t v T,
       extend Gamma x U |- t \in T ->
       \empty |- v \in U -> Gamma |- [x := v]t \in T.
Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
(*  t_cases (induction t) Case; intros T Gamma H; *)
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tvar".
    rename i into y. destruct (eq_id_dec x y).
    SCase "x=y".
      subst. 
      rewrite extend_eq in H2.
      inversion H2; subst. clear H2.
                  eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ T empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      apply T_Var. rewrite extend_neq in H2... 
  Case "tabs".
    rename i into y. apply T_Abs.
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
Qed.

Theorem preservation : forall t t' T,
       \empty |- t \in T -> t ==> t' -> \empty |- t' \in T.
Proof with eauto.
(*******!!!!!!!##################
            HERE, (remember (empty) as Gamma.) acts as crucial key...
WHY?????????????
*)
  intros. generalize dependent t'.
  remember (empty) as Gamma.  
(*  remember (@empty ty) as Gamma. *)
  induction H; intros; (* inv H0...; *)
  subst Gamma; subst; 
(*  inv HeqGamma; *)
  try solve [inv H0].
  inv H0...
  inv H0...

  inv H1; subst...
(*  
     : forall (Gamma : partial_map ty) (x : id) (U : ty) 
         (t v : STLC.tm) (T : ty),
       extend Gamma x U |- t \in T ->
       \empty |- v \in U -> Gamma |- [x := v]t \in T
*)
  eapply substitution_preserves_typing... inv H...
  inv H0...
  inv H0...
  inv H2...
  inv H0...

(*  
  intros. generalize dependent t'.
  induction H; intros...; (* inv H0...; *)
  try solve [inv H0...].
  inv H0...
  inv H0...

  admit.
  inv H0...
  inv H0...
  inv H2...
  inv H0...
*)
Qed.
(*
  remember (@empty ty) as Gamma. 
  intros t t' T HT. generalize dependent t'.   
  has_type_cases (induction HT) Case;
       intros t' HE; subst Gamma; subst; 
       try solve [inversion HE; subst; auto].
  Case "T_App".
    inversion HE; subst...
    (* Most of the cases are immediate by induction, 
       and [eauto] takes care of them *)
    SCase "ST_AppAbs".
      apply substitution_preserves_typing with T11...
      inversion HT1...
*)
(*
Theorem not_preservation :
  ~(forall t t' T,
   \empty |- t \in T -> t ==> t' -> \empty |- t' \in T).
Proof with eauto.
  unfold not; intro.
  generalize (H (tapp (tabs x TBool (tvar x)) ttrue) (*[x := ttrue](tvar x)*)
                zap
(*                (subst x ttrue (tvar x)) *)
                TBool
             );
  intro T; exploit T.
  eapply T_App...
  constructor...
  intro.
  inv H0.
    
  apply T_App with (T11:=TBool).
  constructor. constructor. rewrite extend_eq. 


  generalize (H (tapp (tif ttrue tfalse tfalse) ttrue) (tapp tfalse ttrue)
             );
  intro T; exploit T.

  intro. inv H0.
Qed.
  | T_Abs : forall (Gamma : partial_map ty) (x : id) 
              (T11 T12 : ty) (t12 : tm),
            extend Gamma x T11 |- t12 \in T12 ->
            Gamma |- tabs x T11 t12 \in TArrow T11 T12
                value v2 -> tapp (tabs x T t12) v2 ==> [x := v2]t12
*)

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.


  unfold not in Hnf.
  unfold not in Hnot_val.
  apply progress in Hhas_type.
  inv Hhas_type. apply Hnot_val in H. inv H.
  apply Hnf in H. inv H.

  generalize (preservation x0 y0 T Hhas_type H); intro.
  apply IHHmulti in H0. inv H0.
  assumption.
  assumption.
Qed.

End stlc_variation1.

(** **** Exercise: 2 stars (stlc_variation2) *)
(** Suppose instead that we add a new term [foo] with the following reduction rules:
                       -----------------                (ST_Foo1)
                       (\x:A. x) ==> foo 

                         ------------                   (ST_Foo2)
                         foo ==> true
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

      - Progress

      - Preservation

[]
*)

Module stlc_variation2.

Inductive tm : Type :=
    tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | foo : tm.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if eq_id_dec x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1)) 
  | tapp t1 t2 => 
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue => 
      ttrue
  | tfalse => 
      tfalse
  | tif t1 t2 t3 => 
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  | zap => zap
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true : 
      value ttrue
  | v_false : 
      value tfalse.

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' -> 
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Foo1 : forall x A,
      (tabs x A (tvar x)) ==> foo
  | ST_Foo2 :
      foo ==> ttrue

where "t1 '==>' t2" := (step t1 t2).
(*
                       -----------------                (ST_Foo1)
                       (\x:A. x) ==> foo 

                         ------------                   (ST_Foo2)
                         foo ==> true
*)
                         
Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" 
  | Case_aux c "ST_App2" | Case_aux c "ST_IfTrue" 
  | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_True" 
  | Case_aux c "T_False" | Case_aux c "T_If" ].

Hint Constructors has_type.

Theorem not_step_deterministic:
  ~(deterministic step).
Proof with eauto.
  unfold deterministic, not; intro.
  generalize (H (tapp (tabs x TBool (tvar x)) ttrue) (subst x ttrue (tvar x))); intro T; exploit T...
  intro. inv H0.
Qed.

Lemma canonical_forms_bool : forall t,
  empty |- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Theorem progress :
  forall t T,
      \empty |- t \in T ->
      value t \/ (exists t', t ==> t').
Proof with eauto.
  induction t; intros; inv H...
  inv H2.
  generalize H3; intro.
  generalize H5; intro.
  apply IHt1 in H3.
  apply IHt2 in H5.
  right.
  inv H3; inv H5.
  inv H0; inv H...
  inv H2. eexists...
  inv H. eexists...
  inv H. eexists...

  right.
  generalize H4; intro.
  generalize H6; intro.
  generalize H7; intro.
  apply IHt1 in H4.
  apply IHt2 in H6.
  apply IHt3 in H7.
  inv H4.
  apply canonical_forms_bool in H...
  inv H; eexists...
  inv H; eexists...
Qed. 


Theorem not_preservation : ~(forall t t' T,
       \empty |- t \in T -> t ==> t' -> \empty |- t' \in T).
Proof with eauto.
  unfold not; intro.
  generalize (H (tabs x TBool (tvar x)) foo); intro T; exploit T.
  repeat constructor... 
  constructor.
  intro.
  inv H0.
Qed.  

End stlc_variation2.

(** **** Exercise: 2 stars (stlc_variation3) *)
(** Suppose instead that we remove the rule [ST_App1] from the [step]
    relation. Which of the following properties of the STLC remain
    true in the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

      - Progress

      - Preservation

[]
*)

Module stlc_variation3.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' -> 
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)

where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Theorem step_deterministic :
  deterministic step.
Proof with auto.
  unfold deterministic.
  intros.
  generalize dependent y2.
  induction H; intros...; inv H0...

  inv H0. auto. inv H3. inv H... inv H5... inv H5. inv H5.

  inv H1... inv H... inv H5...
  inv H0... inv H0. inv H0. apply IHstep in H6. subst...

  inv H0... inv H4.
  inv H0... inv H4.
  inv H0... inv H. inv H. apply IHstep in H5. subst...
Qed.

Theorem not_progress :
  ~(forall t T,
      \empty |- t \in T ->
      value t \/ (exists t', t ==> t')).
Proof with eauto.
  unfold not; intros.
  generalize (H (tapp (tif ttrue (tabs x TBool (tvar x))
                                 (tabs x TBool (tvar x)))
                           ttrue) TBool); intro T; exploit T...
  eapply T_App... constructor...
  intro. inv H0. inv H1. inv H1. inv H0. inv H5.
Qed.


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
      appears_free_in x (tif t1 t2 t3).

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof with eauto.
  intros. 
  generalize dependent Gamma'.
  induction H; intros; auto.
(*  has_type_cases (induction H) Case; intros; auto. *)
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to 
       instantiate is [extend Gamma x T11] *)
    unfold extend. destruct (eq_id_dec x0 x1)... 
  Case "T_App".
    apply T_App with T11...  
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma. 
  generalize dependent T. 
  afi_cases (induction H) Case; 
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
Qed.

Theorem substitution_preserves_typing : forall Gamma x U t v T,
       extend Gamma x U |- t \in T ->
       \empty |- v \in U -> Gamma |- [x := v]t \in T.
Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
(*  t_cases (induction t) Case; intros T Gamma H; *)
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tvar".
    rename i into y. destruct (eq_id_dec x y).
    SCase "x=y".
      subst. 
      rewrite extend_eq in H2.
      inversion H2; subst. clear H2.
                  eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ T empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      apply T_Var. rewrite extend_neq in H2... 
  Case "tabs".
    rename i into y. apply T_Abs.
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
Qed.

Theorem preservation : forall t t' T,
       \empty |- t \in T -> t ==> t' -> \empty |- t' \in T.
Proof with eauto.
  intros. generalize dependent t'.
  remember (empty) as Gamma.  
(*  remember (@empty ty) as Gamma. *)
  induction H; intros; (* inv H0...; *)
  subst Gamma; subst; 
(*  inv HeqGamma; *)
  try solve [inv H0].
  inv H1...
  eapply substitution_preserves_typing... inv H...
  inv H2...
Qed.

End stlc_variation3.



(** **** Exercise: 2 stars, optional (stlc_variation4) *)
(** Suppose instead that we add the following new rule to the reduction relation:
            ----------------------------------        (ST_FunnyIfTrue)
            (if true then t1 else t2) ==> true
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

      - Progress

      - Preservation

*)

Module stlc_variation4.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' -> 
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_FunnyIfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> ttrue
(*      (if true then t1 else t2) ==> true *)
where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Theorem not_step_deterministic :
  not (deterministic step).
Proof with eauto.
  unfold deterministic, not; intros.
  generalize (H (tif ttrue tfalse tfalse) tfalse ttrue); intro T; exploit T...
  intro. inv H0.
Qed.

Lemma canonical_forms_bool : forall t,
  empty |- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Theorem progress :
  forall t T,
      \empty |- t \in T ->
      value t \/ (exists t', t ==> t').
Proof with eauto.
  induction t; intros; inv H...
  inv H2.
  generalize H3; intro.
  generalize H5; intro.
  apply IHt1 in H3.
  apply IHt2 in H5.
  right.
  inv H3; inv H5.
  inv H0; inv H...
  inv H2. eexists...
  inv H. eexists...
  inv H. eexists...

  right.
  generalize H4; intro.
  generalize H6; intro.
  generalize H7; intro.
  apply IHt1 in H4.
  apply IHt2 in H6.
  apply IHt3 in H7.
  inv H4.
  apply canonical_forms_bool in H...
  inv H; eexists...
  inv H; eexists...
Qed.

Theorem not_preservation : ~(forall t t' T,
       \empty |- t \in T -> t ==> t' -> \empty |- t' \in T).
Proof with eauto.
  unfold not; intro.
  generalize (H (tif ttrue
                     (tabs x TBool (tvar x))
                     (tabs x TBool (tvar x)))
                ttrue
                (TArrow TBool TBool)); intro T; exploit T.
  repeat constructor. apply ST_FunnyIfTrue.
  intro. inv H0.
Qed.


End stlc_variation4.

(** **** Exercise: 2 stars, optional (stlc_variation5) *)
(** Suppose instead that we add the following new rule to the typing relation:
                 Gamma |- t1 \in Bool->Bool->Bool
                     Gamma |- t2 \in Bool
                 ------------------------------          (T_FunnyApp)
                    Gamma |- t1 t2 \in Bool
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

      - Progress

      - Preservation

*)

Module stlc_variation5.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T
  | T_FunnyApp : forall Gamma t1 t2,
      Gamma |- t1 \in (TArrow (TArrow TBool TBool) TBool) ->
      Gamma |- t2 \in TBool ->
      Gamma |- (tapp t1 t2) \in TBool
                                         
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

(*
                 Gamma |- t1 \in Bool->Bool->Bool
                     Gamma |- t2 \in Bool
                 ------------------------------          (T_FunnyApp)
                    Gamma |- t1 t2 \in Bool
*)

Hint Constructors has_type.

(* determinstic step : not changed *)

(*
Theorem not_progress :
  ~(forall t T,
      \empty |- t \in T ->
      value t \/ (exists t', t ==> t')).
Proof with eauto.
  unfold not; intros.
  generalize (H
  (tapp (tabs x (TArrow TBool TBool) (ttrue))
(*   (tapp (tvar x) idB) *)
(* ttrue *)
  (tif ttrue tfalse tfalse)
)
  TBool);
    intro T; exploit T.
  apply T_FunnyApp...


  
  intro.
  inv H0.
  inv H1...

  inv H1... 
  inv H0...
  inv H6. inv H4. inv H3. inv H5.
  
    ST_AppAbs : forall (x : id) (T : ty) (t12 v2 : tm),
                value v2 -> tapp (tabs x T t12) v2 ==> [x := v2]t12
  | ST_App1 : forall t1 t1' t2 : tm, t1 ==> t1' -> tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2' : tm,
              value v1 -> t2 ==> t2' -> tapp v1 t2 ==> tapp v1 t2'
  | ST_IfTrue : forall t1 t2 : tm, tif ttrue t1 t2 ==> t1
Qed.

      Gamma |- t1 \in (TArrow (TArrow TBool TBool) TBool) ->
      Gamma |- t2 \in TBool ->
      Gamma |- (tapp t1 t2) \in TBool
*)

Lemma canonical_forms_bool : forall t,
  empty |- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x0. exists t0.  auto.
Qed.

Theorem progress :
  forall t T,
      \empty |- t \in T ->
      value t \/ (exists t', t ==> t').
Proof with eauto.
  induction t; intros; inv H...
  inv H2.
  generalize H3; intro.
  generalize H5; intro.
  apply IHt1 in H3.
  apply IHt2 in H5.
  right.
  inv H3; inv H5.
  inv H0; inv H...
  inv H2. eexists...
  inv H. eexists...
  inv H. eexists...

  right.
  generalize H3; intro; apply IHt1 in H3.
  generalize H5; intro; apply IHt2 in H5.
  inv H3; inv H5.
  apply (canonical_forms_fun t1 (TArrow TBool TBool) TBool) in H...
  inv H. inv H3.
  eexists...

  inv H2; eexists...
  inv H; eexists...
  inv H; eexists...
  
  right.
  generalize H4; intro.
  generalize H6; intro.
  generalize H7; intro.
  apply IHt1 in H4.
  apply IHt2 in H6.
  apply IHt3 in H7.
  inv H4.
  apply canonical_forms_bool in H...
  inv H; eexists...
  inv H; eexists...
Qed.

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
      appears_free_in x (tif t1 t2 t3).

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof with eauto.
  intros. 
  generalize dependent Gamma'.
  induction H; intros; auto.
(*  has_type_cases (induction H) Case; intros; auto. *)
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to 
       instantiate is [extend Gamma x T11] *)
    unfold extend. destruct (eq_id_dec x0 x1)... 
  Case "T_App".
    apply T_App with T11...  
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma. 
  generalize dependent T. 
  afi_cases (induction H) Case; 
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
Qed.

Theorem substitution_preserves_typing : forall Gamma x U t v T,
       extend Gamma x U |- t \in T ->
       \empty |- v \in U -> Gamma |- [x := v]t \in T.
Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
(*  t_cases (induction t) Case; intros T Gamma H; *)
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tvar".
    rename i into y. destruct (eq_id_dec x y).
    SCase "x=y".
      subst. 
      rewrite extend_eq in H2.
      inversion H2; subst. clear H2.
                  eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ T empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      apply T_Var. rewrite extend_neq in H2... 
  Case "tabs".
    rename i into y. apply T_Abs.
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
Qed.


Example tmp : 
    exists t', (tapp (tabs x (TArrow TBool TBool) ((tif ttrue ttrue ttrue)))
        (ttrue)) ==> t'.
Proof.
  eexists... info_eauto.
Qed.

Example tmp2 :
    (tapp (tabs x (TArrow TBool TBool) ((tif ttrue ttrue ttrue)))
        (ttrue)) ==> [x := ttrue] (tif ttrue ttrue ttrue).
Proof. info_auto. Qed.

Inductive not_appears_in : id -> tm -> Prop :=
  | nai_var : forall x y,
                x <> y ->
                not_appears_in x (tvar y)
  | nai_app : forall x t1 t2,
                not_appears_in x t1 ->
                not_appears_in x t2 ->
                not_appears_in x (tapp t1 t2)
  | nai_abs : forall x y T t,
                x <> y ->
                not_appears_in x t ->
                not_appears_in x (tabs y T t)
  | nai_if : forall x t1 t2 t3,
                not_appears_in x t1 ->
                not_appears_in x t2 ->
                not_appears_in x t3 ->
                not_appears_in x (tif t1 t2 t3).

Hint Constructors not_appears_in.

(*
Ltac neq_eq_id_dec a b H := destruct (eq_id_dec a b); subst. contradiction H.
*)

(*
Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
  end.
*)
(*
Ltac find_neq :=
  match goal with
      H1: ?E = true |- _ => simpl.
  end.
*)
                          
Lemma not_appears_in_subst : forall x s t Gamma T,
                               not_appears_in x t ->
                               (Gamma |- [x := s]t \in T <->
                               Gamma |- t \in T).
Proof with eauto.
  induction t; split; intros...
  inv H; inv H0...
    destruct (eq_id_dec x0 i); subst... contradiction H3... rewrite <- H...
    destruct (eq_id_dec x0 i); subst... contradiction H3... rewrite <- H...
    destruct (eq_id_dec x0 i); subst... contradiction H3... rewrite <- H...

    destruct (eq_id_dec x0 i); subst... contradiction H3... rewrite <- H2...
    destruct (eq_id_dec x0 i); subst... contradiction H3... rewrite <- H2...
    destruct (eq_id_dec x0 i); subst... contradiction H3... rewrite <- H...
    destruct (eq_id_dec x0 i); subst... contradiction H3... rewrite <- H...
    
  inv H; inv H0... unfold subst.
    destruct (eq_id_dec x0 i); subst... contradiction H3...

  inv H; inv H0...
  eapply IHt1 in H4. eapply IHt2 in H5.
  apply H4 in H3. apply H5 in H7.
  eapply T_App...

  eapply IHt1 in H4. eapply IHt2 in H5.
  apply H4 in H3. apply H5 in H7.
  eapply T_FunnyApp...

  inv H; inv H0...
    eapply IHt1 in H4. eapply IHt2 in H5.
    apply H4 in H3. apply H5 in H7.
    simpl. eapply T_App...

    eapply IHt1 in H4. eapply IHt2 in H5.
    apply H4 in H3. apply H5 in H7.
    simpl. eapply T_FunnyApp...


  inv H0; inv H.
  eapply T_Abs.
  destruct (eq_id_dec x0 i); subst...
  eapply IHt in H5. apply H5 in H6...

  inv H; inv H0...
  eapply IHt in H6.
  simpl. destruct (eq_id_dec x0 i); subst. contradiction H4...
  constructor. apply H6 in H7...

  inv H; inv H0... eapply IHt1 in H5. eapply IHt2 in H6. eapply IHt3 in H7.
  apply H5 in H4. apply H6 in H9. apply H7 in H10.
  constructor...

  inv H; inv H0...
  eapply IHt1 in H5. apply H5 in H4.
  eapply IHt2 in H6. apply H6 in H9.
  eapply IHt3 in H7. apply H7 in H10.
  simpl. constructor...
Qed.

(*
Lemma not_congruent_implies_not_appears_in : forall t Gamma x s,
  Gamma |- s \in TBool ->
  Gamma |- tabs x (TArrow TBool TBool) t
                \in TArrow (TArrow TBool TBool) TBool ->
  not_appears_in x t.
Proof with eauto.
  induction t; simpl; intros.
  destruct (eq_id_dec x0 i); subst... inv H0. inv H3. rewrite extend_eq in H2. inversion H2.
  inv H0; inv H3.
  constructor. eapply IHt1... apply T_Abs in H4.

Qed.
*)

Lemma not_congruent_implies_not_appears_in : forall t Gamma x s,
  Gamma |- s \in TBool ->
  value s ->
  tapp (tabs x (TArrow TBool TBool) t) s ==> [x := s] t ->
  Gamma |- tabs x (TArrow TBool TBool) t \in TArrow (TArrow TBool TBool) TBool ->
  not_appears_in x t.
Proof with eauto.
  induction t; simpl; intros.
  destruct (eq_id_dec x0 i); subst... inv H2. inv H5. rewrite extend_eq in H4. inversion H4.
  constructor. eapply IHt1... inv H2.
  Admitted.

(*                                 
  t2 : tm
  H0 : \empty |- t2 \in TBool
  IHhas_type2 : \empty = \empty ->
                forall t' : tm, t2 ==> t' -> \empty |- t' \in TBool
  x0 : id
  t12 : tm
  H5 : extend \empty x0 (TArrow TBool TBool) |- t12 \in TBool
  IHhas_type1 : \empty = \empty ->
                forall t' : tm,
                tabs x0 (TArrow TBool TBool) t12 ==> t' ->
                \empty |- t' \in TArrow (TArrow TBool TBool) TBool
  M : \empty |- tabs x0 (TArrow TBool TBool) t12 \in
      TArrow (TArrow TBool TBool) TBool
  H7 : value t2
  M1 : tapp (tabs x0 (TArrow TBool TBool) t12) t2 ==> [x0 := t2]t12
  ============================
   \empty |- [x0 := t2]t12 \in TBool
*)


(*
  t1 : tm
  t2 : tm
  t' : tm
  H1 : tapp t1 t2 ==> t'
  H : \empty |- t1 \in TArrow (TArrow TBool TBool) TBool
  H0 : \empty |- t2 \in TBool
  IHhas_type1 : \empty = \empty ->
                forall t'0 : tm,
                t1 ==> t'0 ->
                \empty |- t'0 \in TArrow (TArrow TBool TBool) TBool
  IHhas_type2 : \empty = \empty ->
                forall t'0 : tm, t2 ==> t'0 -> \empty |- t'0 \in TBool
  M : \empty |- t1 \in TArrow (TArrow TBool TBool) TBool
  M1 : tapp t1 t2 ==> t'
  ============================
   \empty |- t' \in TBool
*)

(*
  t2 : tm
  H0 : \empty |- t2 \in TBool
  IHhas_type2 : \empty = \empty ->
                forall t' : tm, t2 ==> t' -> \empty |- t' \in TBool
  x0 : id
  T : ty
  t12 : tm
  H5 : value t2
  H : \empty |- tabs x0 T t12 \in TArrow (TArrow TBool TBool) TBool
  IHhas_type1 : \empty = \empty ->
                forall t' : tm,
                tabs x0 T t12 ==> t' ->
                \empty |- t' \in TArrow (TArrow TBool TBool) TBool
  ============================
   \empty |- [x0 := t2]t12 \in TBool
*)
(*
Lemma abnea : forall t1 t2 x Gamma,
                Gamma |- t2 \in TBool ->
                value t2 ->
                Gamma |- tabs x (TArrow TBool TBool) t1 \in TArrow (TArrow TBool TBool) TBool ->
                not_appears_in x t1.
Proof with eauto.
  induction t1; simpl; intros.
  admit.
  constructor. eapply IHt1_1... inv H1. inv H4.
Qed.
*)                     

Theorem preservation : forall t t' T,
       \empty |- t \in T -> t ==> t' -> \empty |- t' \in T.
Proof with eauto.
  intros. generalize dependent t'.
  remember (empty) as Gamma.  
(*  remember (@empty ty) as Gamma. *)
  induction H; intros; (* inv H0...; *)
  subst Gamma; subst; 
(*  inv HeqGamma; *)
  try solve [inv H0].
  inv H1...
  eapply substitution_preserves_typing... inv H...
  inv H2...

  generalize H; intro M.
  generalize H1; intro M1.  
  inv H; inv H1...
  assert(G : not_appears_in x0 t12).
  apply not_congruent_implies_not_appears_in with (Gamma:=empty) (s:=t2)...
  apply not_appears_in_subst...
  apply substitution_preserves_typing with (v:=idB) in H5.
  apply not_appears_in_subst in H5...
  constructor...
(*  inv H1... *)
(*
  generalize H; intro M.
  generalize H1; intro M1.
  inv H1... inv H...
  apply substitution_preserves_typing with (TBool)...  
  eapply substitution_preserves_typing...
  apply substitution_preserves_typing with (TBool)...
  eapply context_invariance. apply H3.
  intros. eapply free_in_context in H... inv H.
  destruct (eq_id_dec x0 x1); subst. rewrite extend_eq in H1. inv H1.
  rewrite extend_eq. rewrite extend_eq.

       appears_free_in x t ->
       Gamma |- t \in T -> exists T' : ty, Gamma x = Some T'  
  
  apply context_invariance with (empty).
  
  eapply substitution_preserves_typing. apply H3.

  apply context_invariance with (empty).
  
  inv H1... inv H... eapply substitution_preserves_typing... 

  generalize (T_FunnyApp empty t1 t2); intro T; exploit T...
  intro; clear T.
  inv H2... inv H6; inv H... inversion H5.
  inv H1... eapply substitution_preserves_typing...
  inv H1... inv H1...
  
(*                                             
  inv H1...

  | T_FunnyApp : forall (Gamma : context) (t1 t2 : tm),
                 Gamma |- t1 \in TArrow (TArrow TBool TBool) TBool ->
                 Gamma |- t2 \in TBool -> Gamma |- tapp t1 t2 \in TBool  
  eapply T_FunnyApp.
  
  inv H1; inv H; inv H0...
  inv H.
  eapply substitution_preserves_typing... inv H5.
  eapply substitution_preserves_typing...
  
  inv H1... eapply substitution_preserves_typing...
*)
  Abort.
*)
Qed.

(*
Theorem not_preservation : ~(forall T t t',
       \empty |- t \in T -> t ==> t' -> \empty |- t' \in T).
Proof with eauto.
  unfold not; intro.
  remember (tapp (tabs x (TArrow TBool TBool) (ttrue))
                 (tapp (tvar x) ttrue)
           ) as t.
  generalize (H TBool t); intro T; exploit T.
  subst. apply T_FunnyApp.
  constructor. constructor. constructor. constructor.
  constructor.
  
  unfold not; intro.
  remember (tapp (tabs x (TArrow TBool TBool) (ttrue))
                 ttrue
           ) as t.
  generalize (H TBool t); intro T; exploit T.
  subst. apply T_FunnyApp...
  subst. apply ST_AppAbs...
  intro. inv H0.



  generalize (H
  (tapp (tabs x (TArrow TBool TBool) ((tif ttrue ttrue ttrue)))
        (ttrue))
  );

  intro T; exploit T...


  value v2 -> tapp (tabs x T t12) v2 ==> [x := v2]t12
  intro. inv H0.
  apply T_FunnyApp...  
Qed.
*)


End stlc_variation5.


(** **** Exercise: 2 stars, optional (stlc_variation6) *)
(** Suppose instead that we add the following new rule to the typing relation:
                     Gamma |- t1 \in Bool
                     Gamma |- t2 \in Bool
                    ---------------------               (T_FunnyApp')
                    Gamma |- t1 t2 \in Bool
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

      - Progress

      - Preservation

*)


Module stlc_variation6.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T
  | T_FunnyApp' : forall Gamma t1 t2,
      Gamma |- t1 \in TBool->
      Gamma |- t2 \in TBool ->
      Gamma |- (tapp t1 t2) \in TBool
                                         
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* step : same *)

Lemma canonical_forms_bool : forall t,
  empty |- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x0. exists t0.  auto.
Qed.

Theorem not_progress :
  ~(forall t T,
      \empty |- t \in T ->
      value t \/ (exists t', t ==> t')).
Proof.
  unfold not; intros.
  generalize (H (tapp ttrue ttrue) TBool); intro T; exploit T; auto.
  intro. inv H0. inv H1. inv H1. inv H0. inv H4. inv H5.
Qed.

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
      appears_free_in x (tif t1 t2 t3).

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof with eauto.
  intros. 
  generalize dependent Gamma'.
  induction H; intros; auto.
(*  has_type_cases (induction H) Case; intros; auto. *)
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to 
       instantiate is [extend Gamma x T11] *)
    unfold extend. destruct (eq_id_dec x0 x1)... 
  Case "T_App".
    apply T_App with T11...  
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma. 
  generalize dependent T. 
  afi_cases (induction H) Case; 
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
Qed.

Theorem substitution_preserves_typing : forall Gamma x U t v T,
       extend Gamma x U |- t \in T ->
       \empty |- v \in U -> Gamma |- [x := v]t \in T.
Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
(*  t_cases (induction t) Case; intros T Gamma H; *)
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tvar".
    rename i into y. destruct (eq_id_dec x y).
    SCase "x=y".
      subst. 
      rewrite extend_eq in H2.
      inversion H2; subst. clear H2.
                  eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ T empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      apply T_Var. rewrite extend_neq in H2... 
  Case "tabs".
    rename i into y. apply T_Abs.
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
Qed.

Theorem preservation : forall t t' T,
       \empty |- t \in T -> t ==> t' -> \empty |- t' \in T.
Proof with eauto.
  intros. generalize dependent t'.
  remember (empty) as Gamma.  
  induction H; intros; subst Gamma; subst; 
  try solve [inv H0].
  inv H1...
  eapply substitution_preserves_typing... inv H...
  inv H2...

  generalize H; intro M.
  generalize H1; intro M1.  
  inv H; inv H1...
Qed.

End stlc_variation6.


(** **** Exercise: 2 stars, optional (stlc_variation7) *)
(** Suppose we add the following new rule to the typing
    relation of the STLC:
                         ------------------- (T_FunnyAbs)
                         |- \x:Bool.t \in Bool
    Which of the following properties of the STLC remain true in
    the presence of this rule?  For each one, write either
    "remains true" or else "becomes false." If a property becomes
    false, give a counterexample.

      - Determinism of [step]

      - Progress

      - Preservation

[]
*)

Module stlc_variation7.

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).
    
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T
  | T_FunnyAbs : forall Gamma x t,
       Gamma |- (tabs x TBool t) \in TBool

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* step : same *)

(*
Lemma canonical_forms_bool : forall t,
  empty |- t \in TBool ->
  value t ->
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros t HT HVal.
  inversion HVal; intros; subst; try inversion HT; auto.
Qed.
*)

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  exists x0. exists t0.  auto.
Qed.

Theorem progress :
  ~(forall t T,
      \empty |- t \in T ->
      value t \/ (exists t', t ==> t')).
Proof.
  unfold not; intro.
  generalize (H (tif (tabs x TBool ttrue) tfalse tfalse) TBool); intro T; exploit T; auto.
  intro. inv H0. inv H1. inv H1. inv H0. inv H5.
Qed.

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
      appears_free_in x (tif t1 t2 t3).

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof with eauto.
  intros. 
  generalize dependent Gamma'.
  induction H; intros; auto.
(*  has_type_cases (induction H) Case; intros; auto. *)
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to 
       instantiate is [extend Gamma x T11] *)
    unfold extend. destruct (eq_id_dec x0 x1)... 
  Case "T_App".
    apply T_App with T11...  
Qed.

(*
Theorem not_preservation : ~(forall t t' T,
       \empty |- t \in T -> t ==> t' -> \empty |- t' \in T).
Proof with eauto.
  unfold not; intro.
  generalize (H
                (tif (tif ttrue (tabs x TBool ttrue) tfalse) ttrue ttrue)
                (tif (tabs x TBool ttrue) ttrue ttrue)
                TBool
             );
    intro T; exploit T.
  apply T_If. apply T_If... constructor. constructor.
  repeat constructor.
  intro. inv H0. inv H5.
Qed.
                 Gamma |- tabs x TBool t \in TBool
*)

Lemma free_in_context :
  ~(forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T').
Proof.
  unfold not; intros.
  generalize (H y (tabs x TBool (tvar y))
                TBool
                (extend empty y TBool)
             ); intro T; exploit T.
  constructor. unfold not; intro; inv H0. constructor.
  constructor. intro.
  inv H0. inv H1.
  
Abort.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma. 
  generalize dependent T. 
  afi_cases (induction H) Case; 
         intros; try solve [inversion H0; eauto].
  Case "afi_abs".
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
Abort.

Theorem substitution_preserves_typing : forall Gamma x U t v T,
       extend Gamma x U |- t \in T ->
       \empty |- v \in U -> Gamma |- [x := v]t \in T.
Proof with eauto.
  Admitted.

Theorem preservation : forall t t' T,
       \empty |- t \in T -> t ==> t' -> \empty |- t' \in T.
Proof with eauto.
  intros. generalize dependent t'.
  remember (empty) as Gamma.  
  induction H; intros; subst Gamma; subst; 
  try solve [inv H0].
  inv H1...
  eapply substitution_preserves_typing... inv H...
  inv H2...
Qed.

End stlc_variation7.


End STLCProp.

(* ###################################################################### *)
(* ###################################################################### *)
(** ** Exercise: STLC with Arithmetic *) 

(** To see how the STLC might function as the core of a real
    programming language, let's extend it with a concrete base
    type of numbers and some constants and primitive
    operators. *)

Module STLCArith.

(** To types, we add a base type of natural numbers (and remove
    booleans, for brevity) *)

Inductive ty : Type :=
  | TArrow : ty -> ty -> ty
  | TNat   : ty.

(** To terms, we add natural number constants, along with
    successor, predecessor, multiplication, and zero-testing... *)

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | tnat  : nat -> tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tmult : tm -> tm -> tm
  | tif0  : tm -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" 
  | Case_aux c "tabs" | Case_aux c "tnat" 
  | Case_aux c "tsucc" | Case_aux c "tpred"
  | Case_aux c "tmult" | Case_aux c "tif0" ].

(** **** Exercise: 4 stars (stlc_arith) *)
(** Finish formalizing the definition and properties of the STLC extended
    with arithmetic.  Specifically:

    - Copy the whole development of STLC that we went through above (from
      the definition of values through the Progress theorem), and
      paste it into the file at this point.

    - Extend the definitions of the [subst] operation and the [step]
      relation to include appropriate clauses for the arithmetic operators.

    - Extend the proofs of all the properties (up to [soundness]) of
      the original STLC to deal with the new syntactic forms.  Make
      sure Coq accepts the whole file. *)

(* FILL IN HERE *)
(** [] *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' => 
      if eq_id_dec x x' then s else t
  | tabs x' T t1 => 
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1)) 
  | tapp t1 t2 => 
      tapp ([x:=s] t1) ([x:=s] t2)
  | tnat n => 
      tnat n
  | tsucc t => 
      tsucc ([x:=s] t)
  | tpred t => 
      tpred ([x:=s] t)
  | tmult t1 t2 =>
      tmult ([x:=s] t1) ([x:=s] t2)
  | tif0 t1 t2 t3 => 
      tif0 ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_nat : forall n,
      value (tnat n).


(*
    nv_zero : nvalue tzero
  | nv_succ : forall t : Types.tm, nvalue t -> nvalue (Types.tsucc t)
*)
Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' -> 
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif0 (tnat 0) t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2 n,
      (tif0 (tnat (S n)) t1 t2) ==> t1                            
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif0 t1 t2 t3) ==> (tif0 t1' t2 t3)
  | ST_Succ : forall t t',
      t ==> t' ->
      tsucc t ==> tsucc t'
  | ST_Pred : forall t t',
      t ==> t' -> 
      tpred t ==> tpred t'
  | ST_Mult1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tmult t1 t2 ==> tmult t1' t2
  | ST_Mult2 : forall t1 t2 t2',
      value t1 ->
      t2 ==> t2' ->
      tmult t1 t2 ==> tmult t1 t2'
  | ST_NatSucc : forall n,
      tsucc (tnat n) ==> (tnat (S n))
  | ST_NatPredZero :
      tpred (tnat 0) ==> (tnat 0)
  | ST_NatPred : forall n,
      tpred (tnat (S n)) ==> (tnat n)
  | ST_NatMult : forall n m,
      tmult (tnat n) (tnat m) ==> (tnat (mult n m))
(*            
  | ST_NatPredSucc : forall n,
      tpred (tsucc (tnat n)) ==> (tnat n)
*)
where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" 
  | Case_aux c "ST_App2"
  | Case_aux c "ST_IfTrue"
  | Case_aux c "ST_IfFalse"             
  | Case_aux c "ST_If"
  | Case_aux c "ST_Succ"
  | Case_aux c "ST_Pred"
  | Case_aux c "ST_Mult1"
  | Case_aux c "ST_Mult2"
  | Case_aux c "ST_NatSucc"
  | Case_aux c "ST_NatPredZero"
  | Case_aux c "ST_NatPred"
  | Case_aux c "ST_NatMult"             
(*  | Case_aux c "ST_NatPredSucc" *)
             ].

Hint Constructors step.

Theorem step_deterministic :
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros.
  generalize dependent y2.
  step_cases (induction H) Case; intros...; inv H0...
(*  induction H; intros...; inv H0... *)
  Case "ST_AppAbs".
  inv H0... inv H4... inv H3.
  inv H; inv H5...

  Case "ST_App1".
  inv H0... inv H... apply IHstep in H4; subst...
  inv H; inv H3...
  Case "ST_App2".
  inv H1... inv H5; inv H... inv H0. inv H0. inv H; inv H5...
  apply IHstep in H6; subst...

  Case "ST_IfTrue".
  inv H0... inv H4...

  Case "ST_IfFalse".
  inv H0... inv H4...
  
  Case "ST_If".
  inv H0... inv H... inv H. apply IHstep in H5; subst...
  
  Case "ST_Succ".
  inv H0... apply IHstep in H2; subst... inv H.
  
  Case "ST_Pred".
  inv H0... apply IHstep in H2; subst...
  inv H. inv H. 
  
  Case "ST_Mult1".
  inv H0... apply IHstep in H4; subst... inv H3; inv H...
  inv H...

  Case "ST_Mult2".
  inv H1... inv H; inv H5. apply IHstep in H6; subst...
  inv H0...

  Case "ST_NatSucc".
  inv H0... inv H1. inv H0... inv H1.

  Case "ST_NatPred".
  inv H0... inv H1...

  Case "ST_NatMult".
  inv H0... inv H3. inv H4.
Qed.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Definition context := partial_map ty.
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      extend Gamma x T11 |- t12 \in T12 -> 
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 -> 
      Gamma |- t2 \in T11 -> 
      Gamma |- tapp t1 t2 \in T12
  | T_Nat : forall Gamma n,
       Gamma |- (tnat n) \in TNat
  | T_If0 : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TNat ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif0 t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" 
  | Case_aux c "T_App" | Case_aux c "T_If0"
  | Case_aux c "T_Nat"
  ].

Hint Constructors has_type.

Lemma canonical_forms_nat : forall t,
  empty |- t \in TNat ->
  value t ->
  exists n, t = tnat n.
Proof with eauto.
  intros t HT HVal.
  inv HVal. inv HT. eexists...
Qed.

Lemma canonical_forms_fun : forall t T1 T2,
  empty |- t \in (TArrow T1 T2) ->
  value t ->
  exists x u, t = tabs x T1 u.
Proof.
  intros t T1 T2 HT HVal.
  inversion HVal; intros; subst; try inversion HT; subst; auto.
  inv HT... 
  exists x. exists t0.  auto.
Qed.

Theorem progress :
  forall t T,
      \empty |- t \in T ->
      value t \/ (exists t', t ==> t').
Proof with eauto.
  intros t.
  t_cases (induction t) Case; intros T Ht; auto.

  inv Ht. inversion H1.
  inv Ht.
  generalize H2; intro H1.
  generalize H4; intro H3.
  apply IHt1 in H2.
  apply IHt2 in H4.
  right.
  inv H4. inv H2.
  inv H1; inv H0.
  eexists. (*using it to early, right after right, will make next line not work *)
  apply ST_AppAbs...
  inv H0. eexists. apply ST_App1...
  inv H2. inv H. eexists. apply ST_App2...
  inv H. inv H0. eexists. apply ST_App1...

  inv Ht.
  inv Ht.
  inv Ht. 
  inv Ht. generalize H3; intro T1. apply IHt1 in H3. right. inv H3.
  apply canonical_forms_nat in T1. inv T1. eexists... destruct x...
  assumption. inv H. eexists...
Qed.

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
  | afi_if0_1 : forall x t1 t2 t3,
      appears_free_in x t1 ->
      appears_free_in x (tif0 t1 t2 t3)
  | afi_if0_2 : forall x t1 t2 t3,
      appears_free_in x t2 ->
      appears_free_in x (tif0 t1 t2 t3)
  | afi_if0_3 : forall x t1 t2 t3,
      appears_free_in x t3 ->
      appears_free_in x (tif0 t1 t2 t3)
  | afi_tsucc : forall x t,
      appears_free_in x t ->
      appears_free_in x (tsucc t)
  | afi_tpred : forall x t,
      appears_free_in x t ->
      appears_free_in x (tpred t)
  | afi_tmult1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tmult t1 t2)
  | afi_tmult2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tmult t1 t2)
.

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t T,
     Gamma |- t \in T  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
     Gamma' |- t \in T.
Proof with eauto.
  intros. 
  generalize dependent Gamma'.
  induction H; intros; auto.
(*  has_type_cases (induction H) Case; intros; auto. *)
  Case "T_Var".
    apply T_Var. rewrite <- H0...
  Case "T_Abs".
    apply T_Abs.
    apply IHhas_type. intros x1 Hafi.
    (* the only tricky step... the [Gamma'] we use to 
       instantiate is [extend Gamma x T11] *)
    unfold extend. destruct (eq_id_dec x x1)... 
  Case "T_App".
    apply T_App with T11...  
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof.
  intros x t T Gamma H H0. generalize dependent Gamma. 
  generalize dependent T. 
  induction H;
         intros; try solve [inversion H0; eauto].
    inversion H1; subst.
    apply IHappears_free_in in H7.
    rewrite extend_neq in H7; assumption.
Qed.

Theorem substitution_preserves_typing : forall Gamma x U t v T,
       extend Gamma x U |- t \in T ->
       \empty |- v \in U -> Gamma |- [x := v]t \in T.
Proof with eauto.
  intros Gamma x U t v T Ht Ht'.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T Gamma H;
(*  t_cases (induction t) Case; intros T Gamma H; *)
    (* in each case, we'll want to get at the derivation of H *)
    inversion H; subst; simpl...
  Case "tvar".
    rename i into y. destruct (eq_id_dec x y).
    SCase "x=y".
      subst. 
      rewrite extend_eq in H2.
      inversion H2; subst. clear H2.
                  eapply context_invariance... intros x Hcontra.
      destruct (free_in_context _ _ T empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      apply T_Var. rewrite extend_neq in H2... 
  Case "tabs".
    rename i into y. apply T_Abs.
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
Qed.

Theorem preservation : forall t t' T,
       \empty |- t \in T -> t ==> t' -> \empty |- t' \in T.
Proof with eauto.
  intros; generalize dependent t'.
  remember empty as Gamma.
  induction H; intros; subst; try solve [inv H0].
  inv H1... eapply substitution_preserves_typing. inv H...
  inv H...

  inv H2...
Qed.

Definition stuck (t:tm) : Prop :=
  (normal_form step) t /\ ~ value t.

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.


  unfold not in Hnf.
  unfold not in Hnot_val.
  apply progress in Hhas_type.
  inv Hhas_type. apply Hnot_val in H. inv H.
  apply Hnf in H. inv H.

  generalize (preservation x y T Hhas_type H); intro.
  apply IHHmulti in H0. inv H0.
  assumption.
  assumption.
Qed.

End STLCArith.

(* $Date: 2014-04-23 09:37:37 -0400 (Wed, 23 Apr 2014) $ *)

