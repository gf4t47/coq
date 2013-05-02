(** **** KE DING 8318 *)

(** * MoreCoq: More About Coq *)

Require Export Poly.

(** This chapter introduces several more Coq tactics that,
    together, allow us to prove many more theorems about the
    functional programs we are writing. *)

(* ###################################################### *)
(** * The [apply] Tactic *)

(** We often encounter situations where the goal to be proved is
    exactly the same as some hypothesis in the context or some
    previously proved lemma. *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n,o] = [n,p] ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* At this point, we could finish with 
     "[rewrite -> eq2. reflexivity.]" as we have 
     done several times above. But we can achieve the
     same effect in a single step by using the 
     [apply] tactic instead: *)
  apply eq2.  Qed.

(** The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2. 
  apply eq2. apply eq1.  Qed.

(** You may find it instructive to experiment with this proof
    and see if there is a way to complete it using just [rewrite]
    instead of [apply]. *)

(** Typically, when we use [apply H], the statement [H] will
    begin with a [forall] binding some _universal variables_.  When
    Coq matches the current goal against the conclusion of [H], it
    will try to find appropriate values for these variables.  For
    example, when we do [apply eq2] in the following proof, the
    universal variable [q] in [eq2] gets instantiated with [n] and [r]
    gets instantiated with [m]. *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** Exercise: 2 stars, optional (silly_ex) *)
(** Complete the following proof without using [simpl]. *)

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros eq1.
  intros eq2.
  apply eq1.
  apply eq2.
  Qed.
(** [] *)

(** To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal _exactly_ -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  (* Here we cannot use [apply] directly *)
Admitted.

(** In this case we can use the [symmetry] tactic, which switches the
    left and right sides of an equality in the goal. *)

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Actually, this [simpl] is unnecessary, since 
            [apply] will do a [simpl] step first. *)  
  apply H.  Qed.         

(** **** Exercise: 3 stars (apply_exercise1) *)
(** Hint: you can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [SearchAbout] is
    your friend. *)
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l'.
  intros H.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
  Qed.
(** [] *)

(** **** Exercise: 1 star, optional (apply_rewrite) *)
(** Briefly explain the difference between the tactics [apply] and
    [rewrite].  Are there situations where both can usefully be
    applied?
*)
(** **** Answer: 
    1) [apply] is [rewrite] with [reflexivity]. But rewrite can use [->] or [<-] to
       decide the direction which [apply] need [symmetry] to help deal with.
    2) [apply] can be used in context that contains a assumption while [rewrite] can
       be used in same place without the assumption limitation.
    3) Yes, when only one [rewrite] cannot finish proof, it can be wrote as
       [rewrite -> H1] [rewrite -> H2] then [apply -> H3].
*)
(** [] *)

(* ###################################################### *)
(** * Inversion *)

(** Recall the definition of natural numbers:
     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.
    It is clear from this definition that every number has one of two
    forms: either it is the constructor [O] or it is built by applying
    the constructor [S] to another number.  But there is more here than
    meets the eye: implicit in the definition (and in our informal
    understanding of how datatype declarations work in other
    programming languages) are two other facts:

    - The constructor [S] is _injective_.  That is, the only way we can
      have [S n = S m] is if [n = m].

    - The constructors [O] and [S] are _disjoint_.  That is, [O] is not
      equal to [S n] for any [n]. *)

(** Similar principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal.  For lists, the [cons] constructor is
    injective and [nil] is different from every non-empty list.  For
    booleans, [true] and [false] are unequal.  (Since neither [true]
    nor [false] take any arguments, their injectivity is not an issue.) *)

(** Coq provides a tactic called [inversion] that allows us to exploit
    these principles in proofs.
 
    The [inversion] tactic is used like this.  Suppose [H] is a
    hypothesis in the context (or a previously proven lemma) of the
    form
      c a1 a2 ... an = d b1 b2 ... bm
    for some constructors [c] and [d] and arguments [a1 ... an] and
    [b1 ... bm].  Then [inversion H] instructs Coq to "invert" this
    equality to extract the information it contains about these terms:

    - If [c] and [d] are the same constructor, then we know, by the
      injectivity of this constructor, that [a1 = b1], [a2 = b2],
      etc.; [inversion H] adds these facts to the context, and tries
      to use them to rewrite the goal.

    - If [c] and [d] are different constructors, then the hypothesis
      [H] is contradictory.  That is, a false assumption has crept
      into the context, and this means that any goal whatsoever is
      provable!  In this case, [inversion H] marks the current goal as
      completed and pops it off the goal stack. *)

(** The [inversion] tactic is probably easier to understand by
    seeing it in action than from general descriptions like the above.
    Below you will find example theorems that demonstrate the use of
    [inversion] and exercises to test your understanding. *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.  Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n m.
  intros eq. inversion eq. reflexivity.  Qed.

(** As a convenience, the [inversion] tactic can also
    destruct equalities between complex values, binding
    multiple variables as it goes. *)

Theorem silly5 : forall (n m o : nat),
     [n,m] = [o,o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

(** **** Exercise: 1 star (sillyex1) *) 
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros X x y z l j.
  intros eq1.
  intros eq2.
  inversion eq1.
  inversion eq2.
  rewrite -> H0.
  reflexivity. Qed.
(** [] *)

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra.  Qed.

(** **** Exercise: 1 star (sillyex2) *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros X x y z l j.
  intros eq1.
  intros eq2.
  inversion eq1.
  Qed.
(** [] *)

(** While the injectivity of constructors allows us to reason
    [forall (n m : nat), S n = S m -> n = m], the reverse direction of
    the implication, provable by standard equational reasoning, is a
    useful fact to record for cases we will see several times. *)

Lemma eq_remove_S : forall n m,
  n = m -> S n = S m.
Proof. intros n m eq. rewrite -> eq. reflexivity. Qed.

(** Here's another illustration of [inversion].  This is a slightly
    roundabout way of stating a fact that we have already proved
    above.  The extra equalities force us to do a little more
    equational reasoning and exercise some of the tactics we've seen
    recently. *)

Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l. induction l as [| v' l'].
  Case "l = []". intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'". intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply eq_remove_S. apply IHl'. inversion eq. reflexivity. Qed.

(** **** Exercise: 2 stars, optional (practice) *)
(** A couple more nontrivial but not-too-complicated proofs to work
    together in class, or for you to work as exercises.  They may
    involve applying lemmas from earlier lectures or homeworks. *)
 

Theorem beq_nat_0_l : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  destruct n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    intros H.
    inversion H.
  Qed.
    
Theorem beq_nat_0_r : forall n,
  true = beq_nat n 0 -> 0 = n.
Proof.
  destruct n as [|n'].
  Case "n = 0".
    reflexivity.
  Case "n = S n'".
    intros H.
    inversion H.
  Qed.
(** [] *)


(* ###################################################### *)
(** * Using Tactics on Hypotheses *)

(** By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic [simpl in H] performs simplification in
    the hypothesis named [H] in the context. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b. 
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** Similarly, the tactic [apply L in H] matches some
    conditional statement [L] (of the form [L1 -> L2], say) against a
    hypothesis [H] in the context.  However, unlike ordinary
    [apply] (which rewrites a goal matching [L2] into a subgoal [L1]),
    [apply L in H] matches [H] against [L1] and, if successful,
    replaces it with [L2].
 
    In other words, [apply L in H] gives us a form of "forward
    reasoning" -- from [L1 -> L2] and a hypothesis matching [L1], it
    gives us a hypothesis matching [L2].  By contrast, [apply L] is
    "backward reasoning" -- it says that if we know [L1->L2] and we
    are trying to prove [L2], it suffices to prove [L1].  

    Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning. *)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5  ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H. 
  apply H.  Qed.

(** Forward reasoning starts from what is _given_ (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the _goal_, and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.
    If you've seen informal proofs before (for example, in a math or
    computer science class), they probably used forward reasoning.  In
    general, Coq tends to favor backward reasoning, but in some
    situations the forward style can be easier to use or to think
    about.  *)

(** **** Exercise: 3 stars (plus_n_n_injective) *)
(** Practice using "in" variants in this exercise. *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n.
  induction n as [| n'].
  Case "n = 0".
    simpl.
    destruct m as [|m'].
    SCase "m = 0".
      reflexivity.
    SCase "m = S m'".
      intros H.
      inversion H.
  Case "n = S n'".
    destruct m as [|m'].
    SCase "m = 0".
      intros H.
      inversion H.
    SCase "m = S m'".
      simpl.
      intros H.
      inversion H.
      rewrite <- plus_n_Sm in H1.
      rewrite <- plus_n_Sm in H1.
      inversion H1.
      apply IHn' in H2.
      rewrite -> H2.
      reflexivity. Qed.
    (* Hint: use the plus_n_Sm lemma *)
(** [] *)

(* ###################################################### *)
(** * Varying the Induction Hypothesis *)

(** In the previous chapter, we noticed the importance of
    controlling the exact form of the induction hypothesis when
    carrying out inductive proofs in Coq.  In particular, we need to
    be careful about which of the assumptions we move (using [intros])
    from the goal to the context before invoking the [induction]
    tactic.  In this short chapter, we consider this point in a little
    more depth and introduce one new tactic, called [generalize
    dependent], that is sometimes useful in helping massage the
    induction hypothesis into the required form.

    First, let's review the basic issue.  Suppose we want to show that
    the [double] function is injective -- i.e., that it always maps
    different arguments to different results.  The way we _start_ this
    proof is a little bit delicate: if we begin it with
      intros n. induction n.
]] 
    all is well.  But if we begin it with
      intros n m. induction n.
    we get stuck in the middle of the inductive case... *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  Case "n = O". simpl. intros eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq. 
  Case "n = S n'". intros eq. destruct m as [| m'].
    SCase "m = O". inversion eq.
    SCase "m = S m'". 
      assert (n' = m') as H.
      SSCase "Proof of assertion". 
      (* Here we are stuck.  We need the assertion in order to
         rewrite the final goal (subgoal 2 at this point) to an
         identity.  But the induction hypothesis, [IHn'], does
         not give us [n' = m'] -- there is an extra [S] in the
         way -- so the assertion is not provable. *)
      Admitted.

(** What went wrong? *)

(** The problem is that, at the point we invoke the induction
    hypothesis, we have already introduced [m] into the context -- 
    intuitively, we have told Coq, "Let's consider some particular
    [n] and [m]..." and we now have to prove that, if [double n =
    double m] for _this particular_ [n] and [m], then [n = m].

    The next tactic, [induction n] says to Coq: We are going to show
    the goal by induction on [n].  That is, we are going to prove that
    the proposition

      - [P n]  =  "if [double n = double m], then [n = m]"

    holds for all [n] by showing

      - [P O]              

         (i.e., "if [double O = double m] then [O = m]")

      - [P n -> P (S n)]  

        (i.e., "if [double n = double m] then [n = m]" implies "if
        [double (S n) = double m] then [S n = m]").

    If we look closely at the second statement, it is saying something
    rather strange: it says that, for a _particular_ [m], if we know

      - "if [double n = double m] then [n = m]"

    then we can prove

       - "if [double (S n) = double m] then [S n = m]".

    To see why this is strange, let's think of a particular [m] --
    say, [5].  The statement is then saying that, if we know

      - [Q] = "if [double n = 10] then [n = 5]"

    then we can prove

      - [R] = "if [double (S n) = 10] then [S n = 5]".

    But knowing [Q] doesn't give us any help with proving [R]!  (If we
    tried to prove [R] from [Q], we would say something like "Suppose
    [double (S n) = 10]..." but then we'd be stuck: knowing that
    [double (S n)] is [10] tells us nothing about whether [double n]
    is [10], so [Q] is useless at this point.) *)

(** To summarize: Trying to carry out this proof by induction on [n]
    when [m] is already in the context doesn't work because we are
    trying to prove a relation involving _every_ [n] but just a
    _single_ [m]. *)

(** The good proof of [double_injective] leaves [m] in the goal
    statement at the point where the [induction] tactic is invoked on
    [n]: *)

Theorem double_injective' : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq. 
  Case "n = S n'". 
    (* Notice that both the goal and the induction
       hypothesis have changed: the goal asks us to prove
       something more general (i.e., to prove the
       statement for _every_ [m]), but the IH is
       correspondingly more flexible, allowing us to
       choose any [m] we like when we apply the IH.  *)
    intros m eq.
    (* Now we choose a particular [m] and introduce the
       assumption that [double n = double m].  Since we
       are doing a case analysis on [n], we need a case
       analysis on [m] to keep the two "in sync." *)
    destruct m as [| m'].
    SCase "m = O". 
      (* The 0 case is trivial *)
      inversion eq.  
    SCase "m = S m'". 
      (* At this point, since we are in the second
         branch of the [destruct m], the [m'] mentioned
         in the context at this point is actually the
         predecessor of the one we started out talking
         about.  Since we are also in the [S] branch of
         the induction, this is perfect: if we
         instantiate the generic [m] in the IH with the
         [m'] that we are talking about right now (this
         instantiation is performed automatically by
         [apply]), then [IHn'] gives us exactly what we
         need to finish the proof. *)
      assert (n' = m') as H.
      SSCase "Proof of assertion". apply IHn'.
        inversion eq. reflexivity.
      rewrite -> H. reflexivity.  Qed.

(** What this teaches us is that we need to be careful about using
    induction to try to prove something too specific: If we're proving
    a property of [n] and [m] by induction on [n], we may need to
    leave [m] generic. *)

(** **** Exercise: 2 stars (beq_nat_eq) *)
Theorem beq_nat_eq : forall n m,
  true = beq_nat n m -> n = m.
Proof.
  induction n as [|n'].
  Case "n = 0".
    intros m H.
    destruct m as [|m'].
    SCase "m = 0".
      reflexivity.
    SCase "m = S m'".
      inversion H.
  Case "n = S n'".
    intros m H.
    destruct m as [|m'].
    SCase "m = 0".
      inversion H.
    SCase "m = S m'".
      inversion H.
      apply (IHn' m') in H1.
      rewrite -> H1.
      reflexivity. 
Qed.
(** [] *)

(** **** Exercise: 2 stars, advanced (beq_nat_eq_informal) *)
(** Give a careful informal proof of [beq_nat_eq], being as explicit
    as possible about quantifiers. *)
(** **** Answer
    for any [n] and [m] in [nat], 
    if [true = beq_nat n m] then our goal is to prove that [n = m].
    We are going to show the goal by [induction] on [n].
    That is assume : 
      - [P n']  =  "for particular [n = n'] and any [m] in [nat],
                   if [true = beq_nat n' m], then [n' = m]".
    
    holds for all [n] by showing
      - [P O]  =  "for particular [n = 0] and any [m : nat],
                   if [true = beq_nat 0 m], then [0 = m]".
        
        We are going to show the subgoal by [destruct] on [m].
        That is : 
        - for particular [n = 0] and [m = 0], 
          if [true = beq_nat 0 0], then [0 = 0].
          That could be proved by definition.
      
        - for particular [n = 0] and [m = m'],
          if [true = beq_nat 0 (S m')], then [0 = (S m')].
          that the hypothesis [true = beq_nat 0 (S m')] is contradictory
          because different constructors for [0] and [S m'] in definition of [beq_nat].
          So the subgoal is provable.

      - [P n' -> P (S n')] that is :
        [P n'] = "for particular [n = n'] and any [m] in [nat], 
                if [true = beq_nat n' m], then [n' = m]".
        can imply
        [P (S n')] = "for particular [n'] and any [m] in [nat], 
                    if [true = beq_nat (S n') m], then [(S n') = m]".
        
        We are going to show the subgoal by [destruct] on [m].
        That is : 
        - for particular [n = n'] and [m = 0], 
          if [true = beq_nat (S n') 0], then [(S n') = 0].
          that the hypothesis [true = beq_nat (S n') 0] is contradictory
          because different constructors for [S n'] and [0] in definition of [beq_nat].
          So the subgoal is provable.
        
        - for particular [n = n'] and [m = m'], 
          if [true = beq_nat (S n') (S m')], then [(S n') = (S m')].
          By [inversion] on [true = beq_nat (S n') (S m')] 
          according the definition of [beq_nat].
          we can get a further hypothesis that 
          [H] = "for particular [n = n'] and [m = m'] [true = beq_nat n' m']".
          Apply the hypothesis [P n'] in [H] and instantiate 
          the generic [m] in the [P n] with the particular [m'] in [H].
          We can get a slightly changed conclusion of 
          [P n] = "for particular [n = n'] and [m = m'], [n' = m']".
          [rewrite] conclusion of [P n] in our sub goal, we get new sub goal
          that [(S m') = (S m')] which can be proved by the definition of [S _].
      [Qed] that proof is done.
**)
(** [] *)


(** The strategy of doing fewer [intros] before an [induction] doesn't
    always work directly; sometimes a little _rearrangement_ of
    quantified variables is needed.  Suppose, for example, that we
    wanted to prove [double_injective] by induction on [m] instead of
    [n]. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  Case "m = O". simpl. intros eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq. 
  Case "m = S m'". intros eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'". 
      assert (n' = m') as H.
      SSCase "Proof of assertion". 
        (* Stuck again here, just like before. *)
Admitted.

(** The problem is that, to do induction on [m], we must first
    introduce [n].  (If we simply say [induction m] without
    introducing anything first, Coq will automatically introduce
    [n] for us!)   *)

(** What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that [m] is quantified before [n].  This
    will work, but it's not nice: We don't want to have to mangle the
    statements of lemmas to fit the needs of a particular strategy for
    proving them -- we want to state them in the most clear and
    natural way. *)

(**  What we can do instead is to first introduce all the
    quantified variables and then _re-generalize_ one or more of
    them, taking them out of the context and putting them back at
    the beginning of the goal.  The [generalize dependent] tactic
    does this. *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. 
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  induction m as [| m'].
  Case "m = O". simpl. intros n eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'". 
      assert (n' = m') as H.
      SSCase "Proof of assertion". 
        apply IHm'. inversion eq. reflexivity.
      rewrite -> H. reflexivity.  Qed.

(** Let's look at an informal proof of this theorem.  Note that
    the proposition we prove by induction leaves [n] quantified,
    corresponding to the use of generalize dependent in our formal
    proof.

_Theorem_: For any nats [n] and [m], if [double n = double m], then
  [n = m].

_Proof_: Let [m] be a [nat]. We prove by induction on [m] that, for
  any [n], if [double n = double m] then [n = m].

  - First, suppose [m = 0], and suppose [n] is a number such
    that [double n = double m].  We must show that [n = 0].

    Since [m = 0], by the definition of [double] we have [double n =
    0].  There are two cases to consider for [n].  If [n = 0] we are
    done, since this is what we wanted to show.  Otherwise, if [n = S
    n'] for some [n'], we derive a contradiction: by the definition of
    [double] we would have [n = S (S (double n'))], but this
    contradicts the assumption that [double n = 0].

  - Otherwise, suppose [m = S m'] and that [n] is again a number such
    that [double n = double m].  We must show that [n = S m'], with
    the induction hypothesis that for every number [s], if [double s =
    double m'] then [s = m'].
 
    By the fact that [m = S m'] and the definition of [double], we
    have [double n = S (S (double m'))].  There are two cases to
    consider for [n].

    If [n = 0], then by definition [double n = 0], a contradiction.
    Thus, we may assume that [n = S n'] for some [n'], and again by
    the definition of [double] we have [S (S (double n')) = S (S
    (double m'))], which implies by inversion that [double n' = double
    m'].

    Instantiating the induction hypothesis with [n'] thus allows us to
    conclude that [n' = m'], and it follows immediately that [S n' = S
    m'].  Since [S n' = n] and [S m' = m], this is just what we wanted
    to show. [] *)

(** **** Exercise: 3 stars (gen_dep_practice) *)

(** Prove this by induction on [l]. *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index (S n) l = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [|x l'].
  Case "l = []".
    reflexivity.
  Case "l = x::l'".
    destruct n as [|n'].
    SCase "n = 0".
      intros H.
      inversion H.
    SCase "n = S n'".
      intros H.
      inversion H.
      rewrite -> H1.
      simpl.
      apply (IHl' n' H1).
Qed. 
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (index_after_last_informal) *)
(** **** Answer : 
    Write an informal proof corresponding to your Coq proof
    of [index_after_last]:
 
     _Theorem_: For all sets [X], lists [l : list X], and numbers
      [n], if [length l = n] then [index (S n) l = None].
 
     _Proof_: Let [l] be a [list X]. We prove by induction on [l] that, for
     any [n], if [length l = n] then [index (S n) l = None].

     - First, suppose [l = []], we must show that [index (S n) [] = None]
       which we can get from the definition of index.

     - Otherwise, suppose [l = x::l'], with the induction hypothesis that
       [IHl'] = "For all sets [X], particular lists [l = l'], and for all numbers [n], 
                if [length l' = n] then [index (S n) l' = None]".
       we must prove our goal that 
       [G] = "For all sets [X], particular lists [l = l'], and for all numbers [n],
             if [length x::l' = n] then [index (S n) (x::l') = None]".
       
       We are going to show the subgoal by [destruct] on [n].
       That is : 
        - for particular [l = l'] and [n = 0], 
          if [length x::l' = 0] then [index (S 0) (x::l') = None].
          that the hypothesis [length x::l' = 0] is contradictory 
          by the definition of [beq_nat]. So the subgoal is provable.
        
        - for particular [l = n'] and [n = n'], 
          if [length x::l' = S n'] then [index (S (S n')) (x::l') = None].
          [introduce] the hypothesis [length x::l' = S n'] we can get 
          [length l' = n'] by the definition of [length].
          we can [simpl] the [index (S (S n')) (x::l') = None] to [index (S n') l' = None]
          by the definition of [index].
          [apply] the induction hypothesis [IHl'] 
          and instantiate the generic [n] in the [IHl'] with the particular [n'] in context.
          we can get the subgoal to [length l' = n'] which we just proved 
          in the introduced hypothesis.
    [Qed] that proof is done.
**)

(** **** Exercise: 3 stars, optional (gen_dep_practice_more) *)
(** Prove this by induction on [l]. *)   
Theorem length_snoc''' : forall (n : nat) (X : Type) 
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros n X v l.
  generalize dependent n.
  induction l as [|x l'].
  Case "l = []".
    simpl.
    intros n H.
    rewrite -> H.
    reflexivity.
  Case "l = x::l'".
    destruct n as [|n'].
    SCase "n = 0".
      intros H.
      inversion H.
    SCase "n = S n'".
      intros H.
      inversion H.
      rewrite -> H1.
      simpl.
      apply IHl' in H1.
      rewrite -> H1.
      reflexivity.
Qed.
    
(** [] *)

(** **** Exercise: 3 stars, optional (app_length_cons) *)
(** Prove this by induction on [l1], without using [app_length]. *)

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) 
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  induction l1 as [|x1 l1'].
  Case "l1 = []".
    intros l2 x n.
    simpl.
    intros H.
    apply H.
  Case "l1 = x1::l1'".
    destruct n as [|n'].
    SCase "n = 0".
      simpl.
      intros H.
      inversion H.
    SCase "n = S n'".
      simpl.
      intros H.
      inversion H.
      rewrite -> H1.
      assert (A : S (length (l1' ++ l2)) = n').
      SSCase "proof of assert".
        apply (IHl1' l2 x n' H1).
      rewrite -> A.
      reflexivity.
Qed.

(** **** Exercise: 4 stars, optional (app_length_twice) *)
(** Prove this by induction on [l], without using app_length. *)
Theorem app_insert : forall (X:Type) (l1 l2 : list X) (x : X) (n : nat),
	S (length (l1 ++ l2)) = n ->
		length (l1 ++ (x :: l2)) = n.
Proof.
  intros X l1 l2 x n.
  generalize dependent n.
  generalize dependent l2.
  induction l1 as [|x1 l1'].
  Case "l1 = []".
    simpl.
    intros l2 n H.
    apply H.
  Case "l1 = x1::l1'".
    simpl.
    destruct n as [|n'].
    SCase "n = 0".
      intros H.
      inversion H.
    SCase "n = S n'".
      intro H.
      inversion H.
      apply IHl1' in H1.
      rewrite -> H1.
      rewrite -> H.
      reflexivity.
Qed.

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n l.
  generalize dependent n.
  induction l as [|x l'].
  Case "l = []".
    simpl.
    intros n H.
    rewrite <- H.
    reflexivity.
  Case "l = x::l'".
    simpl.
    destruct n as [|n'].
    SCase "n = 0".
      intros H.
      inversion H.
    SCase "n = S n'".
      intros H.
      inversion H.
      rewrite -> H.
      apply IHl' in H1.
      rewrite -> (app_insert X l' l' x (S (n' + n'))).
      rewrite -> plus_n_Sm.
      reflexivity.
      rewrite -> H1.
      reflexivity.
Qed.
(** [] *)

(* ###################################################### *)
(** * Using [destruct] on Compound Expressions *)

(** We have seen many examples where the [destruct] tactic is
    used to perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun. 
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity.  Qed.

(** After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (beq_nat n 3) then ... else ...].  Well,
    either [n] is equal to [3] or it isn't, so we use [destruct
    (beq_nat n 3)] to let us reason about the two cases. *)

(** **** Exercise: 1 star (override_shadow) *)
Theorem override_shadow : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override.
  destruct (beq_nat k1 k2).
  Case "beq_nat k1 k2 = true".
    reflexivity.
  Case "beq_nat k1 k2 = false".
    reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (combine_split) *)
(** Remove the comment brackets (needed because [split] was defined in 
    a previous exercise) and complete the proof. *)

Print split.
Lemma split_ref : forall X Y (l : list (X * Y)),
  split l = (fst (split l), snd (split l)).
Proof.
  intros X Y l.
  induction l as [|(x,y) l'].
  Case "l = []".
    reflexivity.
  Case "l = (x,y)::l'".
    reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y.
  intros l.
  induction l as [|(x,y) l'].
  Case "l = []".
    intros l1 l2 H.
    inversion H.
    reflexivity.
  Case "l = (x,y)::l'".
    destruct l1 as [|x1 l1'].
    SCase "l1 = []".
      intros l2 H.
      inversion H.
    SCase "l1 = x1::l1'".
      destruct l2 as [|x2 l2'].
      SSCase "l2 = []".
        intros H.
        inversion H.
      SSCase "l2 = x2::l2'".
        intros H.
        inversion H.
        simpl.
        rewrite -> H2.
        rewrite -> H4.
        rewrite -> (IHl' l1' l2').
        reflexivity.
        rewrite <- H2.
        rewrite <- H4.
        apply split_ref.
Qed.

(** **** Exercise: 3 stars, advanced (split_combine) *)
(** We have just proven that for all lists of pairs, [combine] is the
    inverse of [split].  How would you formalize the statement that
    [split] is the inverse of [combine]?
 
    State this as a theorem in Coq, and prove it. (Be sure to leave
    your induction hypothesis general by not doing [intros] on more
    things than necessary.  Hint: what property do you need of [l1]
    and [l2] for [split] [combine l1 l2 = (l1,l2)] to be true?) *)

Lemma length_0_nil : forall (X : Type) (l : list X),
  length l = 0 -> l = [].
Proof.
  intros X l.
  induction l.
  reflexivity.
  simpl.
  intros H.
  inversion H.
Qed.
  
Theorem split_combine : forall (X Y : Type) (l1 : list X) (l2 : list Y) (l : list (X * Y)),
    length l1 = length l2 -> combine l1 l2 = l -> 
    split l = (l1, l2).
Proof.
  intros X Y l1.
  induction l1 as [|x1 l1'].
  Case "l1 = []".
    intros l2 l eq H.
    inversion eq.
    symmetry in H1.
    apply (length_0_nil Y l2) in H1.
    rewrite -> H1 in H.
    simpl in H.
    rewrite -> H1.
    rewrite <- H.
    reflexivity.
  Case "l1 = x1::l1'".
    destruct l2 as [|y2 l2'].
    SCase "l2 = []".
      intros l eq H.
      inversion eq.
    SCase "l2 = y2::l2'".
      destruct l as [|(x,y) l'].
        SSCase "l = []".
          intros eq H.
          inversion H.
        SSCase "l = (x,y)::l'".
          intros eq H.
          inversion eq.
          simpl in H.
          inversion H.
          rewrite -> H4.
          simpl.
          rewrite -> (IHl1' l2' l').
          reflexivity.
          apply H1.
          apply H4.
Qed.

(* ###################################################### *)
(** * The [remember] Tactic *)

(** We have seen how the [destruct] tactic can be used to
    perform case analysis of the results of arbitrary computations.
    If [e] is an expression whose type is some inductively defined
    type [T], then, for each constructor [c] of [T], [destruct e]
    generates a subgoal in which all occurrences of [e] (in the goal
    and in the context) are replaced by [c].

    Sometimes, however, this substitution process loses information
    that we need in order to complete the proof.  For example, suppose
    we define a function [sillyfun1] like this: *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(** And suppose that we want to convince Coq of the rather
    obvious observation that [sillyfun1 n] yields [true] only when [n]
    is odd.  By analogy with the proofs we did with [sillyfun] above,
    it is natural to start the proof like this: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Admitted.

(** We get stuck at this point because the context does not
    contain enough information to prove the goal!  The problem is that
    the substitution peformed by [destruct] is too brutal -- it threw
    away every occurrence of [beq_nat n 3], but we need to keep at
    least one of these because we need to be able to reason that
    since, in this branch of the case analysis, [beq_nat n 3 = true],
    it must be that [n = 3], from which it follows that [n] is odd.

    What we would really like is not to use [destruct] directly on
    [beq_nat n 3] and substitute away all occurrences of this
    expression, but rather to use [destruct] on something else that is
    _equal_ to [beq_nat n 3].  For example, if we had a variable that
    we knew was equal to [beq_nat n 3], we could [destruct] this
    variable instead.

    The [remember] tactic allows us to introduce such a variable. *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  remember (beq_nat n 3) as e3.
  (* At this point, the context has been enriched with a new
     variable [e3] and an assumption that [e3 = beq_nat n 3].
     Now if we do [destruct e3]... *)
  destruct e3.
  (* ... the variable [e3] gets substituted away (it
    disappears completely) and we are left with the same
     state as at the point where we got stuck above, except
     that the context still contains the extra equality
     assumption -- now with [true] substituted for [e3] --
     which is exactly what we need to make progress. *)
    Case "e3 = true". apply beq_nat_eq in Heqe3.
      rewrite -> Heqe3. reflexivity.
    Case "e3 = false".
     (* When we come to the second equality test in the
       body of the function we are reasoning about, we can
        use [remember] again in the same way, allowing us
        to finish the proof. *)
      remember (beq_nat n 5) as e5. destruct e5.
        SCase "e5 = true".
          apply beq_nat_eq in Heqe5.
          rewrite -> Heqe5. reflexivity.
        SCase "e5 = false". inversion eq.  Qed.

(** **** Exercise: 2 stars *)
Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  Case "b = true".
    remember (f true) as ft.
    destruct ft.
    SCase "f true = true".
      symmetry in Heqft.
      rewrite -> Heqft.
      apply Heqft.
    SCase "f true = false".
      remember (f false) as ff.
      destruct ff.
      SSCase "f false = true".
        symmetry in Heqft.
        apply Heqft.
      SSCase "f false = false".
        symmetry in Heqff.
        apply Heqff.
  Case "b = fasle".
    remember (f false) as ff.
    destruct ff.
    SCase "f false = true".
      remember (f true) as ft.
      destruct ft.
      SSCase "f true = true".
        symmetry in Heqft.
        apply Heqft.
      SSCase "f true = false".
        symmetry in Heqff.
        apply Heqff.
    SCase "f false = false".
      symmetry in Heqff.
      rewrite -> Heqff.
      apply Heqff.
Qed.
(** [] *)

(** **** Exercise: 2 stars (override_same) *)
Theorem override_same : forall {X:Type} x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f.
  intros eq.
  unfold override.
  remember (beq_nat k1 k2) as k1_eq_k2.
  destruct k1_eq_k2.
  Case "k1 = k2".
    apply beq_nat_eq in Heqk1_eq_k2.
    rewrite <- Heqk1_eq_k2.
    symmetry in eq.
    apply eq.
  Case "k1 != k2".
    reflexivity.
Qed.
(** [] *)

(* ###################################################### *)
(** * The [apply ... with ...] Tactic *)

(** The following silly example uses two rewrites in a row to
    get from [[a,b]] to [[e,f]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Since this is a common pattern, we might
    abstract it out as a lemma recording once and for all
    the fact that equality is transitive. *)

Theorem trans_eq : forall {X:Type} (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. 
  reflexivity.  Qed.

(** Now, we should be able to use [trans_eq] to
    prove the above example.  However, to do this we need
    a slight refinement of the [apply] tactic. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  (* If we simply tell Coq [apply trans_eq] at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate [X]
     with [[nat]], [n] with [[a,b]], and [o] with [[e,f]].
     However, the matching process doesn't determine an
     instantiation for [m]: we have to supply one explicitly
     by adding [with (m:=[c,d])] to the invocation of
     [apply]. *)
  apply trans_eq with (m:=[c,d]). apply eq1. apply eq2.   Qed.

(**  Actually, we usually don't have to include the name [m]
    in the [with] clause; Coq is often smart enough to
    figure out which instantiation we're giving. We could
    instead write: apply trans_eq with [c,d]. *)

(** **** Exercise: 3 stars (apply_with_exercise3) *)
Lemma beq_nat_swap : forall n m : nat,
  beq_nat n m = beq_nat m n.
Proof.
  induction n.
  Case "n = 0".
    destruct m.
    SCase "m = 0".
      reflexivity.
    SCase "m = S m".
      reflexivity.
  Case "n = S n".
    destruct m.
    SCase "m = 0".
      reflexivity.
    SCase "m = S m".
      simpl.
      apply IHn.
Qed.

Theorem override_permute : forall {X:Type} x1 x2 k1 k2 k3 (f : nat->X),
  false = beq_nat k2 k1 ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros X x1 x2 k1 k2 k3 f eq.
  remember (beq_nat k3 k1) as k3_eq_k1.
  destruct k3_eq_k1.
  Case "k3 = k1".
    apply beq_nat_eq in Heqk3_eq_k1.
    rewrite -> Heqk3_eq_k1.
    rewrite -> override_eq.
    unfold override.
    rewrite <- eq.
    rewrite <- beq_nat_refl.
    reflexivity.
  Case "k3 != k1".
    remember (beq_nat k3 k2) as k3_eq_k2.
    destruct k3_eq_k2.
    SCase "k3 = k2".
      apply beq_nat_eq in Heqk3_eq_k2.
      rewrite -> Heqk3_eq_k2.
      rewrite -> override_eq.
      unfold override.
      rewrite -> beq_nat_swap in eq.
      rewrite <- eq.
      rewrite <- beq_nat_refl.
      reflexivity.
    SCase "k3 != k2".
      unfold override.
      rewrite -> beq_nat_swap in Heqk3_eq_k1.
      rewrite <- Heqk3_eq_k1.
      rewrite -> beq_nat_swap in Heqk3_eq_k2.
      rewrite <- Heqk3_eq_k2.
      reflexivity.
Qed.
     
(** **** Exercise: 3 stars, optional (apply_with_exercise1) *)
Print trans_eq.
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o). 
Proof.
  intros n m o p H1 H2.
  apply trans_eq with m.
  apply H2.
  apply H1.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (apply_with_exercise2) *)
Print beq_nat_eq.
Theorem beq_nat_trans : forall n m p,
  true = beq_nat n m ->
  true = beq_nat m p ->
  true = beq_nat n p.
Proof.
  intros n m p H1 H2.
  apply beq_nat_eq in H1.
  apply beq_nat_eq in H2.
  assert (A : n = p).
    apply trans_eq with m.
    apply H1.
    apply H2.
  rewrite -> A.
  apply beq_nat_refl.
Qed.
(** [] *)

(* ################################################################## *)
(** * Review *)

(** We've now seen a bunch of Coq's fundamental tactics.  We'll
    introduce a few more as we go along through the coming lectures,
    and later in the course we'll introduce some more powerful
    _automation_ tactics that make Coq do more of the low-level work
    in many cases.  But basically we've got what we need to get work
    done.

    Here are the ones we've seen:

      - [intros]: 
        move hypotheses/variables from goal to context 

      - [reflexivity]:
        finish the proof (when the goal looks like [e = e])

      - [apply]:
        prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: 
        apply a hypothesis, lemma, or constructor to a hypothesis in
        the context (forward reasoning)

      - [apply... with...]:
        explicitly specify values for variables that cannot be
        determined by pattern matching

      - [simpl]:
        simplify computations in the goal 

      - [simpl in H]:
        ... or a hypothesis 

      - [rewrite]:
        use an equality hypothesis (or lemma) to rewrite the goal 

      - [rewrite ... in H]:
        ... or a hypothesis 

      - [symmetry]:
        changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]:
        changes a hypothesis of the form [t=u] into [u=t]

      - [unfold]:
        replace a defined constant by its right-hand side in the goal 

      - [unfold... in H]:
        ... or a hypothesis  

      - [destruct... as...]:
        case analysis on values of inductively defined types 

      - [induction... as...]:
        induction on values of inductively defined types 

      - [inversion]:
        reason by injectivity and distinctness of constructors

      - [remember (e) as x]:
        give a name ([x]) to an expression ([e]) so that we can
        destruct [x] without "losing" [e]

      - [assert (e) as H]:
        introduce a "local lemma" [e] and call it [H] 

      - [generalize dependent x]:
        move the variable [x] (and anything else that depends on it)
        from the context back to an explicit hypothesis in the goal
        formula 
*)

(* ###################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (beq_nat_sym) *)
Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  apply beq_nat_swap.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (beq_nat_sym_informal) *)
(** Give an informal proof of this lemma that corresponds to your
    formal proof above:

   Theorem: For any [nat]s [n] [m], [beq_nat n m = beq_nat m n].

   Proof:
   (* FILL IN HERE *)
[]
 *)

(** **** Exercise: 3 stars, advanced (filter_exercise) *)
(** This one is a bit challenging.  Pay attention to the form of your IH. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l.
  generalize dependent x.
  induction l as [|y l'].
  Case "l = []".
    intros x lf eq.
    inversion eq.
  Case "l = y::l'".
    intros x lf eq.
    remember (test y) as test_y.
    destruct test_y.
    SCase "test y = true".
      unfold filter in eq.
      rewrite <- Heqtest_y in eq.
      inversion eq.
      rewrite <- H0.
      symmetry in Heqtest_y.
      apply Heqtest_y.
    SCase "test y = false".
      unfold filter in eq.
      rewrite <- Heqtest_y in eq.
      apply IHl' in eq.
      apply eq.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (forall_exists_challenge) *)
(** **** Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:
      forallb oddb [1,3,5,7,9] = true

      forallb negb [false,false] = true
  
      forallb evenb [0,2,4,5] = false
  
      forallb (beq_nat 5) [] = true
    The second checks whether there exists an element in the list that
    satisfies a given predicate:
      existsb (beq_nat 5) [0,2,3,6] = false
 
      existsb (andb true) [true,true,false] = true
 
      existsb oddb [1,0,0,0,0,3] = true
 
      existsb evenb [] = false
    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].
 
    Prove that [existsb'] and [existsb] have the same behavior.
*)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X)  : bool :=
  match l with
    | nil => true
    | x::l' => if (test x) then (forallb test l')
                           else false
  end.

Example test_forallb1 : forallb oddb [1,3,5,7,9] = true.
reflexivity. Qed.
Example test_forallb2 : forallb negb [false,false] = true.
reflexivity. Qed.
Example test_forallb3 : forallb evenb [0,2,4,5] = false.
reflexivity. Qed.
Example test_forallb4 : forallb (beq_nat 5) [] = true.
reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | nil => false
    | x::l' => if (test x) then true
                           else existsb test l'
  end.

Example test_existsb1 : existsb (beq_nat 5) [0,2,3,6] = false.
reflexivity. Qed.
Example test_existsb2 : existsb (andb true) [true,true,false] = true.
reflexivity. Qed. 
Example test_existsb3 : existsb oddb [1,0,0,0,0,3] = true.
reflexivity. Qed. 
Example test_existsb4 : existsb evenb [] = false.
reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb ((fun (test : X -> bool) (x : X) => negb (test x)) test) l).

Example test_existsb'1 : existsb' (beq_nat 5) [0,2,3,6] = false.
reflexivity. Qed.
Example test_existsb'2 : existsb' (andb true) [true,true,false] = true.
reflexivity. Qed. 
Example test_existsb'3 : existsb' oddb [1,0,0,0,0,3] = true.
reflexivity. Qed. 
Example test_existsb'4 : existsb' evenb [] = false.
reflexivity. Qed.

Theorem existsb_eq : forall {X : Type} (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros X test l.
  induction l as [|x l'].
  Case "l = []".
    reflexivity.
  Case "l = x::l'".
    remember (test x) as test_x.
    destruct test_x.
    SCase "test x = true".
      simpl.
      rewrite <- Heqtest_x.
      unfold existsb'.
      simpl.
      rewrite <- Heqtest_x.
      reflexivity.
    SCase "test x = false".
      simpl.
      rewrite <- Heqtest_x.
      unfold existsb'.
      simpl.
      rewrite <- Heqtest_x.
      simpl.
      apply IHl'.
Qed.

(* $Date: 2013-02-06 13:21:22 -0500 (Wed, 06 Feb 2013) $ *)

(** **** KE DING 8318 *)

