(** **** KE DING 8318 *)

(** * Logic: Logic in Coq *)

Require Export MoreProp. 

(** Coq's built-in logic is very small: the only primitives are
    [Inductive] definitions, universal quantification ([forall]), and
    implication ([->]), while all the other familiar logical
    connectives -- conjunction, disjunction, negation, existential
    quantification, even equality -- can be encoded using just these.

    This chapter explains the encodings and shows how the tactics
    we've seen can be used to carry out standard forms of logical
    reasoning involving these connectives. *)

(* ########################################################### *)
(** * Conjunction *)

(** The logical conjunction of propositions [P] and [Q] can be
    represented using an [Inductive] definition with one
    constructor. *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

Definition conjunction (P Q : Prop) := and P Q.

Check conjunction.

Theorem alternate_conjunction : forall P Q : Prop,
  conjunction P Q -> and P Q.
Proof.
  intros P Q H.
  apply H.
Qed.

Theorem alternate_conjunction' : forall P Q : Prop,
  and P Q -> conjunction P Q.
Proof.
  intros P Q H.
  unfold conjunction.
  apply H.
Qed.

(** Note that, like the definition of [ev] in the previous
    chapter, this definition is parameterized; however, in this case,
    the parameters are themselves propositions, rather than numbers. *)

(** The intuition behind this definition is simple: to
    construct evidence for [and P Q], we must provide evidence
    for [P] and evidence for [Q].  More precisely:

    - [conj p q] can be taken as evidence for [and P Q] if [p]
      is evidence for [P] and [q] is evidence for [Q]; and

    - this is the _only_ way to give evidence for [and P Q] --
      that is, if someone gives us evidence for [and P Q], we
      know it must have the form [conj p q], where [p] is
      evidence for [P] and [q] is evidence for [Q]. 

   Since we'll be using conjunction a lot, let's introduce a more
   familiar-looking infix notation for it. *)

Notation "P /\ Q" := (and P Q) : type_scope.

(** (The [type_scope] annotation tells Coq that this notation
    will be appearing in propositions, not values.) *)

(** Consider the "type" of the constructor [conj]: *)

Check conj.
(* ===>  forall P Q : Prop, P -> Q -> P /\ Q *)

(** Notice that it takes 4 inputs -- namely the propositions [P]
    and [Q] and evidence for [P] and [Q] -- and returns as output the
    evidence of [P /\ Q]. *)

(** Besides the elegance of building everything up from a tiny
    foundation, what's nice about defining conjunction this way is
    that we can prove statements involving conjunction using the
    tactics that we already know.  For example, if the goal statement
    is a conjuction, we can prove it by applying the single
    constructor [conj], which (as can be seen from the type of [conj])
    solves the current goal and leaves the two parts of the
    conjunction as subgoals to be proved separately. *)

Theorem and_example : 
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
  (* Case "left". *) apply b_0.
  (* Case "right". *) apply b_3.  Qed.

(** Let's take a look at the proof object for the above theorem. *)

Print and_example. 
(* ===>  conj (beautiful 0) (beautiful 3) b_0 b_3
            : beautiful 0 /\ beautiful 3 *)

(** Note that the proof is of the form
    conj (beautiful 0) (beautiful 3) 
         (...pf of beautiful 3...) (...pf of beautiful 3...)
    as you'd expect, given the type of [conj]. *)

(** Just for convenience, we can use the tactic [split] as a shorthand for
    [apply conj]. *)

Theorem and_example' : 
  (ev 0) /\ (ev 4).
Proof.
  split.
    Case "left". apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0.  Qed.

(** Conversely, the [inversion] tactic can be used to take a
    conjunction hypothesis in the context, calculate what evidence
    must have been used to build it, and add variables representing
    this evidence to the proof context. *)

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  apply HP.  Qed.

(** **** Exercise: 1 star, optional (proj2) *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  intros.
  inversion H.
  apply H1.
Qed.
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HP HQ]. 
  split.  
    (* Case "left". *) apply HQ. 
    (* Case "right".*) apply HP.  Qed.
  
(** Once again, we have commented out the [Case] tactics to make the
    proof object for this theorem easy to understand.  Examining it
    shows that all that is really happening is taking apart a record
    containing evidence for [P] and [Q] and rebuilding it in the
    opposite order: *)

Print and_commut.
(* ===>
   and_commut = 
     fun (P Q : Prop) (H : P /\ Q) =>
     let H0 := match H with
               | conj HP HQ => conj Q P HQ HP
               end 
     in H0
     : forall P Q : Prop, P /\ Q -> Q /\ P *)

(** **** Exercise: 2 stars (and_assoc) *)
(** In the following proof, notice how the _nested pattern_ in the
    [inversion] breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP: P], [HQ : Q], and [HR : R].  Finish the proof from there: *)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
  split.
  apply HP.
  apply HQ.
  apply HR.
Qed.
(** [] *)

(** **** Exercise: 2 stars (even__ev) *)
(** Now we can prove the other direction of the equivalence of [even]
   and [ev], which we left hanging in chapter [Prop].  Notice that the
   left-hand conjunct here is the statement we are actually interested
   in; the right-hand conjunct is needed in order to make the
   induction hypothesis strong enough that we can carry out the
   reasoning in the inductive step.  (To see why this is needed, try
   proving the left conjunct by itself and observe where things get
   stuck.) *)

Print even.
Print ev.

Theorem even__ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  (* Hint: Use induction on [n]. *)
  intros.
  induction n as [| n'].
  Case "n = 0".
    split.
    SCase "left".
      intros.
      apply ev_0.
    SCase "right".
      intros.
      inversion H.
  Case "n = S n'".
    split.
    SCase "left".
      inversion IHn'.
      apply H0.
    SCase "right".
      intros.
      inversion H.
      apply ev_SS.
      inversion IHn'.
      apply H0.
      apply H1.
Qed.    
(** [] *)

(** **** Exercise: 2 stars, optional (conj_fact) *)
(** Construct a proof object demonstrating the following proposition. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (H1: P /\ Q) (H2 : Q /\ R) => 
  match H1 with
    | conj p q => match H2 with
                    | conj q r => conj P R p r
                  end
  end.
(** [] *)

(* ###################################################### *)
(** ** Iff *)

(** The handy "if and only if" connective is just the conjunction of
    two implications. *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.  
  intros P Q H. 
  inversion H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop, 
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. 
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.

(** **** Exercise: 1 star, optional (iff_properties) *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof.
  split.
  intros.
  apply H.
  intros.
  apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R HPQ HQR.
  split.
  intros.
  apply HQR.
  apply HPQ.
  apply H.
  intros.
  inversion HPQ.
  inversion HQR.
  apply H1.
  apply H3.
  apply H.
Qed.

(** Hint: If you have an iff hypothesis in the context, you can use
    [inversion] to break it into two separate implications.  (Think
    about why this works.) *)
(** [] *)

(** **** Exercise: 2 stars, advanced (beautiful_iff_gorgeous) *)

(** We have seen that the families of propositions [beautiful] and
    [gorgeous] actually characterize the same set of numbers.
    Prove that [beautiful n <-> gorgeous n] for all [n].  Just for
    fun, write your proof as an explicit proof object, rather than
    using tactics. (_Hint_: if you make use of previously defined
    theorems, you should only need a single line!) *)

Print beautiful.
Print gorgeous.
Definition beautiful_iff_gorgeous :
  forall n, beautiful n <-> gorgeous n :=
    fun n => conj (beautiful n -> gorgeous n) (gorgeous n -> beautiful n) 
                  (beautiful__gorgeous n) (gorgeous__beautiful n).
(** [] *)

(** Some of Coq's tactics treat [iff] statements specially, thus
    avoiding the need for some low-level manipulation when reasoning
    with them.  In particular, [rewrite] can be used with [iff]
    statements, not just equalities. *)

(* ############################################################ *)
(** * Disjunction *)

(** Disjunction ("logical or") can also be defined as an
    inductive proposition. *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

(** Consider the "type" of the constructor [or_introl]: *)

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

(** It takes 3 inputs, namely the propositions [P], [Q] and
    evidence of [P], and returns, as output, the evidence of [P \/ Q].
    Next, look at the type of [or_intror]: *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

(** It is like [or_introl] but it requires evidence of [Q]
    instead of evidence of [P]. *)

(** Intuitively, there are two ways of giving evidence for [P \/ Q]:

    - give evidence for [P] (and say that it is [P] you are giving
      evidence for -- this is the function of the [or_introl]
      constructor), or

    - give evidence for [Q], tagged with the [or_intror]
      constructor. *)

(** Since [P \/ Q] has two constructors, doing [inversion] on a
    hypothesis of type [P \/ Q] yields two subgoals. *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

(** From here on, we'll use the shorthand tactics [left] and [right]
    in place of [apply or_introl] and [apply or_intror]. *)

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ.  Qed.

(** **** Exercise: 2 stars, optional (or_commut'') *)
(** Try to write down an explicit proof object for [or_commut] (without
    using [Print] to peek at the ones we already defined!). *)

(* FILL IN HERE *)
(** [] *)

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof. 
  intros P Q R. intros H. inversion H as [HP | [HQ HR]]. 
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

(** **** Exercise: 2 stars (or_distributes_over_and_2) *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  inversion H as [[HPl |HQ] [HPr |HR]].
  Case "left /\ left".
    left.
    apply HPl.
  Case "left /\ right".
    left.
    apply HPl.
  Case "right /\ left".
    left.
    apply HPr.
  Case "right /\ right".
    right.
    split.
    apply HQ.
    apply HR.
Qed.
(** [] *)

(** **** Exercise: 1 star, optional (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
  apply or_distributes_over_and_1.
  apply or_distributes_over_and_2.
Qed.
(** [] *)

(* ################################################### *)
(** ** Relating [/\] and [\/] with [andb] and [orb] (advanced) *)

(** We've already seen several places where analogous structures
    can be found in Coq's computational ([Type]) and logical ([Prop])
    worlds.  Here is one more: the boolean operators [andb] and [orb]
    are clearly analogs of the logical connectives [/\] and [\/].
    This analogy can be made more precise by the following theorems,
    which show how to translate knowledge about [andb] and [orb]'s
    behaviors on certain inputs into propositional facts about those
    inputs. *)

Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

(** **** Exercise: 2 stars, optional (bool_prop) *)
SearchAbout andb.
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. 
  intros.
  destruct c.
  Case "c = true".
    rewrite -> andb_eq_rt with (a := b) in H.
    left.
    apply H.
  Case "c = false".
    right.
    reflexivity.
Qed.
  
SearchAbout orb.  
Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros.
  destruct c.
  Case "c = true".
    right.
    reflexivity.
  Case "c = false".
    rewrite -> orb_eq_rf with (a := b) in H.
    left.
    apply H.
Qed.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  intros.
  destruct c.
  Case "c = true".
    rewrite -> orb_eq_rt with (a := b) in H.
    inversion H.
  Case "c = false".
    rewrite -> orb_eq_rf with (a := b) in H.
    split.
    apply H.
    reflexivity.
Qed.
(** [] *)

(* ################################################### *)
(** * Falsehood *)

(** Logical falsehood can be represented in Coq as an inductively
    defined proposition with no constructors. *)

Inductive False : Prop := . 

(** Intuition: [False] is a proposition for which there is no way
    to give evidence. *)

(** Since [False] has no constructors, inverting an assumption
    of type [False] always yields zero subgoals, allowing us to
    immediately prove any goal. *)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof. 
  intros contra.
  inversion contra.  Qed. 

(** How does this work? The [inversion] tactic breaks [contra] into
    each of its possible cases, and yields a subgoal for each case.
    As [contra] is evidence for [False], it has _no_ possible cases,
    hence, there are no possible subgoals and the proof is done. *)

(** Conversely, the only way to prove [False] is if there is already
    something nonsensical or contradictory in the context: *)

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

(** Actually, since the proof of [False_implies_nonsense]
    doesn't actually have anything to do with the specific nonsensical
    thing being proved; it can easily be generalized to work for an
    arbitrary [P]: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from
    falsehood follows whatever you please."  This theorem is also
    known as the _principle of explosion_. *)

(* #################################################### *)
Print True.
(** ** Truth *)

(** Since we have defined falsehood in Coq, one might wonder whether
    it is possible to define truth in the same way.  We can. *)

(** **** Exercise: 2 stars, advanced (True) *)
(** Define [True] as another inductively defined proposition.  (The
    intution is that [True] should be a proposition for which it is
    trivial to give evidence.) *)

Inductive True : Prop :=  I : True.
(** [] *)

(** However, unlike [False], which we'll use extensively, [True] is
    just a theoretical curiosity: it is trivial (and therefore
    uninteresting) to prove as a goal, and it carries no useful
    information as a hypothesis. *)

(* #################################################### *)
(** * Negation *)

(** The logical complement of a proposition [P] is written [not
    P] or, for shorthand, [~P]: *)

Definition not (P:Prop) := P -> False.

(** The intuition is that, if [P] is not true, then anything at
    all (even [False]) follows from assuming [P]. *)

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

(** It takes a little practice to get used to working with
    negation in Coq.  Even though you can see perfectly well why
    something is true, it can be a little hard at first to get things
    into the right configuration so that Coq can see it!  Here are
    proofs of a few familiar facts about negation to get you warmed
    up. *)

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. 
  (* WORKED IN CLASS *)
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA. 
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, advanced (double_neg_inf) *)
(** **** Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
     By the definition of [~] we can get that [~ p = p -> False],
     so [~~p = ~(~ p) = ~(P - > False) = (P -> False) -> False].
     Now our goal is that [P] implies [(P -> False) -> False], for any prop [P].
     [Intros] the hypothesis [P -> False], then our goal is [False],
     and [Apply] hypothesis [P -> False] so our goal is [P].
     Just [apply] the initial hypothesis any prop [P].
     The proving is done.
**)

(** **** Exercise: 2 stars (contrapositive) *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.
  unfold not.
  intros Hq.
  intros Hp.
  apply Hq.
  apply H.
  apply Hp.
Qed.  
(** [] *)

(** **** Exercise: 1 star (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  unfold not.
  intros.
  inversion H.
  apply H1.
  apply H0.
Qed.
(** [] *)

(** **** Exercise: 1 star, advanced (informal_not_PNP) *)
(** **** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)].

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
     By the definition of [~] we can get that [~ p = p -> False],
     so [~(P /\ ~P) = (P /\ (P -> False)) -> False].
     Now our goal is that [(P /\ (P -> False))] implies [False], for any prop [P].
     [Intros] the hypothesis [(P /\ (P -> False))], then our goal is [False],
     By the definition of [/\] we can get two more hypothesis [P] and [P -> False].
     [apply] the hypothesis [P -> False] then our goal is [P].
     [apply] the other hypothesis [P] so that proving is done.
**)

Print ev.
Theorem five_not_even :  
  ~ ev 5.
Proof. 
  (* WORKED IN CLASS *)
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn]. 
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.  Qed.

(** **** Exercise: 1 star (ev_not_ev_S) *)
(** Theorem [five_not_even] confirms the unsurprising fact that five
    is not an even number.  Prove this more interesting fact: *)

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
  unfold not. intros n H. induction H as [|n']. (* not n! *)
  Case "n = 0".
    intros.
    inversion H.
  Case "n = S S n'".
    intros Hev.
    inversion Hev.
    apply IHev.
    apply H1.
Qed.    
(** [] *)

(** Note that some theorems that are true in classical logic are _not_
    provable in Coq's (constructive) logic.  E.g., let's look at how
    this proof gets stuck... *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H.
  (* But now what? There is no way to "invent" evidence for [~P] 
     from evidence for [P]. *) 
  Admitted.

(** **** Exercise: 5 stars, advanced, optional (classical_axioms) *)
(** For those who like a challenge, here is an exercise
    taken from the Coq'Art book (p. 123).  The following five
    statements are often considered as characterizations of
    classical logic (as opposed to constructive logic, which is
    what is "built in" to Coq).  We can't prove them in Coq, but
    we can consistently add any one of them as an unproven axiom
    if we wish to work in classical logic.  Prove that these five
    propositions are equivalent. *)

Definition peirce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
  ~~P -> P.
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
  ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
  (P->Q) -> (~P\/Q). 

Lemma classic__peirce : classic -> peirce.
Proof.
  intros.
  unfold peirce. 
  unfold classic. 
  intros P Q HPQP.
  (* P *)
  apply (H P).
  intros HP_F.
  apply HP_F.
  (* P *)
  apply HPQP.
  intros HP.
  (* Q *)
  apply (H Q).
  intros HQ_F.
  apply HP_F.
  apply HP.
Qed.

Lemma peirce__classic : peirce -> classic.
Proof.
  intros.
  unfold classic.
  unfold peirce in H.
  unfold not.
  intros P Hnn.
  apply H with (Q := False).
  intros HP.
  apply Hnn in HP.
  inversion HP.
Qed.

Theorem peirc_eq_classic : peirce <-> classic.
Proof.
  split.
  apply peirce__classic.
  apply classic__peirce.
Qed.

Lemma excluded_middle__peirce :  excluded_middle -> peirce.
Proof.
  unfold excluded_middle.
  unfold peirce.
  intros.
  destruct (H P).
  Case "P".
    apply H1.
  Case "~P".
    apply H0.
    intros.
    apply ex_falso_quodlibet.
    apply H1.
    apply H2.
Qed.  

Lemma peirce__excluded_middle : peirce -> excluded_middle.
Proof.
  unfold peirce.
  unfold excluded_middle.
  intros.
  right.
  apply H with (Q := ~P).
  intros.
  apply H0.
  unfold not in H0.
Admitted.
  
(** [] *)

(* ########################################################## *)
(** ** Inequality *)

(** Saying [x <> y] is just the same as saying [~(x = y)]. *)

Notation "x <> y" := (~ (x = y)) : type_scope.

(** Since inequality involves a negation, it again requires
    a little practice to be able to work with it fluently.  Here
    is one very useful trick.  If you are trying to prove a goal
    that is nonsensical (e.g., the goal state is [false = true]),
    apply the lemma [ex_falso_quodlibet] to change the goal to
    [False].  This makes it easier to use assumptions of the form
    [~P] that are available in the context -- in particular,
    assumptions of the form [x<>y]. *)

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.  
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.

(** **** Exercise: 2 stars (not_eq_beq_false) *)
Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof.
  intros n n'.
  unfold not.
  intros H.
  remember (beq_nat n n') as n__n'.
  destruct n__n'.
  Case "n = n'".
    apply (beq_nat_eq n n') in Heqn__n'.
    apply ex_falso_quodlibet.
    apply H.
    apply Heqn__n'.
  Case "n <> n'".
    reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (beq_false_not_eq) *)
Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  intros.
  unfold not.
  intros.
  rewrite -> H0 in H.
  rewrite <- beq_nat_refl in H.
  inversion H.
Qed.
  
(** [] *)

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

    For example, consider this existentially quantified proposition: *)

Check ex.
Definition some_nat_is_even : Prop := 
  ex nat ev.
Check some_nat_is_even.

(** To prove this proposition, we need to choose a particular number
    as witness -- say, 4 -- and give some evidence that that number is
    even. *)
Check ex_intro.
Definition snie : some_nat_is_even := 
  ex_intro nat ev 4 (ev_SS 2 (ev_SS 0 ev_0)).
Check snie.

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

(** We can use the usual set of tactics for
    manipulating existentials.  For example, to prove an
    existential, we can [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example : ex _ (fun n => n + (n * n) = 6).
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note, again, that we have to explicitly give the witness. *)

(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

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

(** **** Exercise: 1 star, optional (english_exists) *)
(** **** In English, what does the proposition 
      [ex nat (fun n => beautiful (S n))] mean?

    it means that there exists some [n : nat]s that make [S n] is a [beautiful] number.
**)

(** Complete the definition of the following proof object: *)

Print beautiful.
Check ex.
Check ex_intro.
Definition p : ex nat (fun n => beautiful (S n)) :=
  ex_intro nat (fun n => beautiful (S n)) 2 (b_3).
(** [] *)

(** **** Exercise: 1 star (dist_not_exists) *)
(** Prove that "[P] holds for all [x]" and "there is no [x] for
    which [P] does not hold" are equivalent assertions. *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  intros.
  unfold not.
  intros He.
  inversion He as [x Hx].
  apply Hx.
  apply H.
Qed.
(** [] *)

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
  intros Hem.
  intros.
  assert (P x \/ ~ P x).
  apply Hem.
  inversion H0.
  Case "left".
    apply H1.
  Case "right".
    apply ex_falso_quodlibet.
    apply H.
    unfold not in H1.
    exists x.
    apply H1.
Qed.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or) *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  Case "left -> right".
    intros.
    inversion H as [y Hor].
    inversion Hor as [Hl |Hr].
    SCase "left".
      left.
      exists y.
      apply Hl.
    SCase "right".
      right.
      exists y.
      apply Hr.
  Case "right -> left".
    intros.
    inversion H as [Hl |Hr].
    SCase "left".
      inversion Hl as [y Hp].
      exists y.
      left.
      apply Hp.
    SCase "right".
      inversion Hr as [y Hq].
      exists y.
      right.
      apply Hq.
Qed.
(** [] *)

(*Print dist_exists_or*)

(* ###################################################### *)
(** * Equality *)

(** Even Coq's equality relation is not built in.  It has (roughly)
    the following inductive definition. *)

(* (We enclose the definition in a module to avoid confusion with the
    standard library equality, which we have used extensively
    already.) *)

Module MyEquality.

Inductive eq (X:Type) : X -> X -> Prop :=
  refl_equal : forall x, eq X x x.

(** Standard infix notation: *)

Notation "x = y" := (eq _ x y) 
                    (at level 70, no associativity) 
                    : type_scope.

(** The definition of [=] is a bit subtle.  The way to think about it
    is that, given a set [X], it defines a _family_ of propositions
    "[x] is equal to [y]," indexed by pairs of values ([x] and [y])
    from [X].  There is just one way of constructing evidence for
    members of this family: applying the constructor [refl_equal] to a
    type [X] and a value [x : X] yields evidence that [x] is equal to
    [x]. *)

(** **** Exercise: 2 stars (leibniz_equality) *)
(** The inductive definitions of equality corresponds to _Leibniz equality_: 
   what we mean when we say "[x] and [y] are equal" is that every 
   property on [P] that is true of [x] is also true of [y].  *)

Lemma leibniz_equality : forall (X : Type) (x y: X), 
 x = y -> forall P : X -> Prop, P x -> P y.
Proof.
  intros X x y H P Hp.
  inversion H.
  rewrite <- H1.
  apply Hp.
Qed.
(** [] *)

(** We can use
    [refl_equal] to construct evidence that, for example, [2 = 2].
    Can we also use it to construct evidence that [1 + 1 = 2]?  Yes:
    indeed, it is the very same piece of evidence!  The reason is that
    Coq treats as "the same" any two terms that are _convertible_
    according to a simple set of computation rules.  These rules,
    which are similar to those used by [Eval simpl], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.
    
    In tactic-based proofs of equality, the conversion rules are
    normally hidden in uses of [simpl] (either explicit or implicit in
    other tactics such as [reflexivity]).  But you can see them
    directly at work in the following explicit proof objects: *)

Definition four : 2 + 2 = 1 + 3 :=  
  refl_equal nat 4. 

Definition singleton : forall (X:Set) (x:X), []++[x] = x::[]  :=
  fun (X:Set) (x:X) => refl_equal (list X) [x]. 

End MyEquality.


(* ####################################################### *)
(** ** Inversion, Again (Advanced) *)

(** We've seen [inversion] used with both equality hypotheses and
    hypotheses about inductively defined propositions.  Now that we've
    seen that these are actually the same thing, we're in a position
    to take a closer look at how [inversion] behaves...

    In general, the [inversion] tactic

    - takes a hypothesis [H] whose type [P] is inductively defined,
      and

    - for each constructor [C] in [P]'s definition,

      - generates a new subgoal in which we assume [H] was
        built with [C],

      - adds the arguments (premises) of [C] to the context of
        the subgoal as extra hypotheses,

      - matches the conclusion (result type) of [C] against the
        current goal and calculates a set of equalities that must
        hold in order for [C] to be applicable,
        
      - adds these equalities to the context (and, for convenience,
        rewrites them in the goal), and

      - if the equalities are not satisfiable (e.g., they involve
        things like [S n = O]), immediately solves the subgoal. *)

(** _Example_: If we invert a hypothesis built with [or], there are two
   constructors, so two subgoals get generated.  The
   conclusion (result type) of the constructor ([P \/ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.

   _Example_: If we invert a hypothesis built with [and], there is
   only one constructor, so only one subgoal gets generated.  Again,
   the conclusion (result type) of the constructor ([P /\ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.  The
   constructor does have two arguments, though, and these can be seen
   in the context in the subgoal.

   _Example_: If we invert a hypothesis built with [eq], there is
   again only one constructor, so only one subgoal gets generated.
   Now, though, the form of the [refl_equal] constructor does give us
   some extra information: it tells us that the two arguments to [eq]
   must be the same!  The [inversion] tactic adds this fact to the
   context.  *)


(** **** Exercise: 1 star, optional (dist_and_or_eq_implies_and) *)  
Lemma dist_and_or_eq_implies_and : forall P Q R,
P /\ (Q \/ R) /\ Q = R -> P/\Q.
Proof.
  intros.
  inversion H as [Hp [Hor Heq]].
  inversion Hor.
  Case "left".
    split.
    apply Hp.
    apply H0.
  Case "right".
    split.
    apply Hp.
    rewrite -> Heq.
    apply H0.
Qed.
(** [] *)

(* ########################################################### *)
(** * Quantification and Implication *)

(** In fact, the built-in logic is even smaller than it appears, since
    [->] and [forall] are actually the _same_ primitive!

    The [->] notation is actually just a shorthand for a degenerate
    use of [forall]. *)

(** For example, consider this proposition: *)

Definition funny_prop1 := 
  forall n, forall (E : beautiful n), beautiful (n+3).
Check funny_prop1.
(** A proof term inhabiting this proposition would be a function
    with two arguments: a number [n] and some evidence [E] that [n] is
    beautiful.  But the name [E] for this evidence is not used in the
    rest of the statement of [funny_prop1], so it's a bit silly to
    bother making up a name for it.  We could write it like this
    instead, using the dummy identifier [_] in place of a real
    name: *)

Definition funny_prop1' := 
  forall n, forall (_ : beautiful n), beautiful (n+3).

(** Or, equivalently, we can write it in more familiar notation: *)

Definition funny_prop1'' := 
  forall n, beautiful n -> beautiful (n+3). 

(** In general, "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)

(* ####################################################### *)
(** * Relations *)

(** A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeModule.  

(** We've seen an inductive definition of one fundamental relation:
    equality.  Another useful one is the "less than or equal to"
    relation on numbers: *)

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
    hypotheses in the context (e.g., to prove that [~(2 <= 1)].) *)

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
  ~ (2 <= 1).
Proof. 
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  |sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars (total_relation) *)
(** **** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop :=
  | tr : forall n m : nat, total_relation n m.

(** [] *)

(** **** Exercise: 2 stars (empty_relation) *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation : nat -> nat -> Prop :=.

(** [] *)

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

(** ****
      - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
  
    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

(** **** answer
    - [R 1 1 2] is provable.

    - No, the set will not change. since [c2] and [c3] already give [m] and [n]
      the property of exchengeable.

    - No, the set will not change. since [c5] is just a inverse constructed direction
      as [c3] and [c4].
**)
[]
*)

(** **** Exercise: 3 stars, optional (R_fact) *)  
(** **** State and prove an equivalent characterization of the relation
    [R].  That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)

Lemma R__refl : forall n : nat,
  R 0 n n.
Proof.
  intros.
  induction n.
  Case "n = 0".
    apply c1.
  SCase "n = S n".
    apply c3.
    apply IHn.
Qed.

Theorem R__plus : forall m n o : nat,
  R m n o <-> m + n = o.
Proof.
  intros.
  split.
  Case "left -> right".
    intros.
    induction H as [mc1 nc1 oc1 
                   |mc2 nc2 oc2
                   |mc3 nc3 oc3
                   |mc4 nc4 oc4
                   |mc5 nc5 oc5].
    SCase "c1".
      reflexivity.
    SCase "c2".
      simpl.
      rewrite -> IHR.
      reflexivity.
    SCase "c3".
      rewrite <- plus_n_Sm.
      rewrite -> IHR.
      reflexivity.
    SCase "c4".
      simpl in IHR.
      rewrite <- (plus_n_Sm mc4 nc4) in IHR.
      inversion IHR.
      reflexivity.
    SCase "c5".
      rewrite <- IHR.
      apply plus_comm.
  Case "right -> left".
    generalize dependent n.
    generalize dependent o.
    induction m.
    SCase "m = 0".
      simpl.
      intros.
      rewrite <- H.
      apply R__refl.
    SCase "m = S m".
      intros.
      rewrite <- H.
      simpl.
      apply c2.
      apply (IHm (m+n) n).
      reflexivity.
Qed.           
(** [] *)

End R.

(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  | all_nil : all P []
  | all_intro : forall x : X, forall l : list X, 
                P x -> all P l -> all P (x::l).

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** ****
    Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? 
*)

Definition allb {X : Type} (test : X -> bool) (l : list X) : Prop :=
  all (fun x : X => test x = true) l.

Eval simpl in (forallb evenb [2,4,6,8]).
Example test1 : allb evenb [2,4,6,8].
Proof.
  apply all_intro. reflexivity.
  apply all_intro. reflexivity.
  apply all_intro. reflexivity.
  apply all_intro. reflexivity.
  apply all_nil.
Qed.

Theorem allb__forallb : forall {X : Type} (test : X -> bool) (l : list X),
  allb test l -> forallb test l = true.
Proof.
  intros.
  induction H as [|x l'].
  Case "l = []".
    reflexivity.
  Case "l = x::l'".
    simpl.
    rewrite -> H.
    rewrite -> IHall.
    reflexivity.
Qed.

Theorem forallb__allb : forall {X : Type} (test : X -> bool) (l : list X),
  forallb test l = true -> allb test l.
Proof.
  intros.
  induction l as [|x l'].
  Case "l = []".
    apply all_nil.
  Case "l = x::l'".
    simpl in H.
    apply andb_true__and in H.
    inversion H.
    apply all_intro.
    apply H0.
    apply IHl'.
    apply H1.
Qed.

Theorem forallb_eq_allb : forall {X : Type} (test : X -> bool) (l : list X),
  forallb test l = true <-> allb test l.
Proof.
  split.
  apply forallb__allb.
  apply allb__forallb.
Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge) *)
(** **** One of the main purposes of Coq is to prove that programs match
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

Inductive order_merge {X : Type} : list X -> list X -> list X -> Prop :=
  | merge_nil : @order_merge X [] [] []
  | merge_lhd : forall x l1 l2 l3, order_merge l1 l2 l3 -> order_merge (x::l1) l2 (x::l3)
  | merge_rhd : forall x l1 l2 l3, order_merge l1 l2 l3 -> order_merge l1 (x::l2) (x::l3).

Example merge_ex1 : order_merge [1,6,2] [4,3] [1,4,6,2,3].
Proof.
  apply merge_lhd.
  apply merge_rhd.
  apply merge_lhd.
  apply merge_lhd.
  apply merge_rhd.
  apply merge_nil.
Qed.

Lemma all_cons_list : forall {X : Type} (P : X -> Prop) (x : X) (l : list X),
  all P (x::l) -> all P l /\ P x.
Proof.
  intros.
  inversion H.
  split.
  apply H3.
  apply H2.
Qed.

Lemma cons_injective : forall {X : Type} (l1 l2 : list X) (x : X),
  l1 = l2 <-> x :: l1 = x :: l2.
Proof.
  intros.
  split.
  Case "left -> right".
    intro.
    rewrite H.
    reflexivity.
  Case "right -> left".
    intros.
    inversion H.
    reflexivity.
Qed.

Theorem filter_challenge : forall {X : Type} (test : X -> bool) (l l1 l2 : list X),
  order_merge l1 l2 l ->
  all (fun x => test x = true) l1 ->
  all (fun x => test x = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l l1 l2.
  intros H.
  induction H as [|y l1 l2 l |y l1 l2 l].
  Case "[] [] []".
    intros.
    reflexivity.
  Case "x::l1 l2 l".
    intros H1 H2.
    apply all_cons_list in H1.
    inversion H1.
    simpl.
    rewrite -> H3.
    apply cons_injective.
    apply IHorder_merge.
    apply H0.
    apply H2.
  Case "l1 x::l2 l".
    intros H1 H2.
    apply all_cons_list in H2.
    inversion H2.
    simpl.
    rewrite -> H3.
    apply IHorder_merge.
    apply H1.
    apply H0.
Qed.    

(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2) *)
(** **** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)
Inductive test_subseq {X:Type} (test:X->Prop) : list X -> list X -> Prop :=
  | test_sub_nil : test_subseq test [] []
  | test_sub_drop : forall (x:X) (sub l:list X), 
                    test_subseq test sub l -> test_subseq test sub (x::l)
  | test_sub_match : forall (x:X) (sub l:list X),
                     test_subseq test sub l -> test x ->test_subseq test (x::sub) (x::l).

Lemma le_Sn_m : forall n m : nat,
  S n <= m -> n <= m.
Proof.
  intros.
  induction H.
  Case "le_n".
    apply le_S.
    apply le_n.
  Case "le_S".
    apply le_S.
    apply IHle.
Qed.

Lemma le_n_Sm : forall n m : nat,
  n <= m -> n <= S m.
Proof.
  intros.
  induction H.
  Case "le_n".
    apply le_S.
    apply le_n.
  Case "le_S".
    apply le_S.
    apply IHle.
Qed.      

Lemma le_Sn_Sm : forall n m : nat,
  n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  Case "le_n".
    apply le_n.
  Case "le_S".
    apply le_S.
    apply IHle.
Qed.  

Theorem filter_challenge2 : forall {X:Type} (test:X->bool) (sub l:list X),
  test_subseq (fun x:X => test x = true) sub l ->
  length sub <= length (filter test l).
Proof.
  intros.
  induction H.
  Case "test_sub_nil".
    reflexivity.
  Case "test_sub_drop".
    simpl.
    remember (test x) as test_x.
    destruct test_x.
    SCase "test x = true".
      simpl.
      apply le_n_Sm.
      apply IHtest_subseq.
    SCase "test x = false".
      apply IHtest_subseq.
  Case "test_sub_match".
    simpl.
    rewrite -> H0.
    simpl.
    apply le_Sn_Sm.
    apply IHtest_subseq.
Qed.

Lemma ble_Sn_m : forall n m : nat,
  ble_nat (S n) m = true -> ble_nat n m = true.
Proof.
  induction n.
  Case "n = 0".
    intros.
    reflexivity.
  Case "n = S n".
    intros.
    destruct m.
    SCase "m = 0".
      inversion H.
    SCase "m = S m".
      simpl.
      apply IHn.
      apply H.
Qed.
    
Lemma ble_n_Sm : forall n m : nat,
  ble_nat n m = true -> ble_nat n (S m) = true.
Proof.
  intros.
  generalize dependent m.
  induction n.
  Case "n = 0".
    intros.
    reflexivity.
  Case "n = S n".
    intros.
    apply ble_Sn_m in H.
    simpl.
    apply H.
Qed.      
    
Theorem filter_challenge2' : forall {X:Type} (test:X->bool) (sub l:list X),
  test_subseq (fun x:X => test x = true) sub l ->
  ble_nat (length sub) (length (filter test l)) = true.
Proof.
  intros.
  induction H.
  Case "test_sub_nil".
    reflexivity.
  Case "test_sub_drop".
    simpl.
    remember (test x) as test_x.
    destruct test_x.
    SCase "test x = true".
      simpl.
      apply ble_n_Sm.
      apply IHtest_subseq.
    SCase "test x = false".
      apply IHtest_subseq.
  Case "test_sub_match".
    simpl.
    rewrite -> H0.
    simpl.
    apply IHtest_subseq.
Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced (no_repeats) *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall {X:Type} (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  intros X xs.
  induction xs as [|x1 xs'].
  Case "xs = []".
    intros.
    simpl in H.
    right.
    apply H.
  Case "xs = x1::xs'".
    intros.
    inversion H.
    SCase "ai_here".
      left.
      apply ai_here.
    SCase "ai_later".
      apply IHxs' in H1.
      inversion H1.
      SSCase "left".
        left.
        apply ai_later.
        apply H3.
      SSCase "right".
        right.
        apply H3.
Qed.

Lemma app_appears_in : forall {X:Type} (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros X xs.
  induction xs as [|y xs'].
  Case "xs = []".
    intros.
    inversion H.
    SCase "left".
      inversion H0.
    SCase "right".
      apply H0.
  Case "xs = y::xs'".
    intros.
    inversion H.
    SCase "left".
      inversion H0.
      SSCase "ai_here".
        apply ai_here.
      SSCase "ai_later".
        apply ai_later.
        apply IHxs'.
        left.
        apply H2.
    SCase "right".
      apply ai_later.
      apply IHxs'.
      right.
      apply H0.
Qed.

(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

Inductive disjoint {X : Type} (l1 l2 : list X) : Prop :=
  | dsjt : (forall (x:X) , appears_in x l1 -> ~ appears_in x l2) -> disjoint l1 l2.

Definition disjoint' {X : Type} (x:X) (l1 l2 : list X) : Prop :=
  appears_in x l1 -> ~ appears_in x l2.

(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

Inductive no_repeats {X : Type} : list X -> Prop :=
  | nr_nil : no_repeats []
  | nr_cons : forall (x : X) (l : list X), no_repeats l -> ~ appears_in x l -> no_repeats (x::l).

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)

Lemma disjoint_cons : forall {X : Type} (x : X) (l1 l2 : list X),
  disjoint (x::l1) l2 -> disjoint l1 l2.
Proof.
  intros.
  induction l1 as [|y l1'].
  Case "l1 = []".
    apply dsjt.
    intros.
    inversion H0.
  Case "l1 = y::l1'".
    apply dsjt.
    intros.
    inversion H.
    apply H1.
    apply ai_later.
    apply H0.
Qed.    

Lemma not_appears_app : forall {X : Type} (x : X) (l1 l2 : list X),
   ~ appears_in x l1 -> ~ appears_in x l2 -> ~ appears_in x (l1++l2).
Proof.
  intros.
  unfold not.
  intros.
  apply appears_in_app in H1.
  inversion H1.
  Case "left".
    unfold not in H.
    apply H.
    apply H2.
  Case "right".
    unfold not in H0.
    apply H0.
    apply H2.
Qed.     

Theorem no_repeats_no_joint : forall {X:Type} (l1 l2 : list X),
  no_repeats l1 -> no_repeats l2 -> disjoint l1 l2 ->
  no_repeats (l1++l2).
Proof.
  intros X l1.
  induction l1 as [|x l1'].
  Case "l1 = []".
    intros l2 H1 H2 H.
    simpl.
    apply H2.
  Case "l1 = x::l1'".
    intros l2 H1 H2 H.
    apply nr_cons.
    apply IHl1'.
    inversion H1.
    apply H4.
    apply H2.
    apply disjoint_cons in H.
    apply H.
    apply not_appears_app.
    inversion H1.
    apply H5.
    inversion H.
    apply H0.
    apply ai_here.
Qed.          
    
(** [] *)

(** **** Exercise: 2 stars, optional (le_exercises) *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n.
  Case "n = 0".
    apply le_n.
  Case "n = S n".
    apply le_S.
    apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  apply le_Sn_Sm.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros n m.  generalize dependent n.  induction m. 
  Case "m = 0".
    intros.
    inversion H.
    SCase "le_n".
      reflexivity.
    SCase "le_S".
      inversion H1.
  Case "m = S m".
    intros.
    inversion H.
    SCase "le_n".
      reflexivity.
    SCase "le_S".
      apply IHm in H1.
      apply le_n_Sm.
      apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  intros.
  induction b.
  Case "b = 0".
    rewrite -> plus_0_r.
    apply le_n.
  Case "b = S b".
    rewrite <- plus_n_Sm.
    apply le_S.
    apply IHb.
Qed.      

Lemma le_lt : forall n m : nat,
  n <= m -> n < S m.
Proof.
  intros.
  inversion H.
  Case "le_n".
    apply le_n.
  Case "le_S".
    apply le_S.
    apply n_le_m__Sn_le_Sm.
    apply H0.
Qed.

Lemma lt_le : forall n m : nat,
  n < m -> n <= m.
Proof.
  intros.
  inversion H.
  Case "le_n".
    apply le_S.
    apply le_n.
  Case "le_S".
    apply le_S.
    apply le_Sn_m.
    apply H0.
Qed.
    
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
  intros.
  induction H.
  Case "le_n".
    split.
    SCase "left".
      apply le_lt.
      apply le_plus_l.
    SCase "right".
      apply le_lt.
      rewrite -> plus_comm.
      apply le_plus_l.
  Case "le_S".
    split.
    SCase "left".
      inversion IHle.
      apply le_lt.
      apply lt_le.
      apply H0.
    SCase "right".
      inversion IHle.
      apply le_lt.
      apply lt_le.
      apply H1.
Qed.  

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  intros.
  inversion H.
  Case "le_n".
    apply le_S.
    apply le_n.
  Case "le_S".
    apply le_S.
    apply le_n_Sm.
    apply H0.
Qed.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  intros n.
  induction n.
  Case "n = 0".
    intros.
    apply O_le_n.
  Case "n = S n".
    intros.
    destruct m.
    SCase "m = 0".
      inversion H.
    SCase "m = S m".
      apply n_le_m__Sn_le_Sm.
      apply IHn.
      simpl in H.
      apply H.
Qed.      

Theorem ble_nat_n_Sn_false : forall n m,
  ble_nat n (S m) = false ->
  ble_nat n m = false.
Proof. 
  intros n.
  induction n.
  Case "n = 0".
    intros.
    inversion H.
  Case "n = S n".
    intros.
    simpl in H.
    destruct m.
    SCase "m  = 0".
      reflexivity.
    SCase "m = S m".
      simpl.
      apply IHn.
      apply H.
Qed.    

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  Case "m = 0".
    intros.
    unfold not.
    intros.
    inversion H0.
    rewrite -> H1 in H.
    inversion H.
  Case "m = S m".
    intros.
    unfold not.
    intros.
    inversion H0.
    SCase "le_n".
      rewrite -> H1 in H.
      rewrite <- ble_nat_refl in H.
      inversion H.
    SCase "le_S".
      unfold not in IHm.
      apply (IHm n).
      apply ble_nat_n_Sn_false.
      apply H.
      apply H2.
Qed.
(** [] *)

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
  | nst_nil : nostutter []
  | nst_one : forall (x : nat), nostutter [x]
  | nst_cons : forall (x y : nat) (l : list nat), nostutter (y::l) -> ~ x = y ->
               nostutter (x::y::l).

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

Example test_nostutter_1:      nostutter [3,1,4,1,5,6].
Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_2:  nostutter [].
Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_4:      not (nostutter [3,1,1,4]).
Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H5; auto. Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle) *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall {X:Type} (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros X l1 l2. 
  induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. 
    rewrite -> IHl1'. 
    reflexivity. 
Qed.

Print appears_in.
Lemma appears_in_app_split : forall {X:Type} (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros X x l.
  induction l as [|y l'].
  Case "l = []".
    intros.
    inversion H.
  Case "l = y::l'".
    intros.
    inversion H.
      SCase "ai_here".
        exists [].
        exists l'.
        reflexivity.
      SCase "ai_later".
        apply IHl' in H1.
        inversion H1 as [sl1 Hl2].
        inversion Hl2 as [sl2 Hl].
        exists (y::sl1).
        exists sl2.
        rewrite -> Hl.
        reflexivity.
Qed.    

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | rp_init : forall (x : X) (l : list X), appears_in x l -> repeats (x::l)
  | rp_cons : forall (x : X) (l : list X), repeats l -> repeats (x::l).

(** Now here's a way to formalize the pigeonhole principle. List [l2]
   represents a list of pigeonhole labels, and list [l1] represents an
   assignment of items to labels: if there are more items than labels,
   at least two items must have the same label.  You will almost
   certainly need to use the [excluded_middle] hypothesis. *)
Print excluded_middle.

Lemma diff_ai : forall (X : Type) (x y : X) (l1 l2 : list X), 
  excluded_middle -> 
  x <> y -> 
  appears_in y (l1 ++ x :: l2) -> 
  appears_in y (l1 ++ l2).
Proof.
  induction l1 as [|x1 l1'].
  Case "l1 = []".
    intros.
    simpl.
    simpl in H1.
    inversion H1.
    SCase "ai_here".
      apply ex_falso_quodlibet.
      apply H0.
      symmetry.
      apply H3.
    SCase "ai_later".
      apply H3.
  Case "l1 = x1::l1'".
    intros.
    simpl.
    assert ((y = x1) \/ ~(y = x1)).
    SCase "Proof of assert".
      unfold excluded_middle in H.
      apply H.
    inversion H2.
    SCase "left : y = x1".
      rewrite -> H3.
      apply ai_here.
    SCase "right : y <> x1".
      apply ai_later.
      inversion H1.
      SSCase "ai_here".
        apply ex_falso_quodlibet.
        apply H3.
        apply H5.
      SSCase "ai_later".
        apply IHl1'.
        apply H.
        apply H0.
        apply H5.
Qed.

Theorem pigeonhole_principle: forall {X:Type} (l1 l2:list X),
  excluded_middle -> 
  (forall x, appears_in x l1 -> appears_in x l2) -> 
  length l2 < length l1 -> 
  repeats l1.  
Proof. intros X l1. induction l1 as [|x1 l1'].
  Case "l1 = []".
    intros.
    inversion H1.
  Case "l1 = x1::l1'".
    intros.
    unfold excluded_middle in H.
    assert ((appears_in x1 l1') \/ ~(appears_in x1 l1')).
    apply H.
    inversion H2.
    SCase "left : x1 in l1'".
      apply rp_init.
      apply H3.
    SCase "right : x1 not in l1'".
      apply rp_cons.
      assert (exists t1, exists t2, l2 = t1 ++ (x1::t2)).
      SSCase "proof of assert".
        apply appears_in_app_split.
        apply H0.
        apply ai_here.
      inversion H4 as [t1].
      inversion H5 as [t2].
      apply (IHl1' (t1 ++ t2)).
      unfold excluded_middle.
      apply H.
      intros.
      assert ((x = x1) \/ ~(x = x1)).
      SSCase "Proof of assert".
        apply H.
      inversion H8.
      SSCase "left : x = x1".
        apply ex_falso_quodlibet.
        apply H3.
        rewrite -> H9 in H7.
        apply H7.
      SSCase "right : x <> x1".
        assert (appears_in x1 l2).
        SSSCase "Proof of assert".
          apply H0.
          apply ai_here.
          apply (diff_ai X x1 x t1 t2).
          unfold excluded_middle.
          apply H.
          unfold not.
          intros.
          rewrite -> H11 in H9.
          unfold not in H9.
          apply H9.
          reflexivity.
          rewrite <- H6.
          apply H0.
          apply ai_later.
          apply H7.
          rewrite -> app_length.
          rewrite -> H6 in H1.
          rewrite -> app_length in H1.
          simpl in H1.
          rewrite <- plus_n_Sm in H1.
          apply Sn_le_Sm__n_le_m in H1.
          apply H1.
Qed. 
(** [] *)

(* $Date: 2013-02-10 18:08:54 -0500 (Sun, 10 Feb 2013) $ *)

(** **** KE DING 8318 *)