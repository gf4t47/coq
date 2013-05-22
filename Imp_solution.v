(** * Imp: Simple Imperative Programs *)

(* HIDE: At some point we could consider moving material from
   HoareLists.v to this chapter (and into later files, as
   appropriate).  We haven't done it yet because it's a shame to
   complicate the nice simple presentation here when it's used as the
   basis for applications like Xavier's static analysis lectures. *)
(* HIDE: Another nice challenge exercise at some point would be to add
   C-style arrays (i.e., indirect read/write).  This sets up some
   really nice challenge problems in Hoare.v (reasoning about arrays /
   aliasing / etc.). *)
(* SOONER: It's a bit silly that we prove all these awkward versions
   of theorems about states and then in the very next chapter
   introduce functional_extensionality, which would have allowed us to
   do it the easier way.  Why not just introduct functional
   extensionality here.  (Or, indeed, introduce it earlier, in the
   Logic chapter or someplace like that.) *)
(** In this chapter, we begin a new direction that will continue for
    the rest of the course.  Up to now most of our attention has been
    focused on various aspects of Coq itself, while from now on we'll
    mostly be using Coq to formalize other things.  (We'll continue to
    pause from time to time to introduce a few additional aspects of
    Coq.)

    Our first case study is a _simple imperative programming language_
    called Imp, embodying a tiny core fragment of conventional
    mainstream languages such as C and Java.  Here is a familiar
    mathematical function written in Imp.
[[
     Z ::= X;
     Y ::= 1;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;
       Z ::= Z - 1
     END
]]
*)

(* HIDEFROMADVANCED *)
(** This chapter looks at how to define the _syntax_ and _semantics_
    of Imp; the chapters that follow develop a theory of _program
    equivalence_ and introduce _Hoare Logic_, a widely used logic for
    reasoning about imperative programs. *)
(** HIDE: (old TERSE) Enough tiny examples!  Time to use Coq for
    something more interesting... *)

(* /HIDEFROMADVANCED *)
(* ####################################################### *)
(** *** Sflib *)

(** FULL: A minor technical point: Instead of asking Coq to import our
    earlier definitions from chapter [Logic], we import a small library
    called [Sflib.v], containing just a few definitions and theorems
    from earlier chapters that we'll actually use in the rest of the
    course.  This change should be nearly invisible, since most of what's
    missing from Sflib has identical definitions in the Coq standard
    library.  The main reason for doing it is to tidy the global Coq
    environment so that, for example, it is easier to search for
    relevant theorems. *)
(** TERSE: Note that we import earlier definitions from [Sflib]
    here, not [Logic]: *)

Require Export SfLib.

(* ####################################################### *)
(** * Arithmetic and Boolean Expressions *)

(* SOONER: At this point, I usually take some of the lecture time to
   give a high-level picture of the structure of an interpreter, the
   processes of lexing and parsing, the notion of ASTs, etc.  Might be
   nice to work some of those ideas into the notes. - BCP *)
(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)

(* ####################################################### *)
(** ** Syntax *)

(* TERSE: HIDEFROMHTML *)
Module AExp.

(* TERSE: /HIDEFROMHTML *)
(** FULL: These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)
(** TERSE: _Abstract syntax trees_ for arithmetic and boolean expressions: *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(** FULL: In this chapter, we'll elide the translation from the
    concrete syntax that a programmer would actually write to these
    abstract syntax trees -- the process that, for example, would
    translate the string ["1+2*3"] to the AST [APlus (ANum
    1) (AMult (ANum 2) (ANum 3))].  The optional chapter [ImpParser]
    develops a simple implementation of a lexical analyzer and parser
    that can perform this translation.  You do _not_ need to
    understand that file to understand this one, but if you haven't
    taken a course where these techniques are covered (e.g., a
    compilers course) you may want to skim it. *)

(** For comparison, here's a conventional BNF (Backus-Naur Form)
    grammar defining the same abstract syntax:
[[
    a ::= nat
        | a + a
        | a - a
        | a * a

    b ::= true
        | false
        | a = a
        | a <= a
        | b and b
        | not b
]]
*)

(** FULL: Compared to the Coq version above...

       - The BNF is more informal -- for example, it gives some
         suggestions about the surface syntax of expressions (like the
         fact that the addition operation is written [+] and is an
         infix symbol) while leaving other aspects of lexical analysis
         and parsing (like the relative precedence of [+], [-], and
         [*]) unspecified.  Some additional information -- and human
         intelligence -- would be required to turn this description
         into a formal definition (when implementing a compiler, for
         example).

         The Coq version consistently omits all this information and
         concentrates on the abstract syntax only.

       - On the other hand, the BNF version is lighter and
         easier to read.  Its informality makes it flexible, which is
         a huge advantage in situations like discussions at the
         blackboard, where conveying general ideas is more important
         than getting every detail nailed down precisely.

         Indeed, there are dozens of BNF-like notations and people
         switch freely among them, usually without bothering to say which
         form of BNF they're using because there is no need to: a
         rough-and-ready informal understanding is all that's
         needed. *)

(* HIDEFROMADVANCED *)
(** FULL: It's good to be comfortable with both sorts of notations:
    informal ones for communicating between humans and formal ones for
    carrying out implementations and proofs. *)

(* /HIDEFROMADVANCED *)
(* ####################################################### *)
(** ** Evaluation *)

(** _Evaluating_ an arithmetic expression produces a number. *)

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** Similarly, evaluating a boolean expression yields a boolean. *)

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2   => ble_nat (aeval a1) (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

(* QUIZ *)
(** What does the following expression evaluate to?
[[
  aeval (APlus (ANum 3) (AMinus (ANum 4) (ANum 1)))
]]

  (1) true

  (2) false

  (3) 0

  (4) 3

  (5) 6

*)
(* /QUIZ *)

(* ####################################################### *)
(** ** Optimization *)

(** FULL: We haven't defined very much yet, but we can already get
    some mileage out of the definitions.  Suppose we define a function
    that takes an arithmetic expression and slightly simplifies it,
    changing every occurrence of [0+e] (i.e., [(APlus (ANum 0) e])
    into just [e]. *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

(** FULL: To make sure our optimization is doing the right thing we
    can test it on some examples and see if the output looks OK. *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

(** FULL: But if we want to be sure the optimization is correct --
    i.e., that evaluating an optimized expression gives the same
    result as the original -- we should prove it. *)

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  Case "ANum". reflexivity.
  Case "APlus". destruct a1.
    SCase "a1 = ANum n". destruct n.
      SSCase "n = 0".  simpl. apply IHa2.
      SSCase "n <> 0". simpl. rewrite IHa2. reflexivity.
    SCase "a1 = APlus a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    SCase "a1 = AMinus a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    SCase "a1 = AMult a1_1 a1_2".
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  Case "AMinus".
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  Case "AMult".
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.

(* ####################################################### *)
(** * Coq Automation *)

(** FULL: The repetition in this last proof is starting to be a little
    annoying.  If either the language of arithmetic expressions or the
    optimization being proved sound were significantly more complex,
    it would begin to be a real problem.

    So far, we've been doing all our proofs using just a small handful
    of Coq's tactics and completely ignoring its powerful facilities
    for constructing parts of proofs automatically.  This section
    introduces some of these facilities, and we will see more over the
    next several chapters.  Getting used to them will take some
    energy -- Coq's automation is a power tool -- but it will allow us
    to scale up our efforts to more complex definitions and more
    interesting properties without becoming overwhelmed by boring,
    repetitive, low-level details. *)
(** TERSE: That last proof was getting a little repetitive.  Let's pause
    to learn a few more Coq tricks. *)

(* ####################################################### *)
(** ** Tacticals *)

(** _Tacticals_ is Coq's term for tactics that take other tactics as
    arguments -- "higher-order tactics," if you will.  *)

(* ####################################################### *)
(** *** The [repeat] Tactical *)

(** The [repeat] tactical takes another tactic and keeps applying
    this tactic until the tactic fails. Here is an example showing
    that [100] is even using repeat. *)

Theorem ev100 : ev 100.
Proof.
  repeat (apply ev_SS). (* applies ev_SS 50 times,
                           until [apply ev_SS] fails *)
  apply ev_0.
Qed.
(* Print ev100. *)

(* FULL *)
(** The [repeat T] tactic never fails; if the tactic [T] doesn't apply
    to the original goal, then repeat still succeeds without changing
    the original goal (it repeats zero times). *)

Theorem ev100' : ev 100.
Proof.
  repeat (apply ev_0). (* doesn't fail, applies ev_0 zero times *)
  repeat (apply ev_SS). apply ev_0. (* we can continue the proof *)
Qed.

(** The [repeat T] tactic does not have any bound on the number of
    times it applies [T]. If [T] is a tactic that always succeeds then
    repeat [T] will loop forever (e.g. [repeat simpl] loops forever
    since [simpl] always succeeds). While Coq's term language is
    guaranteed to terminate, Coq's tactic language is not! *)
(* /FULL *)

(* ####################################################### *)
(** *** The [try] Tactical *)

(** If [T] is a tactic, then [try T] is a tactic that is just like [T]
    except that, if [T] fails, [try T] _successfully_ does nothing at
    all (instead of failing). *)
(* SOONER: Maybe we want to move the discussion of "try solve" from
   later to here?  It might be helpful for students, but it will make
   this already-longish chapter a bit longer... *)

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* this just does [reflexivity] *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* just [reflexivity] would have failed *)
  apply HP. (* we can still finish the proof in some other way *)
Qed.

(** FULL: Using [try] in a completely manual proof is a bit silly, but
    we'll see below that [try] is very useful for doing automated
    proofs in conjunction with the [;] tactical. *)

(* ####################################################### *)
(** *** The [;] Tactical (Simple Form) *)

(** In its most commonly used form, the [;] tactical takes two tactics
    as argument: [T;T'] first performs the tactic [T] and then
    performs the tactic [T'] on _each subgoal_ generated by [T]. *)

(** FULL: For example, consider the following trivial lemma: *)
(** TERSE: For example: *)

Lemma foo : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    Case "n=0". simpl. reflexivity.
    Case "n=Sn'". simpl. reflexivity.
Qed.

(** We can simplify this proof using the [;] tactical: *)

Lemma foo' : forall n, ble_nat 0 n = true.
Proof.
  intros.
  destruct n; (* [destruct] the current goal *)
  simpl; (* then [simpl] each resulting subgoal *)
  reflexivity. (* and do [reflexivity] on each resulting subgoal *)
Qed.

(** Using [try] and [;] together, we can get rid of the repetition in
    the proof that was bothering us a little while ago. *)

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  (* The remaining cases -- ANum and APlus -- are different *)
  Case "ANum". reflexivity.
  Case "APlus".
    destruct a1;
      (* Again, most cases follow directly by the IH *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the [try...] does nothing,
       is when [e1 = ANum n]. In this case, we have to destruct
       [n] (to see whether the optimization applies) and rewrite
       with the induction hypothesis. *)
    SCase "a1 = ANum n". destruct n;
      simpl; rewrite IHa2; reflexivity.   Qed.

(* HIDEFROMADVANCED *)
(* FULL *)
(** Coq experts often use this "[...; try... ]" idiom after a tactic
    like [induction] to take care of many similar cases all at once.
    Naturally, this practice has an analog in informal proofs.

    Here is an informal proof of this theorem that matches the
    structure of the formal one:

    _Theorem_: For all arithmetic expressions [a],
[[
       aeval (optimize_0plus a) = aeval a.
]]
    _Proof_: By induction on [a].  The [AMinus] and [AMult] cases
    follow directly from the IH.  The remaining cases are as follows:

      - Suppose [a = ANum n] for some [n].  We must show
[[
          aeval (optimize_0plus (ANum n)) = aeval (ANum n).
]]
        This is immediate from the definition of [optimize_0plus].

      - Suppose [a = APlus a1 a2] for some [a1] and [a2].  We
        must show
[[
          aeval (optimize_0plus (APlus a1 a2))
        = aeval (APlus a1 a2).
]]
        Consider the possible forms of [a1].  For most of them,
        [optimize_0plus] simply calls itself recursively for the
        subexpressions and rebuilds a new expression of the same form
        as [a1]; in these cases, the result follows directly from the
        IH.

        The interesting case is when [a1 = ANum n] for some [n].
        If [n = ANum 0], then
[[
          optimize_0plus (APlus a1 a2) = optimize_0plus a2
]]
        and the IH for [a2] is exactly what we need.  On the other
        hand, if [n = S n'] for some [n'], then again [optimize_0plus]
        simply calls itself recursively, and the result follows from
        the IH.  [] *)

(* /FULL *)
(* /HIDEFROMADVANCED *)
(** FULL: This proof can still be improved: the first case (for [a = ANum
    n]) is very trivial -- even more trivial than the cases that we
    said simply followed from the IH -- yet we have chosen to write it
    out in full.  It would be better and clearer to drop it and just
    say, at the top, "Most cases are either immediate or direct from
    the IH.  The only interesting case is the one for [APlus]..."  We
    can make the same improvement in our formal proof too.  Here's how
    it looks: *)
(** TERSE: This proof can be further improved by removing the trivial
    first case (for [e = ANum n]). *)

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  Case "APlus".
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    SCase "a1 = ANum n". destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

(* FULL *)
(* ####################################################### *)
(** *** The [;] Tactical (General Form) *)

(** The [;] tactical has a more general than the simple [T;T'] we've
    seen above, which is sometimes also useful.  If [T], [T1], ...,
    [Tn] are tactics, then
[[
      T; [T1 | T2 | ... | Tn]
]]
   is a tactic that first performs [T] and then performs [T1] on the
   first subgoal generated by [T], performs [T2] on the second
   subgoal, etc.

   So [T;T'] is just special notation for the case when all of the
   [Ti]'s are the same tactic; i.e. [T;T'] is just a shorthand for:
[[
      T; [T' | T' | ... | T']
]]
*)
(* /FULL *)

(* ####################################################### *)
(** ** Defining New Tactic Notations *)

(** FULL: Coq also provides several ways of "programming" tactic scripts.

      - The [Tactic Notation] idiom illustrated below gives a handy
        way to define "shorthand tactics" that bundle several tactics
        into a single command.

      - For more sophisticated programming, Coq offers a small
        built-in programming language called [Ltac] with primitives
        that can examine and modify the proof state.  The details are
        a bit too complicated to get into here (and it is generally
        agreed that [Ltac] is not the most beautiful part of Coq's
        design!), but they can be found in the reference manual, and
        there are many examples of [Ltac] definitions in the Coq
        standard library that you can use as examples.

      - There is also an OCaml API, which can be used to build tactics
        that access Coq's internal structures at a lower level, but
        this is seldom worth the trouble for ordinary Coq users.

The [Tactic Notation] mechanism is the easiest to come to grips with,
and it offers plenty of power for many purposes.  Here's an example.
*)
(** TERSE: Coq also provides several ways of "programming" tactic scripts:
     - [Ltac]: scripting language for tactics
     - [Tactic Notation]: syntax extension for tactics
     - OCaml tactic scripting API (only for wizards)

An example [Tactic Notation]: *)

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(* FULL *)
(** This defines a new tactical called [simpl_and_try] which
    takes one tactic [c] as an argument, and is defined to be
    equivalent to the tactic [simpl; try c].  For example, writing
    "[simpl_and_try reflexivity.]" in a proof would be the same as
    writing "[simpl; try reflexivity.]" *)

(** The next subsection gives a more sophisticated use of this
    feature... *)

(* /FULL *)
(* ####################################################### *)
(** *** Bulletproofing Case Analyses *)

(** FULL: Being able to deal with most of the cases of an [induction]
    or [destruct] all at the same time is very convenient, but it can
    also be a little confusing.  One problem that often comes up is
    that _maintaining_ proofs written in this style can be difficult.
    For example, suppose that, later, we extended the definition of
    [aexp] with another constructor that also required a special
    argument.  The above proof might break because Coq generated the
    subgoals for this constructor before the one for [APlus], so that,
    at the point when we start working on the [APlus] case, Coq is
    actually expecting the argument for a completely different
    constructor.  What we'd like is to get a sensible error message
    saying "I was expecting the [AFoo] case at this point, but the
    proof script is talking about [APlus]."  Here's a nice trick (due
    to Aaron Bohannon) that smoothly achieves this. *)

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(** ([Case_aux] implements the common functionality of [Case],
    [SCase], [SSCase], etc.  For example, [Case "foo"] is defined as
    [Case_aux Case "foo".) *)

(** For example, if [a] is a variable of type [aexp], then doing
[[
      aexp_cases (induction a) Case
]]
    will perform an induction on [a] (the same as if we had just typed
    [induction a]) and _also_ add a [Case] tag to each subgoal
    generated by the [induction], labeling which constructor it comes
    from.  For example, here is yet another proof of
    [optimize_0plus_sound], using [aexp_cases]: *)

Theorem optimize_0plus_sound''': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  aexp_cases (induction a) Case;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try reflexivity.
  (* At this point, there is already an ["APlus"] case name
     in the context.  The [Case "APlus"] here in the proof
     text has the effect of a sanity check: if the "Case"
     string in the context is anything _other_ than ["APlus"]
     (for example, because we added a clause to the definition
     of [aexp] and forgot to change the proof) we'll get a
     helpful error at this point telling us that this is now
     the wrong case. *)
  Case "APlus".
    aexp_cases (destruct a1) SCase;
      try (simpl; simpl in IHa1;
           rewrite IHa1; rewrite IHa2; reflexivity).
    SCase "ANum". destruct n;
      simpl; rewrite IHa2; reflexivity.  Qed.

(* FULL *)
(* EX3 (optimize_0plus_b) *)
(** Since the [optimize_0plus] tranformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  (* ADMIT *)
  match b with
  | BTrue       => BTrue
  | BFalse      => BFalse
  | BEq a1 a2   => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2   => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b1     => BNot (optimize_0plus_b b1)
  | BAnd b1 b2  => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.
(* /ADMIT *)

(* QUIETSOLUTION *)
Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].
(* /QUIETSOLUTION *)

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  (* ADMITTED *)
  bexp_cases (induction b) Case;
     simpl;
     try (repeat rewrite optimize_0plus_sound);
     try reflexivity.
  Case "BNot".
    rewrite IHb.  reflexivity.
  Case "BAnd".
    rewrite IHb1. rewrite IHb2. reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX4? (optimizer) *)
(** _Design exercise_: The optimization implemented by our
    [optimize_0plus] function is only one of many imaginable
    optimizations on arithmetic and boolean expressions.  Write a more
    sophisticated optimizer and prove it correct.

(* SOLUTION *)
  (* LATER: add a possible solution here? *)
(* /SOLUTION *)
*)
(** [] *)

(* /FULL *)
(* ####################################################### *)
(** ** The [omega] Tactic *)

(** The [omega] tactic implements a decision procedure for a subset of
    first-order logic called _Presburger arithmetic_.  It is based on
    the Omega algorithm invented in 1992 by William Pugh.

    If the goal is a universally quantified formula made out of

      - numeric constants, addition ([+] and [S]), subtraction ([-]
        and [pred]), and multiplication by constants (this is what
        makes it Presburger arithmetic),

      - equality ([=] and [<>]) and inequality ([<=]), and

      - the logical connectives [/\], [\/], [~], and [->],

    then invoking [omega] will either solve the goal or tell you that
    it is actually false. *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

(** FULL: Liebniz wrote, "It is unworthy of excellent men to lose
    hours like slaves in the labor of calculation which could be
    relegated to anyone else if machines were used."  We recommend
    using the omega tactic whenever possible. *)

(* ####################################################### *)
(** ** A Few More Handy Tactics *)

(** Finally, here are some miscellaneous tactics that you may find
    convenient.

     - [clear H]: Delete hypothesis [H] from the context.

     - [subst x]: Find an assumption [x = e] or [e = x] in the
       context, replace [x] with [e] throughout the context and
       current goal, and clear the assumption.

     - [subst]: Substitute away _all_ assumptions of the form [x = e]
       or [e = x].

     - [rename... into...]: Change the name of a hypothesis in the
       proof context.  For example, if the context includes a variable
       named [x], then [rename x into y] will change all occurrences
       of [x] to [y].

     - [assumption]: Try to find a hypothesis [H] in the context that
       exactly matches the goal; if one is found, behave just like
       [apply H].

     - [contradiction]: Try to find a hypothesis [H] in the current
       context that is logically equivalent to [False].  If one is
       found, solve the goal.

     - [constructor]: Try to find a constructor [c] (from some
       [Inductive] definition in the current environment) that can be
       applied to solve the current goal.  If one is found, behave
       like [apply c]. *)

(** FULL: We'll see many examples of these in the proofs below. *)

(* ####################################################### *)
(** * Evaluation as a Relation *)

(* HIDEFROMADVANCED *)
(** We have presented [aeval] and [beval] as functions defined by
    [Fixpoints].  Another way to think about evaluation -- one that we
    will see is often more flexible -- is as a _relation_ between
    expressions and their values.  This leads naturally to [Inductive]
    definitions like the following one for arithmetic
    expressions... *)

(* TERSE: HIDEFROMHTML *)
Module aevalR_first_try.

(* TERSE: /HIDEFROMHTML *)
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum  : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

(** FULL: As is often the case with relations, we'll find it
    convenient to define infix notation for [aevalR].  We'll write [e
    || n] to mean that arithmetic expression [e] evaluates to value
    [n].  (This notation is one place where the limitation to ASCII
    symbols becomes a little bothersome.  The standard notation for
    the evaluation relation is a double down-arrow.  We'll typeset it
    like this in the HTML version of the notes and use a double
    vertical bar as the closest approximation in [.v] files.)  *)

(** TERSE: A standard notation for "evaluates to": *)

Notation "e '||' n" := (aevalR e n) : type_scope.
(* HIDEFROMHTML *)

End aevalR_first_try.
(* /HIDEFROMHTML *)

(** FULL: In fact, Coq provides a way to use this notation in the definition
    of [aevalR] itself.  This avoids situations where we're working on
    a proof involving statements in the form [e || n] but we have to
    refer back to a definition written using the form [aevalR e n].

    We do this by first "reserving" the notation, then giving the
    definition together with a declaration of what the notation
    means. *)
(* /HIDEFROMADVANCED *)

(** TERSE: If we "reserve" the notation in advance, we can also use it
    in the definition: *)

Reserved Notation "e '||' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)

  where "e '||' n" := (aevalR e n) : type_scope.

Tactic Notation "aevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_ANum" | Case_aux c "E_APlus"
  | Case_aux c "E_AMinus" | Case_aux c "E_AMult" ].

(* HIDE *)
(* SOONER: These didn't work well -- no way to have the question and
   the relevant inductive definition on the screen together! *)
(* QUIZ *)
(** Which rules are needed to show the following?
[[
   (AMult (APlus (ANum 3) (ANum 1)) (ANum 0)) || 0
]]

  (1) [E_ANum] and [E_APlus]

  (2) [E_ANum] only

  (3) [E_ANum] and [E_AMult]

  (4) [E_AMult] and [E_APlus]

  (5) [E_ANum], [E_AMult], and [E_APlus]

*)
(* /QUIZ *)
(* QUIZ *)
(** What about this?
[[
   (AMinus (ANum 3) (AMinus (ANum 2) (ANum 1))) || 2
]]

  (1) [E_ANum] and [E_APlus]

  (2) [E_ANum] only

  (3) [E_ANum] and [E_AMinus]

  (4) [E_AMinus] and [E_APlus]

  (5) [E_ANum], [E_AMinus], and [E_APlus]

*)
(* /QUIZ *)
(* /HIDE *)
(* QUIZ *)
(** Write down a term with the following type:
[[
   (AMinus (ANum 3) (AMinus (ANum 2) (ANum 1))) || 2
]]

*)
(* /QUIZ *)

(* ####################################################### *)
(** ** Inference Rule Notation *)

(** FULL: In informal discussions, it is convenient write the rules for
    [aevalR] and similar relations in the more readable graphical form
    of _inference rules_, where the premises above the line justify
    the conclusion below the line (we have already seen them in the
    Prop chapter). *)

(** For example, the constructor [E_APlus]...
[[
      | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
          aevalR e1 n1 ->
          aevalR e2 n2 ->
          aevalR (APlus e1 e2) (n1 + n2)
]]
    ...would be written like this as an inference rule:
[[[
                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2
]]]
*)

(** FULL: Formally, there is nothing very deep about inference rules:
    they are just implications.  You can read the rule name on the
    right as the name of the constructor and read each of the
    linebreaks between the premises above the line and the line itself
    as [->].  All the variables mentioned in the rule ([e1], [n1],
    etc.) are implicitly bound by universal quantifiers at the
    beginning. (Such variables are often called _metavariables_ to
    distinguish them from the variables of the language we are
    defining.  At the moment, our arithmetic expressions don't include
    variables, but we'll soon be adding them.)  The whole collection
    of rules is understood as being wrapped in an [Inductive]
    declaration (informally, this is either elided or else indicated
    by saying something like "Let [aevalR] be the smallest relation
    closed under the following rules..."). *)
(** TERSE: There is nothing very deep going on here:
      - rule name corresponds to a constructor name
      - above the line are premises
      - below the line is conclusion
      - _metavariables_ like [e1] and [n1] are implicitly universally
        quantified
      - the whole collection of rules is implicitly wrapped in an
        [Inductive] (sometimes we write this slightly more explicitly,
        as "...closed under these rules...")
*)

(** For example, [||] is the smallest relation closed under these
    rules:
[[[
                             -----------                               (E_ANum)
                             ANum n || n

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 || n1+n2

                               e1 || n1
                               e2 || n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 || n1-n2

                               e1 || n1
                               e2 || n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 || n1*n2
]]]
*)
(* LATER: This should be clearer about the use of inference rules to
   specify inductive definitions.  There should also be a note here
   remarking that inference rule notation is used in other contexts --
   to express quantified implications in statements of theorems,
   etc.. *)

(* QUIZ *)
(** Here, again, is the Coq definition of the [beval] function:
[[
  Fixpoint beval (e : bexp) : bool :=
    match e with
    | BTrue       => true
    | BFalse      => false
    | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
    | BLe a1 a2   => ble_nat (aeval a1) (aeval a2)
    | BNot b1     => negb (beval b1)
    | BAnd b1 b2  => andb (beval b1) (beval b2)
    end.
]]
    Write out a corresponding definition of boolean evaluation as a
    relation (in inference rule notation). 

*)
(* /QUIZ *)

(* QUIZ *)
(** Answer to the above: 
[[[
                            -------------                             (E_BTrue)
                            BTrue || true

                           ---------------                           (E_BFalse)
                           BFalse || false

                               e1 || n1
                               e2 || n2
                          beq_nat n1 n2 = b
                          -----------------                             (E_BEq)
                            BEq e1 e2 || b

                               e1 || n1
                               e2 || n2
                      --------------------------                        (E_BLe)
                      BEq e1 e2 || ble_nat n1 n2

                               e1 || b1
                          ------------------                           (E_BNot)
                          BNot e1 || negb b1

                               e1 || b1
                               e2 || b2
                       ------------------------                        (E_BAnd)
                       BAnd e1 e2 || andb b1 b2

]]]
*)
(* /QUIZ *)
(* /HIDEFROMADVANCED *)

(* HIDEFROMADVANCED *)
(* ####################################################### *)
(** ** Equivalence of the Definitions *)

(** It is straightforward to prove that the relational and functional
    definitions of evaluation agree on all possible arithmetic
    expressions... *)

(* /HIDEFROMADVANCED *)
Theorem aeval_iff_aevalR : forall a n,
  (a || n) <-> aeval a = n.
(* FOLD *)
Proof.
 split.
 Case "->".
   intros H.
   aevalR_cases (induction H) SCase; simpl.
   SCase "E_ANum".
     reflexivity.
   SCase "E_APlus".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   SCase "E_AMinus".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   SCase "E_AMult".
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 Case "<-".
   generalize dependent n.
   aexp_cases (induction a) SCase;
      simpl; intros; subst.
   SCase "ANum".
     apply E_ANum.
   SCase "APlus".
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMinus".
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   SCase "AMult".
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.
(* /FOLD *)
(* SOONER: Is this a good place to talk about folded proofs in the HTML? *)
(* HIDEFROMADVANCED *)

(** We can make the proof quite a bit shorter by making more
    use of tacticals... *)

Theorem aeval_iff_aevalR' : forall a n,
  (a || n) <-> aeval a = n.
Proof.
  (* WORKINCLASS *)
  split.
  Case "->".
    intros H; induction H; subst; reflexivity.
  Case "<-".
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.
(* /WORKINCLASS *)

(* /HIDEFROMADVANCED *)
(* FULL *)
(* EX3  (bevalR) *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)

(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
Inductive bevalR:
(* SOLUTION *)
   bexp -> bool -> Prop :=
  | BETrue : bevalR BTrue true
  | BEFalse : bevalR BFalse false
  | BEEq : forall  a1 a2 n1 n2,
    aevalR  a1 n1 ->
    aevalR  a2 n2 ->
    bevalR  (BEq a1 a2) (beq_nat n1 n2)
  | BELe : forall  a1 a2 n1 n2,
    aevalR  a1 n1 ->
    aevalR  a2 n2 ->
    bevalR  (BLe a1 a2) (ble_nat n1 n2)
  | BENot : forall  b1 tv1,
    bevalR  b1 tv1 ->
    bevalR  (BNot b1) (negb tv1)
  | BEAnd : forall  b1 b2 tv1 tv2,
    bevalR  b1 tv1 ->
    bevalR  b2 tv2 ->
    bevalR  (BAnd b1 b2) (andb tv1 tv2).

Tactic Notation "bevalR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BETrue" | Case_aux c "BEFalse" | Case_aux c "BEEq"
  | Case_aux c "BELe" | Case_aux c "BENot" | Case_aux c "BEAnd" ].

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split.
  Case "->".
   intros H.
   bevalR_cases (induction H) SCase; simpl; intros; subst;
      try (rewrite aeval_iff_aevalR in H, H0; rewrite H; rewrite H0); reflexivity.
  Case "<-".
   generalize dependent bv.
   bevalR_cases (induction b) SCase; simpl; intros; subst; constructor;
       try rewrite aeval_iff_aevalR; try apply IHb; try apply IHb1; try apply IHb2; try reflexivity.
Qed.

Lemma beval_iff_bevalR' : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof. (*using ordinary cut-and-paste rather than tacticals*)
split.
(* -> *)
intros H.
induction H. (*Nice case format follows*)
(*BTrue*)   simpl. reflexivity.
(*BFalse*)  simpl. reflexivity.
(*BEq*)     rewrite aeval_iff_aevalR in H, H0. simpl. subst. reflexivity.
(*BLe*)     rewrite aeval_iff_aevalR in H, H0. simpl. subst. reflexivity.
(*BNot*)    simpl. subst. reflexivity.
(*BAnd*)    simpl. subst. reflexivity. 
(* <- *)
intros. 
subst. (* use H now*)
induction b.
(*BTrue*)   simpl. constructor.
(*BFalse*)  simpl. constructor.
(*BEq*)     simpl. constructor. (*cont*)
            apply aeval_iff_aevalR. reflexivity.
            apply aeval_iff_aevalR. reflexivity.
(*BLe*)     simpl. constructor. (*cont*)
            apply aeval_iff_aevalR. reflexivity.
            apply aeval_iff_aevalR. reflexivity.
(*BNot*)    simpl. constructor. apply IHb.
(*BAnd*)    simpl. constructor. apply IHb1. apply IHb2.
Qed.  



(* /SOLUTION *)
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(** [] *)
(* /FULL *)
(* HIDEFROMHTML *)
End AExp.
(* /HIDEFROMHTML *)
(* HIDEFROMADVANCED *)

(* ####################################################### *)
(** ** Computational vs. Relational Definitions *)

(** For the definitions of evaluation for arithmetic and boolean
    expressions, the choice of whether to use functional or relational
    definitions is mainly a matter of taste.  In general, Coq has
    somewhat better support for working with relations.  On the other
    hand, in some sense function definitions carry more information,
    because functions are necessarily deterministic and defined on all
    arguments; for a relation we have to show these properties
    explicitly if we need them. Functions also take advantage of Coq's
    computations mechanism.

    However, there are circumstances where relational definitions of
    evaluation are preferable to functional ones.  *)

(* TERSE: HIDEFROMHTML *)
Module aevalR_division.

(* TERSE: /HIDEFROMHTML *)
(** For example, suppose that we wanted to extend the arithmetic
    operations by considering also a division operation:*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.   (* <--- new *)

(** Extending the definition of [aeval] to handle this new operation
    would not be straightforward (what should we return as the result
    of [ADiv (ANum 5) (ANum 0)]?).  But extending [aevalR] is
    straightforward. *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (APlus a1 a2) || (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)
  | E_ADiv :  forall (a1 a2: aexp) (n1 n2 n3: nat),
      (a1 || n1) -> (a2 || n2) -> (mult n2 n3 = n1) -> (ADiv a1 a2) || n3

where "a '||' n" := (aevalR a n) : type_scope.

(* TERSE: HIDEFROMHTML *)
End aevalR_division.
(* TERSE: /HIDEFROMHTML *) 
(* TERSE: HIDEFROMHTML *)
Module aevalR_extended.

(* TERSE: /HIDEFROMHTML *) 
(** Suppose, instead, that we want to extend the arithmetic operations
    by a nondeterministic number generator [any]:*)

Inductive aexp : Type :=
  | AAny  : aexp                   (* <--- NEW *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

(** Again, extending [aeval] would be tricky (because evaluation is
    _not_ a deterministic function from expressions to numbers), but
    extending [aevalR] is no problem: *)

Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      AAny || n                 (* <--- new *)
  | E_ANum : forall (n:nat),
      (ANum n) || n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (APlus a1 a2) || (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMinus a1 a2) || (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 || n1) -> (a2 || n2) -> (AMult a1 a2) || (n1 * n2)

where "a '||' n" := (aevalR a n) : type_scope.

(* TERSE: HIDEFROMHTML *)
End aevalR_extended.

(* TERSE: /HIDEFROMHTML *) 


(* ####################################################### *)
(** * Expressions With Variables *)

(* HIDEFROMADVANCED *)
(** Let's turn our attention back to defining Imp.  The next thing we
    need to do is to enrich our arithmetic and boolean expressions
    with variables.  To keep things simple, we'll assume that all
    variables are global and that they only hold numbers. *)

(* /HIDEFROMADVANCED *)
(* ##################################################### *)
(** ** Identifiers *)

(* HIDEFROMADVANCED *)
(** To begin, we'll need to formalize _identifiers_ such as program
    variables.  We could use strings for this -- or, in a real
    compiler, fancier structures like pointers into a symbol table.
    But for simplicity let's just use natural numbers as identifiers. *)

(* TERSE: HIDEFROMHTML *)
(** (We hide this section in a module because these definitions are
    actually in [SfLib], but we want to repeat them here so that we
    can explain them.) *)

Module Id.

(* TERSE: /HIDEFROMHTML *)
(* /HIDEFROMADVANCED *)
(** We define a new inductive datatype [Id] so that we won't confuse
    identifiers and numbers. *)

Inductive id : Type :=
  Id : nat -> id.

Definition beq_id x1 x2 :=
  match (x1, x2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

(* HIDEFROMADVANCED *)
(** FULL: After we "wrap" numbers as identifiers in this way, it is
    convenient to recapitulate a few properties of numbers as
    analogous properties of identifiers, so that we can work with
    identifiers in definitions and proofs abstractly, without
    unwrapping them to expose the underlying numbers.  Since all we
    need to know about identifiers is whether they are the same or
    different, just a few basic facts are all we need. *)
(* HIDE: old TERSE: A few useful facts about identifiers... *)

(* FULL *)

Theorem beq_id_refl : forall x,
  true = beq_id x x.
Proof.
  intros. destruct x.
  apply beq_nat_refl.  Qed.

(* EX1? (beq_id_eq) *)
(** For this and the following exercises, do not use induction, but
    rather apply similar results already proved for natural numbers.
    Some of the tactics mentioned above may prove useful. *)

Theorem beq_id_eq : forall x1 x2,
  true = beq_id x1 x2 -> x1 = x2.
Proof.
  (* ADMITTED *)
  intros x1 x2 H.
  destruct x1. destruct x2.
  apply beq_nat_eq in H. subst.
  reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX1? (beq_id_false_not_eq) *)
Theorem beq_id_false_not_eq : forall x1 x2,
  beq_id x1 x2 = false -> x1 <> x2.
Proof.
  (* ADMITTED *)
  intros x1 x2 H.
  destruct x1. destruct x2.
  apply beq_nat_false in H.
  intros C. apply H. inversion C. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX1? (not_eq_beq_id_false) *)
Theorem not_eq_beq_id_false : forall x1 x2,
  x1 <> x2 -> beq_id x1 x2 = false.
Proof.
  (* ADMITTED *)
  intros x1 x2 H.
  destruct x1. destruct x2.
  assert (n <> n0).
    intros C. subst. apply H. reflexivity.
  apply not_eq_beq_false. assumption.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX1? (beq_id_sym) *)
Theorem beq_id_sym: forall x1 x2,
  beq_id x1 x2 = beq_id x2 x1.
Proof.
  (* ADMITTED *)
  intros x1 x2. destruct x1. destruct x2. apply beq_nat_sym. Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* TERSE: HIDEFROMHTML *)
End Id.

(* TERSE: /HIDEFROMHTML *)
(* /HIDEFROMADVANCED *)
(* ####################################################### *)
(** ** States *)

(* SOONER: This section needs a little preface talking about "what is
   the meaning of an expression with variables?"... *)
(** LATER: (Note copied from Equiv.v right before the assign_aequiv
   exercise): Some or all of this discussion should really happen when
   states are introduced in Imp.v, and the whole idea of treating
   states as an ADT should be raised there. *)
(* SOONER: One potential confusion arises from the word "state" -- it
   could be interpreted by students as "the state of a (single)
   variable."  We need to emphasize that it is synonymous with
   "memory" as in the WHOLE memory. *)
(* SOONER: Explicitly remind people of the connection with "override"
   in an earlier chapter.  (Indeed, we might want to rename it!
   "override" is easier to grok anyway, avoiding the gratuitious
   suggestion of meta-level mutation.) *)

(** A _state_ represents the current values of all the variables at
    some point in the execution of a program. *)
(** FULL: For simplicity (to avoid dealing with partial functions), we
    let the state be defined for _all_ variables, even though any
    given program is only going to mention a finite number of them. *)

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.  
(* Like most prog langs, nats initialize to 0. *)

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if beq_id x x' then n else st x'.

(* HIDE: BAY, 23 Feb 2011: We tried making state more general,

   state X := id -> option X

   so it could be reused generically later.  However, this ends up
   complicating some of the proofs quite a bit, and not in an
   interesting way.  For example, the factorial invariant would need
   to be something like exists m, exists n, st X = m /\ st Y = n /\
   ... which is a pain to deal with. This file jumps up the complexity
   quite a bit as it is, so we decided it's better to leave the simple
   version here, and go for more generality later on in the course.
*)

(** For proofs involving states, we'll need several simple properties
    of [update]. *)

(* EX1 (update_eq) *)
Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
  (* ADMITTED *)
  intros n x st.
  unfold update.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.
(* /ADMITTED *)
(** [] *)

(* EX1 (update_neq) *)
Theorem update_neq : forall x2 x1 n st,
  beq_id x2 x1 = false ->
  (update st x2 n) x1 = (st x1).
Proof.
  (* ADMITTED *)
  intros x2 x1 n st Hneq.
  unfold update.
  rewrite -> Hneq.
  reflexivity. Qed.
(* /ADMITTED *)
(** [] *)

(* FULL *)
(* EX1 (update_example) *)
(** Before starting to play with tactics, make sure you understand
    exactly what the theorem is saying! *)

Theorem update_example : forall (n:nat),
  (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  (* ADMITTED *)
  reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* EX1! (update_shadow) *)
Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
   (update  (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
  (* ADMITTED *)
  intros n1 n2 x1 x2 st.
  unfold update.
  destruct (beq_id x2 x1); reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX2 (update_same) *)
Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  (* ADMITTED *)
  intros n1 x1 x2 st Heq.
  unfold update. subst.
  remember (beq_id x1 x2) as b.
  destruct b.
  Case "true".
    apply beq_id_eq in Heqb. subst. reflexivity.
  Case "false".
    reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (update_permute) *)
Theorem update_permute : forall n1 n2 x1 x2 x3 st,
  beq_id x2 x1 = false ->
  (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
  (* ADMITTED *)
  intros n1 n2 x1 x2 x3 st H.
  unfold update.
  remember (beq_id x1 x3) as b13.
  remember (beq_id x2 x3) as b23.
  apply beq_id_false_not_eq in H.
  destruct b13; try reflexivity.
  Case "true".
    destruct b23; try reflexivity.
    SCase "true".
      apply beq_id_eq in Heqb13.
      apply beq_id_eq in Heqb23.
      subst. apply ex_falso_quodlibet. apply H. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* Try extensionality on previous exercise. I thot there was 
something fishy about all this tedium for update. *)

(* ################################################### *)
(** ** Syntax  *)

(** We can add variables to the arithmetic expressions we had before by
    simply adding one more constructor: *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp                (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(* LATER: The explanation here is clunky. *)
(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)
(* HIDE: We usually don't use x as a "bare identifier" in examples --
   it is normally wrapped in an AId constructor.  If this were
   _always_ the case, then it would make more sense to define the
   notation [x] to mean [AId (Id 0)].  But there are just a few
   counterexamples.  Maybe we could define [xx] to mean [AId (Id 0)],
   or some such?  But it's still awkward. *)

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

(** FULL: (This convention for naming program variables ([X], [Y],
    [Z]) clashes a bit with our earlier use of uppercase letters for
    types.  Since we're not using polymorphism heavily in this part of
    the course, this overloading should not cause confusion.) *)

(** The definition of [bexp]s is the same as before (using the new
    [aexp]s): *)

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd" ].

(* ################################################### *)
(** ** Evaluation  *)

(** FULL: The arith and boolean evaluators can be extended to handle
    variables in the obvious way: *)
(** TERSE: Add an [st] parameter to both evaluation functions. *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                        (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

(* FULL *)
Example aexp1 :
  aeval (update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval (update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = true.
Proof. reflexivity. Qed.
(* /FULL *)

Eval simpl in aeval (update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2))).

(* ####################################################### *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (often called _statements_). *)

(* ################################################### *)
(** ** Syntax *)

(* HIDEFROMADVANCED *)
(** Informally, commands [c] are described by the following BNF
    grammar:
[[
     c ::= SKIP
         | x ::= a
         | c ; c
         | WHILE b DO c END
         | IFB b THEN c ELSE c FI
]]
    For example, here's the factorial function in Imp.
[[
     Z ::= X;
     Y ::= 1;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;
       Z ::= Z - 1
     END
]]
   When this command terminates, the variable [Y] will contain the
   factorial of the initial value of [X].
*)

(** FULL: Here is the formal definition of the syntax of commands: *)

(* /HIDEFROMADVANCED *)
Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

(** As usual, we can use a few [Notation] declarations to make things
    more readable.  We need to be a bit careful to avoid conflicts
    with Coq's built-in notations, so we'll keep this light -- in
    particular, we won't introduce any notations for [aexps] and
    [bexps] to avoid confusion with the numerical and boolean
    operators we've already defined.  We use the keyword [IFB] for
    conditionals instead of [IF], for similar reasons. *)

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** For example, here is the factorial function again, written as a
    formal definition to Coq: *)

Definition fact_in_coq : com :=
  Z ::= AId X;
  Y ::= ANum 1;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);
    Z ::= AMinus (AId Z) (ANum 1)
  END.

(* HIDEFROMADVANCED *)
(* ####################################################### *)
(** ** Examples *)

(** Assignment: *)

Definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2)).

Definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y)).

Definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;
  X ::= AMinus (AId X) (ANum 1).

(** Loops: *)

Definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;
  Z ::= ANum 5 ;
  subtract_slowly.

(** An infinite loop: *)

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

(* HIDE *)
(** Exponentiation: *)
Definition exp_body : com :=
  Z ::= AMult (AId Z) (AId X) ;
  Y ::= AMinus (AId Y) (ANum 1).
Definition pexp : com :=
  WHILE BNot (BEq (AId Y) (ANum 0)) DO
    exp_body
  END.
(** (Note that [pexp] should be run in a state where [Z] is [1].) *)
(* /HIDE *)

(* /HIDEFROMADVANCED *)
(* ################################################################ *)
(** * Evaluation *)

(** Next we need to define what it means to evaluate an Imp command.
    The fact that [WHILE] loops don't necessarily terminate makes defining
    an evaluation function tricky... *)

(* #################################### *)
(** ** Evaluation as a Function (Failed Attempt) *)

(** Here's an attempt at defining an evaluation function for commands,
    omitting the [WHILE] case. *)

Fixpoint ceval_fun_no_while (st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        update st x (aeval st a1)
    | c1 ; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* bogus *)
  end.

(** In a traditional functional programming language like ML or
    Haskell we could write the [WHILE] case as follows:
<<
  Fixpoint ceval_fun (st : state) (c : com) : state :=
    match c with
      ...
      | WHILE b DO c END =>
          if (beval st b1)
            then ceval_fun st (c1; WHILE b DO c END)
            else st
    end.
>>
    Coq doesn't accept such a definition ("Error: Cannot guess
    decreasing argument of fix") because the function we want to
    define is not guaranteed to terminate. Indeed, it doesn't always
    terminate: for example, the full version of the [ceval_fun]
    function applied to the [loop] program above would never
    terminate. Since Coq is not just a functional programming
    language, but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is
    an (invalid!) Coq program showing what would go wrong if Coq
    allowed non-terminating recursive functions:
<<
     Fixpoint loop_false (n : nat) : False := loop_false n.
>>
    That is, propositions like [False] would become provable
    (e.g. [loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs, the full version
    of [ceval_fun] cannot be written in Coq -- at least not without
    additional tricks (see chapter [ImpCEvalFun] if curious). *)
(* LATER: Perhaps that discussion should be moved to -- or previewed
   in -- Logic.v? *)

(* #################################### *)
(** ** Evaluation as a Relation *)

(** Here's a better way: we define [ceval] as a _relation_ rather than
    a _function_ -- i.e., we define it in [Prop] instead of [Type], as
    we did for [aevalR] above. *)

(* HIDE: (old text) "Besides freeing us from the
    silliness of passing around step indices all over the place" *)
(* HIDEFROMADVANCED *)
(** This is an important change.  Besides freeing us from the awkward
    workarounds that would be needed to define evaluation as a
    function, it gives us a lot more flexibility in the definition.
    For example, if we added concurrency features to the language,
    we'd want the definition of evaluation to be non-deterministic --
    i.e., not only would it not be total, it would not even be a
    partial function! *)

(* /HIDEFROMADVANCED *)
(** We'll use the notation [c / st || st'] for our [ceval] relation:
    [c / st || st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']".
[[[
                           ----------------                            (E_Skip)
                           SKIP / st || st

                           aeval st a1 = n
                   --------------------------------                     (E_Ass)
                   x := a1 / st || (update st x n)

                           c1 / st || st'
                          c2 / st' || st''
                         -------------------                            (E_Seq)
                         c1;c2 / st || st''

                          beval st b1 = true
                           c1 / st || st'
                -------------------------------------                (E_IfTrue)
                IF b1 THEN c1 ELSE c2 FI / st || st'

                         beval st b1 = false
                           c2 / st || st'
                -------------------------------------               (E_IfFalse)
                IF b1 THEN c1 ELSE c2 FI / st || st'

                         beval st b1 = false
                    ------------------------------                 (E_WhileEnd)
                    WHILE b DO c END / st || st

                          beval st b1 = true
                           c / st || st'
                  WHILE b DO c END / st' || st''
                  ---------------------------------               (E_WhileLoop)
                    WHILE b DO c END / st || st''
]]]
*)

(* HIDE: APT: Investigate rewriting these to use equality hypotheses
   rather than repeated variables in the conclusion.  For example:

      E_Skip : forall st st', st = st' -> SKIP /st == st'.

   This makes the constructors easier to apply, and allows us to "swap
   in" an equivalence in place of equality.

  BAY: It sounds nice, but I tried this (23 Feb 2011) and didn't
    really find any benefit. The only difference seemed to be that it
    made quite a few proofs a tiny bit more annoying, due to the need
    for an extra 'reflexivity' or 'subst' or what have you. *)

(** FULL: Here is the formal definition.  (Make sure you understand
    how it corresponds to the inference rules.) *)

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st || (update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ; c2) / st || st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st || st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st || st
  | E_WhileLoop : forall st st' st'' b c,
      beval st b = true ->
      c / st || st' ->
      (WHILE b DO c END) / st' || st'' ->
      (WHILE b DO c END) / st || st''

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

(* HIDEFROMADVANCED *)
(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example ceval_example1:
    (X ::= ANum 2;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   || (update (update empty_state X 2) Z 4).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (update empty_state X 2).
  Case "assignment command".
    apply E_Ass. reflexivity.
  Case "if command".
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.  Qed.

(* /HIDEFROMADVANCED *)
(* FULL *)
(* EX2 (ceval_example2) *)
Example ceval_example2:
    (X ::= ANum 0; Y ::= ANum 1; Z ::= ANum 2) / empty_state ||
    (update (update (update empty_state X 0) Y 1) Z 2).
Proof.
  (* ADMITTED *)
  apply E_Seq with (update empty_state X 0).
  Case "first assignment command".
    apply E_Ass. reflexivity.
  Case "second ;".
    apply E_Seq with (update (update empty_state X 0) Y 1).
    SCase "second assignment command".
      apply E_Ass. reflexivity.
    SCase "third assignment".
      apply E_Ass. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX3A (pup_to_n) *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for X = 2
   (this latter part is trickier than you might expect). *)
(* HIDE: CH: This is hard to solve without eapply.
   Decreased number of iterations to 2. Made the whole thing optional. *)

Definition pup_to_n : com :=
  (* ADMIT *)
  Y ::= (ANum 0);
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Y ::= APlus (AId Y) (AId X) ;
    X ::= AMinus (AId X) (ANum 1)
  END.
(* /ADMIT *)

Theorem pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ||
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
(* HIDE: Tesult is the same as (update (update empty_state X 0) Y 3)
   if one admits functional extensionality *)
Proof.
  (* ADMITTED *)
  unfold pup_to_n.
  apply E_Seq with (update (update empty_state X 2) Y 0).
  Case "assignment command".
    apply E_Ass. reflexivity.
  Case "while command".
    apply E_WhileLoop with
      (update (update (update (update empty_state X 2) Y 0) Y 2) X 1).
      reflexivity.
    SCase "first round".
      apply E_Seq with (update (update (update empty_state X 2) Y 0) Y 2).
      apply E_Ass. reflexivity.
      apply E_Ass. reflexivity.
    SCase "the other rounds".
      eapply E_WhileLoop. reflexivity.
      SSCase "second round".
        eapply E_Seq.
        apply E_Ass. reflexivity.
        apply E_Ass. reflexivity.
      SSCase "no more rounds".
        simpl. rewrite update_eq.
        apply E_WhileEnd. reflexivity. Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)

(* QUIZ *)
(** Is the following proposition provable?
[[
      forall c st st',     
        (SKIP ; c) / st || st' ->
        c / st || st'
]]
    (1) Yes

    (2) No

    (3) Not sure

*)
(* HIDE *)
Check (forall c st st',     
          (SKIP ; c) / st || st' ->
          c / st || st').


Lemma quiz3: forall c st st',     
          (SKIP ; c) / st || st' ->
          c / st || st' .
Proof. intros. inversion H. inversion H2. subst. assumption. Qed.

(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** Is the following proposition provable?
[[
      forall c1 c2 st st',     
          (c1;c2) / st || st' ->
          c1 / st || st ->
          c2 / st || st'
]]
    (1) Yes

    (2) No

    (3) Not sure

*)
(* HIDE *)
Check (forall c1 c2 st st',     
          (c1;c2) / st || st' ->
          c1 / st || st ->
          c2 / st || st').

(* Lemma quiz4 is below after ceval_deterministic. *)



(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** Is the following proposition provable?
[[
      forall b c st st',     
          (IFB b THEN c ELSE c FI) / st || st' ->
          c / st || st'
]]
    (1) Yes

    (2) No

    (3) Not sure

*)
(* HIDE *)
Check (forall b c st st',     
          (IFB b THEN c ELSE c FI) / st || st' ->
          c / st || st').
(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** Is the following proposition provable?
[[
      forall b,     
         (forall st, beval st b = true) ->
         forall c st,
           ~(exists st', (WHILE b DO c END) / st || st')
]]
    (1) Yes

    (2) No

    (3) Not sure

*)
(* HIDE *)
Check (forall b,     
         (forall st, beval st b = true) ->
            forall c st,
              ~(exists st', (WHILE b DO c END) / st || st')).
(* /HIDE *)
(* /QUIZ *)
(* QUIZ *)
(** Is the following proposition provable?
[[
      forall b c st,
         ~(exists st', (WHILE b DO c END) / st || st') ->
         forall st'', beval st'' b = true
]]
    (1) Yes

    (2) No

    (3) Not sure

*)
(* HIDE *)
Check (forall b c st,
         ~(exists st', (WHILE b DO c END) / st || st') ->
         forall st'', beval st'' b = true).
(* /HIDE *)
(* /QUIZ *)

(* HIDEFROMADVANCED *)
(* ####################################################### *)
(** ** Determinism of Evaluation *)

(* LATER: Maybe this should go at the end of the file in a section
   marked optional?  Not everybody will want to spend time on it. *)
(* FULL *)
(** Changing from a computational to a relational definition of
    evaluation is a good move because it allows us to escape from the
    artificial requirement (imposed by Coq's restrictions on
    [Fixpoint] definitions) that evaluation should be a total
    function.  But it also raises a question: Is the second definition
    of evaluation actually a partial function?  That is, is it
    possible that, beginning from the same state [st], we could
    evaluate some command [c] in different ways to reach two different
    output states [st'] and [st'']?

    In fact, this cannot happen: [ceval] is a partial function.
    Here's the proof: *)
(* /FULL *)
(* SOONER: Informal proof needed! *)

Theorem ceval_deterministic: forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
(* FOLD *)
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case;
           intros st2 E2; inversion E2; subst.
  Case "E_Skip". reflexivity.
  Case "E_Ass". reflexivity.
  Case "E_Seq".
    assert (st' = st'0) as EQ1.
      SCase "Proof of assertion". apply IHE1_1; assumption.
    subst st'0.
    apply IHE1_2. assumption.
  Case "E_IfTrue".
    SCase "b1 evaluates to true".
      apply IHE1. assumption.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H5. inversion H5.
  Case "E_IfFalse".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H5. inversion H5.
    SCase "b1 evaluates to false".
      apply IHE1. assumption.
  Case "E_WhileEnd".
    SCase "b1 evaluates to true".
      reflexivity.
    SCase "b1 evaluates to false (contradiction)".
      rewrite H in H2. inversion H2.
  Case "E_WhileLoop".
    SCase "b1 evaluates to true (contradiction)".
      rewrite H in H4. inversion H4.
    SCase "b1 evaluates to false".
      assert (st' = st'0) as EQ1.
        SSCase "Proof of assertion". apply IHE1_1; assumption.
      subst st'0.
      apply IHE1_2. assumption.  Qed.
(* /FOLD *)

Lemma quiz4: forall c1 c2 st st',     
          (c1;c2) / st || st' ->
          c1 / st || st ->
          c2 / st || st'.
Proof. intros.  inversion H. subst. 
assert (st = st'0) as Hd. 
apply ceval_deterministic with (c:=c1) (st:=st) (st1:=st) (st2:=st'0).
assumption. assumption. subst. assumption. Qed.
 
Lemma quiz5: forall b c st st',     
          (IFB b THEN c ELSE c FI) / st || st' ->
          c / st || st'.
Proof. intros. inversion H. assumption. assumption. Qed.

(* ####################################################### *)
(** * Reasoning About Imp Programs *)

(* SOONER: This section doesn't seem very useful -- to anybody!  It
   takes too much time to go through it in class, and even for
   advanced students it's too low-level and grubby to be a very
   convincing motivation for what follows -- i.e., to feel motivated
   by its grubbiness, you have to understand it, but this takes more
   time than it's worth.  Better to cut the whole rest of the
   file (except the further exercises at the very end), or at least
   make it optional. *)
(** We'll get much deeper into systematic techniques for reasoning
    about Imp programs in the following chapters, but we can do quite
    a bit just working with the bare definitions. *)

(* FULL: This section explores some examples. *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st || st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  (* Inverting Heval essentially forces Coq to expand one
     step of the ceval computation - in this case revealing
     that st' must be st extended with the new value of X,
     since plus2 is an assignment *)
  inversion Heval. subst. clear Heval. simpl.
  apply update_eq.  Qed.

(* FULL *)
(* EX3! (XtimesYinZ_spec) *)
(** State and prove a specification of [XtimesYinZ]. *)

(* SOLUTION *)
(* Here is a specification in the style of plus2_spec *)
Theorem XtimesYinZ_spec1 : forall st nx ny st',
  st X = nx ->
  st Y = ny ->
  XtimesYinZ / st || st' ->
  st' Z = mult nx ny.
Proof.
  intros st nx ny st' HX HY Heval.
  (* Start by inverting the assignment *)
  inversion Heval. subst.
  apply update_eq.  Qed.

(* Though perhaps a cleaner specification would be: *)
Theorem XtimesYinZ_spec : forall st,
  XtimesYinZ / st || (update st Z (st X * st Y)).
Proof. intros. apply E_Ass. reflexivity. Qed.

(* A less informative specification would be ... *)
Theorem XtimesYinZ_spec2 : forall st, exists st', XtimesYinZ / st || st'.
Proof.
  intros. exists (update st Z (st X * st Y)).
  apply E_Ass. reflexivity.
Qed.
(* /SOLUTION *)
(** [] *)

(* EX3! (loop_never_stops) *)
Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef.
  (* Proceed by induction on the assumed derivation showing that
     [loopdef] terminates.  Most of the cases are immediately
     contradictory (and so can be solved in one step with
     [inversion]). *)
  (* ADMITTED *)
  ceval_cases (induction contra) Case; try (inversion Heqloopdef).
    Case "E_WhileEnd".
      rewrite -> H1 in H. inversion H.
    Case "E_WhileLoop".
      apply IHcontra2. subst. reflexivity.  Qed.
(* /ADMITTED *)
(** [] *)

(* EX3 (no_whilesR) *)
(** Consider the definition of the [no_whiles] property below: *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP       => true
  | _ ::= _    => true
  | c1 ; c2  => andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI => andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  => false
  end.

(** This property yields [true] just on programs that
    have no while loops.  Using [Inductive], write a property
    [no_whilesR] such that [no_whilesR c] is provable exactly when [c]
    is a program with no while loops.  Then prove its equivalence
    with [no_whiles]. *)

Inductive no_whilesR: com -> Prop :=
 (* SOLUTION *)
 | nw_Skip: no_whilesR SKIP
 | nw_Ass: forall x ae, no_whilesR (x ::= ae)
 | nw_Seq: forall c1 c2, no_whilesR c1 ->
                            no_whilesR c2 ->
                            no_whilesR (c1 ; c2)
 | nw_If: forall be c1 c2,  no_whilesR c1 ->
                            no_whilesR c2 ->
                            no_whilesR (IFB be THEN c1 ELSE c2 FI).

Tactic Notation "no_whilesR_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "nw_Skip" | Case_aux c "nw_Ass"
  | Case_aux c "nw_Seq" | Case_aux c "nw_If" ]
(* /SOLUTION *)
  .

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  (* ADMITTED *)
   intros; split; [  Case "->" | Case "<-" ].
  Case "->".
   com_cases (induction c) SCase; intro Hc;
     try (simpl in Hc; rewrite andb_true_iff in Hc;
       inversion Hc as [Hc1 Hc2]);
     try constructor;
     try (apply IHc1; assumption); try (apply IHc2; assumption).
   SCase "WHILE".  inversion Hc.
  Case "<-".
    intro H. no_whilesR_cases (induction H) SCase; simpl;
      try reflexivity;
      try (rewrite IHno_whilesR1; rewrite IHno_whilesR2; reflexivity).
  Qed.
  (* /ADMITTED *)
(** [] *)

(* EX4 (no_whiles_terminating) *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem that says this. *)
(** FULL: (Use either [no_whiles] or [no_whilesR], as you prefer.) *)

(* SOLUTION *)
(* Here is a solution by induction on no_whilesR *)
Theorem no_whiles_terminating : forall c st,
  no_whilesR c ->
  exists st',
  c / st || st'.
Proof.
  intros c st H. generalize dependent st.
  no_whilesR_cases (induction H) Case; intros; simpl.
  Case "nw_Skip". exists st. constructor.
  Case "nw_Ass". exists (update st x (aeval st ae)).
    constructor. reflexivity.
  Case "nw_Seq".
    destruct (IHno_whilesR1 st) as [st' IH'].
    destruct (IHno_whilesR2 st') as [st'' IH''].
    exists st''. apply E_Seq with st'; assumption.
  Case "nw_If".
    remember (beval st be) as bv. destruct bv.
    SCase "bv = true".
      destruct (IHno_whilesR1 st) as [st' IH'].
      exists st'. apply E_IfTrue. rewrite Heqbv. reflexivity. assumption.
    SCase "bv = false".
      destruct (IHno_whilesR2 st) as [st' IH'].
      exists st'. apply E_IfFalse. rewrite Heqbv. reflexivity. assumption.
Qed.

(* and here is an alternative solution by induction on no_whilesR *)
Theorem no_whiles_terminating' : forall c st1,
  no_whiles c = true ->
  exists st2, c / st1 || st2.
Proof.
  com_cases (induction c) Case; intros st1 Hb.

  Case "SKIP".
    exists st1. apply E_Skip.

  Case "::=".
    exists (update st1 i (aeval st1 a)). apply E_Ass. reflexivity.

  Case ";".
    simpl in Hb.
    assert (Hb1 := andb_true_elim1 _ _ Hb).
    assert (Hb2 := andb_true_elim2 _ _ Hb). clear Hb.
    apply (IHc1 st1) in Hb1. inversion Hb1 as [st1' ceH1].
    apply (IHc2 st1') in Hb2. inversion Hb2 as [st1'' ceH2].
    exists st1''.
    apply E_Seq with (st' := st1'); assumption.

  Case "IFB".
    simpl in Hb. remember (beval st1 b) as bv. destruct bv.
    SCase "E_IfTrue".
      apply andb_true_elim1 in Hb. apply (IHc1 st1) in Hb.
      inversion Hb as [st2 Hce1]. exists st2.
      apply E_IfTrue.
      SSSCase "b is true".
        rewrite <- Heqbv. reflexivity.
      SSSCase "true branch eval".
        assumption.
    SCase "E_IfFalse".
      apply andb_true_elim2 in Hb. apply (IHc2 st1) in Hb.
      inversion Hb as [st2 Hce2]. exists st2.
      apply E_IfFalse.
      SSSCase "b is false".
        rewrite <- Heqbv. reflexivity.
      SSSCase "false branch eval".
        assumption.

  Case "WHILE".
    inversion Hb.  Qed.
(* /SOLUTION *)
(** [] *)
(* /FULL *)

(* LATER: The following section always gets skipped over when I (BCP)
   teach the course, because there isn't time to go through all the
   details and we're going to see the right way to do the same thing
   in a later chapter.  I wouldn't mind reinstating it for the use of
   advanced / self-study readers if somebody wants to write some text
   to really explain it, but what's there is a bit too telegraphic, so
   I'm removing it for now. *)
(* HIDE *)
(* ####################################################### *)
(** * Case Study (Optional) *)

(** Recall the factorial program (broken up into smaller pieces this
    time, for convenience of proving things about it).  *)

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z) ;
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= AId X ;
  Y ::= ANum 1 ;
  fact_loop.

(** Here is an alternative "mathematical" definition of the factorial
    function: *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(** We would like to show that they agree -- if we start [fact_com] in
    a state where variable [X] contains some number [n], then it will
    terminate in a state where variable [Y] contains the factorial of
    [n].

    To show this, we rely on the critical idea of a _loop
    invariant_. *)

Definition fact_invariant (n:nat) (st:state) :=
  (st Y) * (real_fact (st Z)) = real_fact n.

(** We show that the body of the factorial loop preserves the invariant: *)

(* SOONER: Needs an informal proof! *)
Theorem fact_body_preserves_invariant: forall st st' n,
     fact_invariant n st ->
     st Z <> 0 ->
     fact_body / st || st' ->
     fact_invariant n st'.
(* FOLD *)
Proof.
  unfold fact_invariant, fact_body.
  intros st st' n Hm HZnz He.
  inversion He; subst; clear He.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  unfold update. simpl.
  (* Show that st Z = S z' for some z' *)
  destruct (st Z) as [| z'].
    apply ex_falso_quodlibet. apply HZnz. reflexivity.
  rewrite <- Hm. rewrite <- mult_assoc.
  replace (S z' - 1) with z' by omega.
  reflexivity.  Qed.
(* /FOLD *)

(** From this, we can show that the whole loop also preserves the
invariant: *)

Theorem fact_loop_preserves_invariant : forall st st' n,
     fact_invariant n st ->
     fact_loop / st || st' ->
     fact_invariant n st'.
(* FOLD *)
Proof.
  intros st st' n H Hce.
  remember fact_loop as c.
  ceval_cases (induction Hce) Case;
              inversion Heqc; subst; clear Heqc.
  Case "E_WhileEnd".
    (* trivial when the loop doesn't run... *)
    assumption.
  Case "E_WhileLoop".
    (* if the loop does run, we know that fact_body preserves
       fact_invariant -- we just need to assemble the pieces *)
    apply IHHce2.
      apply fact_body_preserves_invariant with st;
            try assumption.
      intros Contra. simpl in H0; subst.
      rewrite Contra in H0. inversion H0.
      reflexivity.  Qed.
(* /FOLD *)

(** Next, we show that, for any loop, if the loop terminates, then the
    condition guarding the loop must be false at the end: *)

Theorem guard_false_after_loop: forall b c st st',
     (WHILE b DO c END) / st || st' ->
     beval st' b = false.
(* FOLD *)
Proof.
  intros b c st st' Hce.
  remember (WHILE b DO c END) as cloop.
  ceval_cases (induction Hce) Case;
     inversion Heqcloop; subst; clear Heqcloop.
  Case "E_WhileEnd".
    assumption.
  Case "E_WhileLoop".
    apply IHHce2. reflexivity.  Qed.
(* /FOLD *)

(** Finally, we can patching it all together... *)

Theorem fact_com_correct : forall st st' n,
     st X = n ->
     fact_com / st || st' ->
     st' Y = real_fact n.
(* FOLD *)
Proof.
  intros st st' n HX Hce.
  inversion Hce; subst; clear Hce.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  inversion H1; subst; clear H1.
  rename st' into st''. simpl in H5.
  (* The invariant is true before the loop runs... *)
  remember (update (update st Z (st X)) Y 1) as st'.
  assert (fact_invariant (st X) st').
    subst. unfold fact_invariant, update. simpl. omega.
  (* ...so when the loop is done running, the invariant
     is maintained *)
  assert (fact_invariant (st X) st'').
    apply fact_loop_preserves_invariant with st'; assumption.
  unfold fact_invariant in H0.
  (* Finally, if the loop terminated, then Z is 0; so Y must be
     factorial of X *)
  apply guard_false_after_loop in H5. simpl in H5.
  destruct (st'' Z).
  Case "st'' Z = 0". simpl in H0. omega.
  Case "st'' Z > 0 (impossible)". inversion H5.
Qed.
(* /FOLD *)

(** One might wonder whether all this work with poking at states and
    unfolding definitions could be ameliorated with some more powerful
    lemmas and/or more uniform reasoning principles... Indeed, this is
    exactly the topic of the upcoming [Hoare] chapter! *)

(* FULL *)
(* EX4? (subtract_slowly_spec) *)
(** Prove a specification for subtract_slowly, using the above
    specification of [fact_com] and the invariant below as
    guides. *)

Definition ss_invariant (n:nat) (z:nat) (st:state) :=
  minus (st Z) (st X) = minus z n.

(* SOLUTION *)
Theorem ss_body_preserves_invariant : forall st n z st',
     ss_invariant n z st ->
     st X <> 0 ->
     subtract_slowly_body / st || st' ->
     ss_invariant n z st'.
Proof.
  unfold ss_invariant.
  intros st n z st' H Hnz He.
  inversion He; subst; clear He.
  inversion H2; subst; clear H2.
  inversion H5; subst; clear H5.
  unfold update. simpl.
  omega.   (* Interestingly, this is all we need here  -- although only after a perceptible delay! *)
Qed.

Theorem ss_preserves_invariant : forall st n z st',
     ss_invariant n z st ->
     subtract_slowly / st || st'  ->
     ss_invariant n z st'.
Proof.
  intros st n z st' H He.
  remember subtract_slowly as c.
  ceval_cases (induction He) Case; inversion Heqc; subst; clear Heqc.
  Case "E_WhileEnd".
    assumption.
  Case "E_WhileLoop".
    apply IHHe2; try reflexivity.
    apply ss_body_preserves_invariant with st; try assumption.
    intros Contra. simpl in H0. rewrite Contra in H0. inversion H0.  Qed.

Theorem ss_correct : forall st n z st',
     st X = n ->
     st Z = z ->
     subtract_slowly / st || st' ->
     st' Z = minus z n.
Proof.
  intros st n z st' HX HZ He.
  assert (ss_invariant n z st).
    unfold ss_invariant.
    subst.
    reflexivity.
  assert (ss_invariant n z st').
    apply ss_preserves_invariant with st; assumption.
  unfold ss_invariant in H0.
  apply guard_false_after_loop in He. simpl in He.
  destruct (st' X).
  Case "st' X = 0". omega.
  Case "st' X > 0 (impossible)". inversion He.
Qed.
(* /SOLUTION *)
(** [] *)
(* /HIDE *)

(* FULL *)
(* ####################################################### *)
(** * Additional Exercises *)

(* EX3 (stack_compiler) *)
(** HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a stack. For instance, the expression
<<
   (2*3)+(3*(4-2))
>>
   would be entered as
<<
   2 3 * 3 4 2 - * +
>>
   and evaluated like this:
<<
  []            |    2 3 * 3 4 2 - * +
  [2]           |    3 * 3 4 2 - * +
  [3, 2]        |    * 3 4 2 - * +
  [6]           |    3 4 2 - * +
  [3, 6]        |    4 2 - * +
  [4, 3, 6]     |    2 - * +
  [2, 4, 3, 6]  |    - * +
  [2, 3, 6]     |    * +
  [6, 6]        |    +
  [12]          |
>>

  The task of this exercise is to write a small compiler that
  translates [aexp]s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad x]: Load the identifier [x] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract.
     - [SMult]:   Similar, but multiply. *)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(** Write a function to evaluate programs in the stack language. It
    takes as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and returns the stack after
    executing the program. Test your function on the examples below.

    Note that the specification leaves unspecified what to do when
    encountering an [SPlus], [SMinus], or [SMult] instruction if the
    stack contains less than two elements.  In a sense, it is
    immaterial what we do, since our compiler will never emit such a
    malformed program. *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
(* ADMIT *)
  match (prog, stack) with
  | (nil,             _           ) => stack
  | (SPush n::prog',  _           ) => s_execute st (n::stack) prog'
  | (SLoad x::prog',  _           ) => s_execute st (st x::stack) prog'
  | (SPlus::prog',    n::m::stack') => s_execute st ((m+n)::stack') prog'
  | (SMinus::prog',   n::m::stack') => s_execute st ((m-n)::stack') prog'
  | (SMult::prog',    n::m::stack') => s_execute st ((m*n)::stack') prog'
  | (_::prog',        _           ) => s_execute st stack prog'
                                       (* Bad state: skip *)
  end.
(* /ADMIT *)

Example s_execute1 :
     s_execute empty_state []
       [SPush 5, SPush 3, SPush 1, SMinus]
   = [2, 5].
(* ADMITTED *)
Proof. reflexivity. Qed.
(* /ADMITTED *)

Example s_execute2 :
     s_execute (update empty_state X 3) [3,4]
       [SPush 4, SLoad X, SMult, SPlus]
   = [15, 4].
(* ADMITTED *)
Proof. reflexivity. Qed.
(* /ADMITTED *)

(** Next, write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
(* ADMIT *)
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus a1 a2 => s_compile a1 ++ s_compile a2 ++ [SPlus]
  | AMinus a1 a2  => s_compile a1 ++ s_compile a2 ++ [SMinus]
  | AMult a1 a2 => s_compile a1 ++ s_compile a2 ++ [SMult]
  end.
(* /ADMIT *)

(** After you've defined [s_compile], uncomment the following to test
    that it works. *)

(* OPEN COMMENT WHEN HIDING SOLUTIONS *)
Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X, SPush 2, SLoad Y, SMult, SMinus].
Proof. reflexivity. Qed.
(* CLOSE COMMENT WHEN HIDING SOLUTIONS *)
(** [] *)

(* EX3A (stack_compiler_correct) *)
(** The task of this exercise is to prove the correctness of the
    calculator implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

(* QUIETSOLUTION *)
(* HIDE: Adam Chlipala's book has a slicker solution which does it all
   in a single induction... APT: Slicker, but arguably harder to
   understand. *)
Lemma execute_app : forall st p1 p2 stack,
    s_execute st stack (p1 ++ p2)
  = s_execute st (s_execute st stack p1) p2.
Proof.
  induction p1.
    Case "nil". simpl. reflexivity.
    Case "cons". destruct a; simpl;
      intros; destruct stack as  [ | x [ | y stack']];
      try rewrite IHp1; reflexivity.
Qed.

Lemma execute_eval_comm : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  induction e;
    try reflexivity ; (* Push, Load *)
    intros; simpl;   (* Plus, Minus, Mult *)
      repeat rewrite execute_app;
      rewrite IHe1; rewrite IHe2; simpl; reflexivity.
Qed.
(* /QUIETSOLUTION *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* ADMITTED *)
  intros. apply execute_eval_comm.
Qed.
(* /ADMITTED *)
(** [] *)
(* /FULL *)
(* /HIDEFROMADVANCED *)

(* FULL *)
(* EX5A (break_imp) *)
Module BreakImp.

(** Imperative languages such as C or Java often have a [break] or
    similar statement for interrupting the execution of loops. In this
    exercise we will consider how to add [break] to Imp.

    First, we need to enrich the language of commands with an
    additional case. *)

Inductive com : Type :=
  | CSkip : com
  | CBreak : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "BREAK" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** Next, we need to define the behavior of [BREAK].  Informally,
    whenever [BREAK] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop (if any) should terminate. If there aren't any
    enclosing loops, then the whole program simply terminates. The
    final state should be the same as the one in which the [BREAK]
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given [BREAK]. In those cases, [BREAK] should only
    terminate the _innermost_ loop where it occurs. Thus, after
    executing the following piece of code...
[[
   X ::= 0;
   Y ::= 1;
   WHILE 0 <> Y DO
     WHILE TRUE DO
       BREAK
     END;
     X ::= 1;
     Y ::= Y - 1
   END
]]
    ... the value of [X] should be [1], and not [0].

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [BREAK] statement: *)

Inductive status : Type :=
  | SContinue : status
  | SBreak : status.

Reserved Notation "c1 '/' st '||' s '/' st'"
                  (at level 40, st, s at level 39).

(** Intuitively, [c / st || s / st'] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that any surrounding loop (or the whole program) should exit
    immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[c / st || s / st']" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([c / st || s / st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [SKIP], then the state doesn't change, and
      execution of any enclosing loop can continue normally.

    - If the command is [BREAK], the state stays unchanged, but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [IF b THEN c1 ELSE c2 FI], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ; c2], we first execute
      [c1]. If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state should be the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal that was
      generated there.

    - Finally, for a loop of the form [WHILE b DO c END], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises. If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration. In either case, since [BREAK] only terminates the
      innermost loop, [WHILE] signals [SContinue]. *)

(** Based on the above description, complete the definition of the
    [ceval] relation. *)

Inductive ceval : com -> state -> status -> state -> Prop :=
  | E_Skip : forall st,
      CSkip / st || SContinue / st
  (* SOLUTION *)
  | E_Break : forall st,
      CBreak / st || SBreak / st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st || SContinue / (update st X n)
  | E_SeqContinue : forall c1 c2 st st' st'' s,
      c1 / st || SContinue / st' ->
      c2 / st' || s / st'' ->
      (c1 ; c2) / st || s / st''
  | E_SeqBreak : forall c1 c2 st st',
      c1 / st || SBreak / st' ->
      (c1 ; c2) / st || SBreak / st'
  | E_If : forall c1 c2 b st st' s,
      (if beval st b then c1 else c2) / st || s / st' ->
      (IFB b THEN c1 ELSE c2 FI) / st || s / st'
  | E_WhileEnd : forall c b st,
      beval st b = false ->
      (WHILE b DO c END) / st || SContinue / st
  | E_WhileContinue : forall c b st st' st'',
      beval st b = true ->
      c / st || SContinue / st' ->
      (WHILE b DO c END) / st' || SContinue / st'' ->
      (WHILE b DO c END) / st || SContinue / st''
  | E_WhileBreak : forall c b st st',
      beval st b = true ->
      c / st || SBreak / st' ->
      (WHILE b DO c END) / st || SContinue / st'
  (* /SOLUTION *)

  where "c1 '/' st '||' s '/' st'" := (ceval c1 st s st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip"
  (* SOLUTION *)
  | Case_aux c "E_Break" | Case_aux c "E_Ass"
  | Case_aux c "E_SeqContinue" | Case_aux c "E_SeqBreak"
  | Case_aux c "E_If"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileContinue"
  | Case_aux c "E_WhileBreak"
  (* /SOLUTION *)
  ].

(** Now the following properties of your definition of [ceval]: *)

Theorem break_ignore : forall c st st' s,
     (BREAK; c) / st || s / st' ->
     st = st'.
Proof.
  (* ADMITTED *)
  intros c st st' s H.
  inversion H; clear H; subst.
  inversion H2.
  inversion H5. subst. reflexivity.
Qed.
(* /ADMITTED *)

Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st || s / st' ->
  s = SContinue.
Proof.
  (* ADMITTED *)
  intros b c st st' s H. inversion H; reflexivity.
Qed.
(* /ADMITTED *)

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st || SBreak / st' ->
  (WHILE b DO c END) / st || SContinue / st'.
Proof.
  (* ADMITTED *)
  intros b c st st' H1 H2.
  apply E_WhileBreak; assumption.
Qed.
(* /ADMITTED *)

Theorem while_break_true : forall b c st st',
  (WHILE b DO c END) / st || SContinue / st' ->
  beval st' b = true ->
  exists st'', c / st'' || SBreak / st'.
Proof.
(* ADMITTED *)
  intros b c st st' H Hb.
  remember (WHILE b DO c END) as c'.
  ceval_cases (induction H) Case;
    inversion Heqc'; clear Heqc'; subst.
  Case "E_WhileEnd".
    rewrite Hb in H. inversion H.
  Case "E_WhileContinue".
    clear IHceval1.
    apply IHceval2. reflexivity. assumption.
  Case "E_WhileBreak".
    exists st. assumption.
Qed.
(* /ADMITTED *)

Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     c / st || s1 / st1  ->
     c / st || s2 / st2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* ADMITTED *)
  intros c st st1 st2 s1 s2 E1 E2.
  generalize dependent s2.
  generalize dependent st2.
  ceval_cases (induction E1) Case;
    intros st2 s2 E2;
    inversion E2; clear E2; subst;
(* SOONER: 
   BCP: And this proof could be better automated in general.
   AAA: The problem with this proof is that it is somewhat hard to automate
        without using [match], which we haven't told them about yet. Each
        branch needs hypotheses with different names. Furthermore, [apply]
        by itself doesn't quite work as well, because we need to substitute
        some values in order for the unification to work. This is what I was 
        able to do.
 *)
    try (rewrite H in H2; inversion H2);
    try (rewrite H in H5; inversion H5);
    try (apply IHE1_1 in H1; destruct H1 as [H11 H12]; try subst);
    try (apply IHE1_2 in H5; destruct H5 as [H51 H52]; try subst);
    try (apply IHE1_1 in H4; destruct H4 as [H41 H42]; inversion H42);
    try (apply IHE1 in H1; destruct H1 as [H11 H12]; try subst; inversion H12);
    try (apply IHE1 in H4; destruct H4 as [H41 H42]; try subst; inversion H42);
    try (apply IHE1_1 in H3; destruct H3 as [H31 H32]; try subst; inversion H32);
    try (apply IHE1_1 in H6; destruct H6 as [H61 H62]; try subst; inversion H62);
    try (apply IHE1_2 in H7; destruct H7 as [H71 H72]; try subst; inversion H72);
    try (apply IHE1 in H3; destruct H3 as [H31 H32]; try subst; inversion H32);
    try (apply IHE1 in H6; destruct H6 as [H61 H62]; try subst; inversion H62);
    try (split; reflexivity).
  Case "E_If".
    apply IHE1. assumption.
Qed.
(* /ADMITTED *)

End BreakImp.
(** [] *)

(* EX3? (short_circuit) *)
(** Most modern programming languages use a "short-circuit" evaluation
    rule for boolean [and]: to evaluate [BAnd b1 b2], first evaluate
    [b1].  If it evaluates to [false], then the entire [BAnd]
    expression evaluates to [false] immediately, without evaluating
    [b2].  Otherwise, [b2] is evaluated to determine the result of the
    [BAnd] expression.

    Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval]. *)

(* SOLUTION *)
Fixpoint beval_sc (st : state) (e : bexp) : bool :=
  match e with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => ble_nat (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval_sc st b1)
  | BAnd b1 b2  => let eb1 := beval_sc st b1 in
      match eb1 with
      | false => false
      | true  => (beval_sc st b2)
      end
  end.

(* This exercise turned out to be easier than we intended! *)
Theorem beval__beval_sc : forall st e,
  beval st e = beval_sc st e.
Proof.
  intros st e.
  destruct e; reflexivity.
Qed.
(* /SOLUTION *)
(** [] *)

(* EX4? (add_for_loop) *)
(** Add C-style [for] loops to the language of commands, update the
    [ceval] definition to define the semantics of [for] loops, and add
    cases for [for] loops as needed so that all the proofs in this file
    are accepted by Coq.

    A [for] loop should be parameterized by (a) a statement executed
    initially, (b) a test that is run on each iteration of the loop to
    determine whether the loop should continue, (c) a statement
    executed at the end of each loop iteration, and (d) a statement
    that makes up the body of the loop.  (You don't need to worry
    about making up a concrete Notation for [for] loops, but feel free
    to play with this too if you like.) *)

(* SOLUTION *)
(* (Providing a solution for this exercise would involve changes
   in many places, so we'll leave this one to you!) *)
(* /SOLUTION *)
(** [] *)

(* /FULL *)

(* FULL: <$Date: 2013-04-04 15:31:41 -0700 (Thu, 04 Apr 2013) $ *)

(* HIDE *)
(* Local Variables: *)
(* fill-column: 70 *)
(* outline-regexp: "(\\*\\* \\*+" *)
(* End: *)
(* mode: outline-minor *)
(* /HIDE *)
