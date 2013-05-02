
(* 
   CLAIM:
   ANY reflexive inductive  
   Coq relation (appropriately defined) is automatically 
   an equivalence relation which behaves as Leibniz equality!
*)

Print eq.

Eval simpl in (eq 2 2).   (* 2=2:Prop *)
Check (eq 2 2).
Example test : eq 2 2.
Proof. reflexivity. Qed.

Eval simpl in 1=2 /\ 2=2.
Check (1=2 /\ 2=2).
Example test2 : 1=2 /\ 2=2.
Proof. Admitted.

(* Coq out-of-the-box example first *)

Lemma coq_equality_is_transitive : forall (T : Type) (x y z: T), 
 x = y /\ y = z -> x = z.
Proof. 
  intros T x y z H.
  inversion H as [Hx Hy].
  rewrite -> Hx.
  rewrite -> Hy.
  reflexivity.
Qed.

(* similarly,  = is transitive   *)

Module My_Equality.  (* equality test kitchen *)

(* Print eql. *)
(* not defined *)

Inductive eql (T:Type) : T -> T -> Prop :=
  eql_refl : forall x, eql T x x.

(** Standard infix notation: *)

(* 
Notation "x = y" := (eq _ x y) 
                    (at level 70, no associativity) 
                    : type_scope.
*)

Eval simpl in (eql nat 2 2).
Eval simpl in (eql nat 1 2) /\ (eql nat 2 2).

Lemma eql_is_transitive_trans : forall (T : Type) (x y z: T), 
 eql T x y /\ eql T y z -> eql T x z.
Proof.
  intros T x y z H.
  inversion H as [Hx Hy].
  (**
  inversion Hx as [hx].
  inversion Hy as [hy].
  apply eql_refl.
  **)
  (* rewrite -> Hx.  NO!*)
  induction Hx as [hx].
  induction Hy as [hy].
  (* reflexivity. NO! *)
  apply eql_refl.
Qed.


Lemma eql_is_symmetric : forall (T : Type) (x y : T), 
 eql T x y -> eql T y x.
Proof.
  intros X x y H.  (* i.e. call T X *)
  induction H as [h].
  (* reflexivity.  NO! *)
  apply eql_refl.
Qed.


Lemma eql_is_leibniz_equality : forall (T : Type) (x y: T), 
 eql T x y -> forall P : T -> Prop, P x -> P y.
Proof.  (* same as for builtin Coq = *)
intros X x y H.
induction H as [xx].
intros P. 
intros PH. 
apply PH.
Qed.

(* eql has same definition as eq so, of course ... *)
Theorem eql_is_equality : forall (T: Type) (x y : T),
   eql T x y -> x = y.
Proof. 
intros T x y H. 
induction H.
reflexivity.
Qed.



End My_Equality.
