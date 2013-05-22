      
(* 
  Some experiments with equality.
  1. About the definitionand the usual properties of equality.
  2. The Axiom of Extensionality for equality.
*)

Print eq.

Eval simpl in (eq 2 2).   (* 2=2:Prop *)

Eval simpl in 1=2 /\ 2=2.

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

(* Print eql. *)   (* not defined *)

Inductive eql {T : Type} (x : T) : T -> Prop :=
  eql_refl : eql x x.

Print eq.
Print eql.

Lemma eql_is_transitive_trans : forall (T : Type) (x y z: T), 
 eql x y /\ eql y z -> eql x z.
Proof.
  intros T x y z H.
  inversion H as [Hx Hy].
  (* rewrite -> Hx.  NO!  *)
  induction Hx.
  induction Hy.
  (* reflexivity.  NO! *)
  apply eql_refl.
Qed.


Lemma eql_is_symmetric : forall (T : Type) (x y : T), 
 eql x y -> eql y x.
Proof.
  intros X x y H.  (* i.e. call T X *)
  induction H.
  (* reflexivity.  NO! *)
  apply eql_refl.
Qed.


Lemma eql_is_leibniz_equality : forall (T : Type) (x y: T), 
 eql x y -> forall P : T -> Prop, P x -> P y.
Proof.  (* same as for builtin Coq = *)
intros X x y H.
induction H.
intros P H. apply H.
Qed.

(* eql has same definition as eq so, of course ... *)
Theorem eql_is_eq : forall (T: Type) (x y : T),
   eql x y <-> x = y.
Proof.
intros T x y. 
split. 
(* -> *) 
intros H. induction H. reflexivity. 
(* <- *)
intros H. subst.
apply eql_refl. 
Qed.

(* extensionality for our eql *)
Axiom eql_extensionality : 
  forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  eql f g.

Definition f (m : nat) : nat := m+1.
Definition g (n : nat) : nat := 1+n.
Definition h (o : nat) : nat := o+1.

Lemma plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* known *) Admitted.

Lemma a : eql f g.
Proof. apply eql_extensionality.
(* work from inside out *)
intros.  unfold f. unfold g. apply plus_comm.
Qed.

Lemma b : f = h.
Proof. reflexivity.  (* definitions of f and h unify *)
Qed.

Lemma c : f = g.
Proof. (* error reflexivity. *) 
unfold f. unfold g. (* STUCK  *)
Abort. (* because = has no extensionality axiom *)

End My_Equality.
