(* Solutions provided by B.Pierce et al, with my 
note regarding plus_n_O *)

Print plus_n_O.  (* apparently BUILT IN *)

Lemma plus_n_0 : forall n:nat,
   n+0=n.
Proof.
   intros. induction n.
   reflexivity.
   simpl. rewrite -> IHn. reflexivity.
Qed.
Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof. 
  (* ADMITTED *)
  intros n m. induction n as [| n'].
  (* Case "n = 0". *)
    simpl. reflexivity.
  (* Case "n = S n'". *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.
(* /ADMITTED *)

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* ADMITTED *)
  intros n m. induction m as [| m'].
  (* Case "m = 0". *)
    simpl. (* rewrite -> plus_n_O. *)
      rewrite -> plus_n_0.  reflexivity.
  (* Case "m = S m'". *)
    simpl. rewrite <- IHm'. rewrite <- plus_n_Sm.
    reflexivity.  Qed.
(* /ADMITTED *)


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* ADMITTED *)
  intros n m p. induction n as [| n']. 
  (* Case "n = 0". *)
    reflexivity. 
  (* Case "n = S n'". *)
    simpl. rewrite -> IHn'. reflexivity.   Qed.
(* /ADMITTED *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* ADMITTED *)
  intros n. induction n as [| n'].
  (* Case "n = 0". *)
    reflexivity.
  (* Case "n = S n'". *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.
(* /ADMITTED *)

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  (* ADMITTED *)
  intros n m p.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n).
    (* Case "Proof of assertion". *)
    rewrite <- plus_comm. reflexivity.
  rewrite -> H. rewrite -> plus_assoc. reflexivity.  Qed.
(* /ADMITTED *)
(* QUIETSOLUTION *)

Theorem mult_m_Sn : forall m n : nat,
 m * (S n) = m + (m * n).
Proof.
  induction m as [| m'].
  (* Case "m = 0". *)
    intros n. simpl. reflexivity.
  (* Case "m = S m'". *)
    intros n.
    simpl.
    rewrite -> IHm'.
    rewrite -> plus_swap.
    reflexivity.  Qed.
(* /QUIETSOLUTION *)

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  (* ADMITTED *)
  induction m as [| m'].
  (* Case "m = 0". *)
    intros n. simpl. rewrite mult_0_r. reflexivity.
  (* Case "m = S m'". *)
    intros n.
    simpl.
    rewrite -> mult_m_Sn.
    rewrite -> IHm'.
    reflexivity.  Qed.
(* /ADMITTED *)
