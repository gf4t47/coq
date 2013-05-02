(** **** KE DING 8318 *)

(* QUIZ 2 *)
Require Export Basics.

(* Fill in proofs for Problems #1,2,3
   and email this file to jrfisher@csupomona.edu
   with subject heading "Quiz2" *)

(* Problem #1 *)
Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  intros n.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity. Qed.

(* Problem #2 *)
Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  reflexivity.
  simpl. rewrite -> IHn'. 
  reflexivity.  Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  destruct n as [| n'].
  reflexivity.
  simpl.
  rewrite -> plus_0_r.
  reflexivity. Qed.
  
(* Assume this Lemma, might be useful in #3 *)
Lemma plus_assoc : forall m n p:nat, 
       p + (m + n)  = (p + m) + n.
Proof.
Admitted.

(* Problem #3 *)
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  rewrite -> plus_assoc.
  reflexivity. Qed.
  
(** **** KE DING 8318 *)
