Check pred(S 0) = 0.
Definition test1 := pred(S 0) = 0.
Check test1.

Check forall n:nat, pred (S n) = n.
Definition test2 := forall n:nat, pred (S n) = n.
Check test2.
Lemma lemma2 : forall n:nat, pred (S n) = n.
Proof.
  intros.
  reflexivity.
Qed.

Check forall n:nat, S(pred n) = n.
Definition test3 := forall n:nat, S(pred n) = n.
Check test3.
Lemma lemma3 : forall n:nat, S(pred n) = n.
Proof.
Admitted.


(** Check forall n : nat, pred (S n).**)
Check 5.
Check fun n => pred (S n).
Check forall n:nat, pred (S n).
Definition test4 := forall n:nat, pred (S 3).
Check 5.