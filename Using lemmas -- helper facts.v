
(* Using lemmas -- helper facts -- to prove theorem 
   Watch goals carefully!  *)

Lemma fact1 : andb true false = false.
Proof. reflexivity. Qed.
Lemma fact2 : andb false true = false.
Proof. reflexivity. Qed.

Theorem andb_eq_orb : 
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c H.
  destruct b. destruct c. reflexivity. 
  rewrite <- fact1. rewrite H. reflexivity.
  destruct c.
  rewrite <- fact2. rewrite H. reflexivity.
  reflexivity. 
  Qed.


(* Redo without lemmas 
   Watch goal carefully! *)

Theorem andb_eq_orb_without_lemmas : 
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof. 
   intros b c.  (* leave hypothesis in place *)
   destruct b.  destruct c.  (* reduce to specific cases *)
   simpl. reflexivity.  (* zap first case *)
   simpl. intros H. rewrite -> H. reflexivity. (* why this? *) 
   simpl.  intros H. rewrite -> H. reflexivity.
Qed