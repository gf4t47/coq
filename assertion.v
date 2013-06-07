Require Export Hoare.
  
Definition as0: Assertion:= fun st => st X = 3.
Definition s1 := update empty_state X 3.
Definition s2 := update empty_state X 5.

Example chk_as0_s1 :  (as0 s1).
Proof. reflexivity. Qed.

Example chk_as0_s2 :  ~(as0 s2).
Proof. unfold not. unfold as0.
intros. inversion H. Qed. 