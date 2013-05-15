(** **** KE DING 8318 *)

(* 
Logic.  Find proofs for these 4 problems. 
DO NOT USE tauto.
*)


Theorem quiz1: 
   forall P Q : Prop, P /\ Q  -> P \/ Q.
Proof. 
  intros.
  inversion H.
  left.
  apply H0.
Qed.

Theorem quiz2: 
   forall X, forall a b : X, (a=b) /\ (a<>b) -> False.
Proof.
  intros.
  inversion H.
  unfold not in H1.
  apply H1.
  apply H0.
Qed.

Theorem quiz3 :
forall P Q : Prop,  P \/ Q -> ~~(P \/ Q).
Proof.
  intros.
  unfold not.
  intros.
  apply H0.
  apply H.
Qed.

Theorem quiz4 :
forall P Q: Prop,  P \/ Q -> ~~P \/ ~~Q.
Proof. 
  intros.
  inversion H.
    left.
    unfold not.
    intros.
    apply H1.
    apply H0.

    right.
    unfold not.
    intros.
    apply H1.
    apply H0.
Qed.
(** **** KE DING 8318 *)
