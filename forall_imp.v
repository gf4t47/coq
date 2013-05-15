Theorem imp: forall (P Q : Prop),
  forall (_:P), Q <-> (P -> Q).
Proof.
  intros.
  split.
  intros. apply H0.
  intros. apply H0. apply H.
Qed.

Theorem imp': forall (P Q : Prop),
  forall (_:P), Q <-> (P -> Q).
Proof.
  tauto.
Qed.