Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.

Lemma param_same : forall a, param a a = a.
Proof. unfold param. 
intro a. destruct a; simpl; auto.
Qed.

Hint Rewrite param_same.

Lemma param_covariant : forall R R1 R2, SubRole R R2 -> SubRole (param R1 R) (param R1 R2).
  intros.
  unfold param. 
  destruct R1; destruct R2; simpl; auto. destruct R. auto. auto.
Qed.


Lemma param_sub1 : forall R R1, SubRole (param R1 R) R1.
Proof. intros. unfold param; simpl; auto.
unfold min. destruct R1; destruct R; simpl; auto.
Qed.


Lemma param_rep_r : `(param R Rep = R).
Proof.
  intros; unfold param; auto.
  case R; reflexivity.
Qed.


Lemma app_role_covariant : forall nu R1 R2, 
    SubRole R1 R2 -> SubRole (app_role nu R1)(app_role nu R2).
Proof.
  intros. unfold app_role. destruct nu; simpl; eauto using param_covariant.
Qed.



