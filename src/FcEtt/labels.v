Require Export Metalib.Metatheory.
Require Export FcEtt.ett_ott.
Require Export FcEtt.tactics.
Require Import FcEtt.imports.

Local Open Scope grade_scope.

Set Implicit Arguments.

Lemma P_sub_binds : forall P P' x psi, P_sub P' P -> binds x psi P -> exists psi', binds x psi' P' /\ psi' <= psi.
Proof. intros. induction H; eauto.
       inversion H0. inversion H4. subst. eexists. eauto.
       destruct IHP_sub. eauto. split_hyp. eexists. split; eauto.
Qed.


Hint Constructors P_sub : core.
Lemma P_sub_refl : forall P, uniq P -> P_sub P P.
Proof. induction 1; econstructor; eauto. reflexivity. Qed.


(* labels *)

Lemma labels_app : forall W1 W2, labels (W1 ++ W2) = labels W1 ++ labels W2.
Proof. induction W1; intros; simpl; auto. destruct a. destruct p.
       rewrite IHW1. eauto.
Qed.

Lemma labels_one : forall x psi0 A, labels [(x, (psi0, A))] = [(x,psi0)].
Proof. reflexivity. Qed.

Lemma labels_dom : forall W, dom (labels W) = dom W.
Proof. induction W; intros; simpl; auto. destruct a. destruct p. rewrite IHW. auto. Qed.

Lemma labels_uniq : forall W, uniq W -> uniq (labels W).
Proof. induction W; intros; simpl; auto. destruct a. destruct p. 
       destruct_uniq. econstructor; eauto. rewrite labels_dom; eauto. Qed.

Lemma binds_labels_1 : forall W x psi,  binds x psi (labels W) -> exists A, binds x (psi, A) W.
Proof. 
  intros. induction W; intros; inversion H; try destruct a; try destruct p; subst.
  inversion H0. subst. eauto.
  destruct IHW. auto. eauto. Qed.
Lemma binds_labels_2 : forall W x psi A,  binds x (psi,A) W -> binds x psi (labels W).
  intros. unfold labels. 
  eapply binds_map_2 with (f := (fun '(u,_) => u)) in H. auto.
Qed.

Lemma labels_subst_ctx : forall a x W1, labels (subst_ctx a x W1) = labels W1.
Proof.
  intros. induction W1; intros. auto. 
  try destruct a0; try destruct p; subst. simpl.
  f_equal. auto.
Qed.

Hint Rewrite labels_subst_ctx : rewr_list.
Hint Rewrite labels_one : rewr_list.
Hint Rewrite labels_app : rewr_list.
Hint Rewrite labels_dom : rewr_dom.

Hint Resolve labels_uniq : core.
Hint Resolve binds_labels_2 : core.

(* ctx_sub *)


Lemma ctx_sub_labels : forall (W1 W2 : context), ctx_sub W2 W1 -> P_sub (labels W2) (labels W1).
  induction 1; intros; eauto;
  econstructor; eauto.
Qed. 

Lemma ctx_sub_dom : forall (W1 W2 : context), ctx_sub W2 W1 -> dom W1 = dom W2.
Proof. induction 1; eauto. all: solve [simpl; f_equal; auto]. Qed.



Lemma ctx_sub_binds : forall {W W2 : context}, ctx_sub W2 W -> forall {x} {psi1:grade}{A}, 
      binds x (psi1, A) W -> exists psi0 , (psi0 <= psi1) /\ binds x (psi0, A) W2.
Proof.
  intros W W2 Sub. induction Sub; intros. inversion H. 

  eapply binds_cons_1 in H3. 
  move: H3 => [[? E] | b]. inversion E. subst.
  eexists. eauto.
  edestruct IHSub. eauto.
  split_hyp.
  eexists. split; eauto.

  eapply binds_cons_1 in H3. 
  move: H3 => [[? E] | b]. inversion E. subst.
  eexists. eauto.
  edestruct IHSub. eauto.
  split_hyp.
  eexists. split; eauto.
Qed.  

Lemma dom_meet_ctx_l : forall {W}, dom (meet_ctx_l q_C W) = dom W.
Proof. intros. induction W. simpl. auto.
       destruct a. destruct p. simpl. f_equal. auto.
Qed.


Lemma ctx_sub_meet_ctx_l :  forall {G1 G2},  ctx_sub G1 G2 -> ctx_sub (meet_ctx_l q_C G1) (meet_ctx_l q_C G2).
Proof.
  intros G1 G2 S. induction S.
  simpl. auto.
  
  simpl. simpl_env.
  econstructor; eauto.
  eapply po_meet_r. auto.
  all: try rewrite dom_meet_ctx_l; auto.

  simpl. simpl_env.
  econstructor; eauto.
  eapply po_meet_r. auto.
  all: try rewrite dom_meet_ctx_l; auto.
Qed.  

Lemma ctx_sub_refl : forall W : context, uniq W ->  ctx_sub W W.
Proof. 
  induction W; eauto.
  move => h. inversion h.
  destruct a. destruct a0.
  simpl_env.
  destruct s;
  econstructor; eauto;
  reflexivity.
Qed.

Lemma ctx_sub_app : forall W1 W2 W1' W2', ctx_sub W1 W1' -> ctx_sub W2 W2' -> uniq (W1 ++ W2) -> ctx_sub (W1 ++ W2) (W1' ++ W2').
Proof.
  intros.
  induction H. simpl. auto.

  simpl_env. inversion H1. subst.
  econstructor; eauto.
  rewrite -> dom_app in *.
  erewrite ctx_sub_dom with (W2 := W2)(W1 := W2'); eauto.

  simpl_env. inversion H1. subst.
  econstructor; eauto.
  rewrite -> dom_app in *.
  erewrite ctx_sub_dom with (W2 := W2)(W1 := W2'); eauto.
Qed.


(* -------------------- *)

Lemma meet_ctx_l_one : forall q x psi0 A,  meet_ctx_l q [(x, (psi0, A))] = [(x, (q + psi0, A))]. intros; eauto. Qed.
Lemma meet_ctx_l_app :forall W2 W1 q, meet_ctx_l q (W2 ++ W1) = meet_ctx_l q W2 ++ meet_ctx_l q W1.
Proof. induction W2; simpl; eauto. destruct a. destruct p. intros. f_equal. eauto. Qed.
Lemma meet_ctx_l_meet_ctx_l : forall W q,  meet_ctx_l q (meet_ctx_l q W) = meet_ctx_l q W.
Proof. induction W; simpl; eauto. destruct a. destruct p. intros. f_equal. 
       rewrite meet_assoc. rewrite meet_idem. auto. auto. Qed.
Lemma meet_ctx_l_subst_ctx : forall W q a x, meet_ctx_l q (subst_ctx a x W) = subst_ctx a x (meet_ctx_l q W).
Proof. induction W; simpl; eauto. destruct a. destruct p. intros. f_equal. eauto. Qed.
Lemma meet_ctx_l_uniq : forall W q, uniq W -> uniq (meet_ctx_l q W). intros. unfold meet_ctx_l. solve_uniq. Qed.

Lemma meet_ctx_l_ctx_sub : forall W q, uniq W ->  ctx_sub (meet_ctx_l q W) W.
intros. induction W; simpl; eauto. destruct a. destruct p.
destruct_uniq.

destruct s.

econstructor; eauto.
eapply leq_meet_r. unfold meet_ctx_l.  auto.

econstructor; eauto.
eapply leq_meet_r. unfold meet_ctx_l.  auto.

Qed.

Hint Rewrite meet_ctx_l_meet_ctx_l : rewr_list.
Hint Rewrite meet_ctx_l_one : rewr_list.
Hint Rewrite meet_ctx_l_app : rewr_list.
Hint Rewrite meet_ctx_l_subst_ctx : rewr_list.

Hint Resolve meet_ctx_l_uniq : core.
