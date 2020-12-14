Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Import FcEtt.imports.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.
Require Import FcEtt.tactics.

Require Import FcEtt.utils.

Require Import FcEtt.sigs.
Require Import FcEtt.toplevel.

(* This file contains these results:

   -- the context is well-formed in any judgement
   -- all components are locally closed in any judgement
  *)

Lemma CoercedValue_Value_lc_mutual: (forall A, CoercedValue A -> lc_tm A) /\
                                    (forall A, Value A -> lc_tm A).
Proof.
  apply CoercedValue_Value_mutual; eauto.
Qed.

Lemma Value_lc : forall A, Value A -> lc_tm A.
  destruct (CoercedValue_Value_lc_mutual); auto.
Qed.
Lemma CoercedValue_lc : forall A, CoercedValue A -> lc_tm A.
  destruct (CoercedValue_Value_lc_mutual); auto.
Qed.

Hint Resolve Value_lc CoercedValue_lc : lc.


(* -------------------------------- *)

Lemma SubRho_trans : forall r2 r1 r3, SubRho r1 r2 -> SubRho r2 r3 -> SubRho r1 r3.
Proof.
  intros.
  destruct r2. inversion H0; subst; auto.
  inversion H; subst; auto.
Qed.

Lemma dom_SubG : forall G1 G2, SubG G1 G2 -> dom G1 [=] dom G2.
Proof. induction 1; simpl; fsetdec. Qed.

Lemma binds_SubG : forall G G2 x rho1 A, SubG G G2  -> binds x (Tm rho1 A) G -> 
                                  exists rho2, SubRho rho1 rho2 /\ binds x (Tm rho2 A) G2.
Proof.
  induction 1; intros.
  - inversion H.
  -
    destruct (binds_cons_1 _ _ _ _ _ _ H2). 
    + move: H3 => [e1 e2]. inversion e2. subst.
      exists rho2. split; eauto.
    + destruct IHSubG as [rho3 [SR BB]]; eauto.
  - destruct (binds_cons_1 _ _ _ _ _ _ H1). 
    move: H2 => [e1 e2]. inversion e2. 
    destruct IHSubG as [rho3 [SR BB]]; eauto.
Qed.

  

Lemma ctx_wff_mutual :
  (forall G0 r a A, Typing G0 r a A -> Ctx G0) /\
  (forall G0 r phi,   PropWff G0 r phi -> Ctx G0) /\
  (forall G0 D r p1 p2, Iso G0 D r p1 p2 -> Ctx G0) /\
  (forall G0 D r A B T,   DefEq G0 D r A B T -> Ctx G0) /\
  (forall G0, Ctx G0 -> True).
Proof.
  eapply typing_wff_iso_defeq_mutual; auto.
Qed.

Definition Typing_Ctx  := first  ctx_wff_mutual.
Definition PropWff_Ctx := second ctx_wff_mutual.
Definition Iso_Ctx     := third  ctx_wff_mutual.
Definition DefEq_Ctx   := fourth ctx_wff_mutual.

Hint Resolve Typing_Ctx PropWff_Ctx Iso_Ctx DefEq_Ctx : core.

Lemma Ctx_uniq : forall G, Ctx G -> uniq G.
  induction G; try auto.
  inversion 1; subst; solve_uniq.
Qed.

Hint Resolve Ctx_uniq : core.


Lemma lc_mutual :
  (forall G0 r a A, Typing G0 r a A -> lc_tm a /\ lc_tm A) /\
  (forall G0 r phi, PropWff G0 r phi -> lc_constraint phi) /\
  (forall G0 D r p1 p2, Iso G0 D r p1 p2 -> lc_constraint p1 /\ lc_constraint p2) /\
  (forall G0 D r A B T, DefEq G0 D r A B T -> lc_tm A /\ lc_tm B /\ lc_tm T) /\
  (forall G0, Ctx G0 -> forall x s , binds x s G0 -> lc_sort s).
Proof.
  eapply typing_wff_iso_defeq_mutual.
  all: pre; basic_solve_n 2.
  all: split_hyp.
  all: lc_solve.
Admitted.
(* This version of the proof is incredibly slow. *)
(*
  all: pre; basic_solve.
  all: try oh_c'mon.
  all: try invert_open_wrt.
  all: try pick fresh c for L.
  all: try eapply lc_a_UCAbs_exists; eauto.
  all: try apply H; eauto.
  all: eapply (lc_a_UAbs_exists c). rewrite e. eauto. done.
Qed.*)

Definition Typing_lc  := first lc_mutual.
Definition PropWff_lc := second lc_mutual.
Definition Iso_lc     := third lc_mutual.
Definition DefEq_lc   := fourth lc_mutual.
Definition Ctx_lc     := fifth lc_mutual.

Lemma Typing_lc1 : forall G0 r a A, Typing G0 r a A -> lc_tm a.
Proof.
  intros. apply (first lc_mutual) in H. destruct H. auto.
Qed.
Lemma Typing_lc2 : forall G0 r a A, Typing G0 r a A -> lc_tm A.
Proof.
  intros. apply (first lc_mutual) in H. destruct H. auto.
Qed.

Lemma Iso_lc1 : forall G0 D r p1 p2, Iso G0 D r p1 p2 -> lc_constraint p1.
Proof.
  intros. apply (third lc_mutual) in H. destruct H. auto.
Qed.
Lemma Iso_lc2 : forall G0 D r p1 p2, Iso G0 D r p1 p2 -> lc_constraint p2.
Proof.
  intros. apply (third lc_mutual) in H. destruct H. auto.
Qed.
Lemma DefEq_lc1 : forall G0 D r A B T,   DefEq G0 D r A B T -> lc_tm A.
Proof.
  intros. apply (fourth lc_mutual) in H. destruct H. auto.
Qed.

Lemma DefEq_lc2 : forall G0 D r A B T,   DefEq G0 D r A B T -> lc_tm B.
Proof.
  intros. apply (fourth lc_mutual) in H. split_hyp. auto.
Qed.
Lemma DefEq_lc3 : forall G0 D r A B T,   DefEq G0 D r A B T -> lc_tm T.
Proof.
  intros. apply (fourth lc_mutual) in H. split_hyp. auto.
Qed.

Hint Resolve Typing_lc1 Typing_lc2 Iso_lc1 Iso_lc2 DefEq_lc1 DefEq_lc2 DefEq_lc3 Ctx_lc : lc.

Lemma Toplevel_lc : forall c s, binds c s toplevel -> lc_sig_sort s.
Proof. induction Sig_toplevel.
       intros. inversion H.
       intros. destruct H2. inversion H2. subst.
       simpl in H0. eauto. eauto with lc.
       eauto.

Qed.



