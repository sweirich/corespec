Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Import FcEtt.imports.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.
Require Import FcEtt.tactics.

Require Import FcEtt.utils.
Require Import FcEtt.toplevel.

(* This file contains these results:

   -- the context is well-formed in any judgement
   -- all components are locally closed in any judgement
  *)

Lemma RolePath_lc : forall F a R, RolePath a F R -> lc_tm a.
Proof. intros. induction H; eauto.
Qed.

Lemma PatCtx_lcp : forall W G F p A B, PatternContexts W G F A p B -> lc_tm p.
Proof. intros. induction H; eauto.
Qed.


(* Lemma uniq_Path : forall F F' a R, RolePath a F R -> RolePath a F' R -> F = F'.
Proof. intros. generalize dependent F'. induction H; intros; auto.
       inversion H0; auto.
       inversion H1; subst. assert (Ax p a A R1 Rs = Cs A0).
       eapply binds_unique; eauto using uniq_toplevel. inversion H2.
       auto. inversion H1; subst. eauto.
       inversion H0; subst. eauto. 
Qed.

Lemma Value_lc : forall R A, Value R A -> lc_tm A.
Proof. intros; induction H; eauto using RolePath_lc.
Qed.


Hint Resolve Value_lc RolePath_lc : lc. *)


(* -------------------------------- *)

Lemma ctx_wff_mutual :
  (forall G0 a A, Typing G0 a A -> Ctx G0) /\
  (forall G0 phi,   PropWff G0 phi -> Ctx G0) /\
  (forall G0 D p1 p2, Iso G0 D p1 p2 -> Ctx G0) /\
  (forall G0 D A B T R,   DefEq G0 D A B T R -> Ctx G0) /\
  (forall G0, Ctx G0 -> True).
Proof.
  eapply typing_wff_iso_defeq_mutual; auto.
Qed.

Definition Typing_Ctx := first ctx_wff_mutual.
Definition PropWff_Ctx := second ctx_wff_mutual. 
Definition Iso_Ctx := third ctx_wff_mutual.
Definition DefEq_Ctx := fourth ctx_wff_mutual.


Hint Resolve Typing_Ctx PropWff_Ctx Iso_Ctx DefEq_Ctx.

Fixpoint ctx_nom (G : context) := match G with
  | nil => nil
  | (x, Tm _) :: G' => (x, Nom) :: ctx_nom G'
  | (x, Co _) :: G' => ctx_nom G'
  end.

Lemma Ctx_uniq : forall G, Ctx G -> uniq G.
  induction G; try auto.
  inversion 1; subst; solve_uniq.
Qed.

Lemma dom_rctx_le_ctx : forall G, dom (ctx_nom G) [<=] dom G.
Proof. intros; induction G; simpl. fsetdec.
       destruct a, s. simpl. fsetdec. fsetdec.
Qed.

Lemma notin_ctx_rctx : forall x G, x `notin` (dom G) -> x `notin` dom (ctx_nom G).
Proof. intros. induction G. auto. destruct a, s; simpl in *.
       all : pose (P := H); apply notin_add_2 in P; fsetdec.
Qed.

Lemma ctx_to_rctx_uniq : forall G, Ctx G -> uniq (ctx_nom G).
Proof. intros G. induction G; intros.
        - simpl; auto.
        - inversion H; subst; simpl. apply Ctx_uniq in H.
          apply IHG in H2. econstructor; eauto. 
          assert (P : dom (ctx_nom G) [<=] dom G). 
          { apply dom_rctx_le_ctx. } fsetdec.
          inversion H. apply IHG; auto.
Qed.

Lemma ctx_to_rctx_binds_tm : forall G x A, binds x (Tm A) G ->
                                             binds x Nom (ctx_nom G).
Proof. intros G. induction G; intros; simpl; eauto.
       destruct a, s. apply binds_cons_1 in H. inversion H; eauto.
       inversion H0. inversion H2. subst. auto.
       apply binds_cons_1 in H. inversion H. inversion H0. inversion H2.
       eauto.
Qed.

Hint Resolve Ctx_uniq.

Lemma lc_mutual :
  (forall G0 a A, Typing G0 a A -> lc_tm a /\ lc_tm A) /\
  (forall G0 phi , PropWff G0 phi -> lc_constraint phi) /\
  (forall G0 D p1 p2,  Iso G0 D p1 p2 -> lc_constraint p1 /\ lc_constraint p2) /\
  (forall G0 D A B T R, DefEq G0 D A B T R -> lc_tm A /\ lc_tm B /\ lc_tm T) /\
  (forall G0, Ctx G0 -> forall x s , binds x s G0 -> lc_sort s).
Proof.
  eapply typing_wff_iso_defeq_mutual.
  all: TacticsInternals.pre; basic_solve_n 2.
  all: split_hyp.
  all: lc_solve.
Qed.

Definition Typing_lc  := first lc_mutual.
Definition PropWff_lc := second lc_mutual.
Definition Iso_lc     := third lc_mutual.
Definition DefEq_lc   := fourth lc_mutual.
Definition Ctx_lc     := fifth lc_mutual.

Lemma Typing_lc1 : forall G0 a A, Typing G0 a A -> lc_tm a.
Proof.
  intros. apply (first lc_mutual) in H. destruct H. auto.
Qed.
Lemma Typing_lc2 : forall G0 a A, Typing G0 a A -> lc_tm A.
Proof.
  intros. apply (first lc_mutual) in H. destruct H. auto.
Qed.

Lemma Iso_lc1 : forall G0 D p1 p2 , Iso G0 D p1 p2  -> lc_constraint p1.
Proof.
  intros. apply (third lc_mutual) in H. destruct H. auto.
Qed.
Lemma Iso_lc2 : forall G0 D p1 p2 , Iso G0 D p1 p2 -> lc_constraint p2.
Proof.
  intros. apply (third lc_mutual) in H. destruct H. auto.
Qed.
Lemma DefEq_lc1 : forall G0 D A B T R,   DefEq G0 D A B T R -> lc_tm A.
Proof.
  intros. apply (fourth lc_mutual) in H. destruct H. auto.
Qed.

Lemma DefEq_lc2 : forall G0 D A B T R,   DefEq G0 D A B T R -> lc_tm B.
Proof.
  intros. apply (fourth lc_mutual) in H. split_hyp. auto.
Qed.
Lemma DefEq_lc3 : forall G0 D A B T R,   DefEq G0 D A B T R -> lc_tm T.
Proof.
  intros. apply (fourth lc_mutual) in H. split_hyp. auto.
Qed.

Hint Resolve Typing_lc1 Typing_lc2 Iso_lc1 Iso_lc2 DefEq_lc1 DefEq_lc2 DefEq_lc3 Ctx_lc : lc.

Lemma Toplevel_lc : forall c s, binds c s toplevel -> lc_sig_sort s.
Proof. induction Sig_toplevel.
       - intros. inversion H.
       - intros. destruct H1. inversion H1. subst.
         simpl in H0. eauto. eauto with lc.
         eauto.
       - intros.
         destruct (binds_cons_1 _ _ _ _ _ _ H4); basic_solve. inversion H5.
         subst. econstructor. eapply PatCtx_lcp; eauto. eapply Typing_lc1; eauto.
         eapply Typing_lc1; eauto.
Qed.
