Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Import FcEtt.imports.
(* Require Import FcEtt.fix_typing. *)
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.
Require Import FcEtt.tactics.
Require Export FcEtt.narrowing.

Require Import FcEtt.utils.

(* Require Import FcEtt.sigs. *)
Require Import FcEtt.toplevel.

(* This file contains these results:

   -- the context is well-formed in any judgement
   -- all components are locally closed in any judgement
  *)

(*
Lemma Path_lc : forall T a, Path T a -> lc_tm a.
Proof. induction 1; eauto. Qed.

Hint Resolve Path_lc : lc.


Lemma DataTy_lc : forall A, DataTy A a_Star -> lc_tm A.
Proof.
  intros. induction H; lc_solve.
Qed.
Hint Resolve DataTy_lc : lc.
*)



Lemma Value_lc : forall A, Value A -> lc_tm A.
Proof.
  induction 1; eauto.
Qed.

Lemma CoercedValue_lc : forall A, CoercedValue A -> lc_tm A.
  induction 1; sfirstorder ctrs: CoercedValue use: Value_lc.
Qed.

Hint Resolve Value_lc CoercedValue_lc : lc.


(* -------------------------------- *)

Lemma Ctx_uniq : forall G, Ctx G -> uniq G.
  induction G; try auto.
  inversion 1; subst; solve_uniq.
Qed.

Hint Resolve Ctx_uniq.


Print Ltac gather_atoms.
Print Ltac pick_fresh.

Ltac all_union_set := let L := gather_atoms in exact L.

Lemma ctx_wff_narrow_mutual :
  (forall G0 psi a A, Typing G0 psi a A -> (Ctx G0 /\ (forall G1, ctx_sub G1 G0 -> Typing G1 psi a A))) /\
  (forall G0 psi phi,   PropWff G0 psi phi -> (Ctx G0 /\ (forall G1, ctx_sub G1 G0 -> PropWff G1 psi phi))) /\
  (forall G0 psi p1 p2, Iso G0 psi p1 p2 -> (Ctx G0 /\ (forall G1, ctx_sub G1 G0 -> Iso G1 psi p1 p2))) /\
  (forall G0 psi phi,   DefEq G0 psi phi -> (Ctx G0 /\ (forall G1, ctx_sub G1 G0 -> DefEq G1 psi phi))) /\
  (forall G0, Ctx G0 -> forall G1, ctx_sub G1 G0 -> Ctx G1) /\
  (forall G0 psi psi0 a b A,CDefEq G0 psi psi0 a b A -> (Ctx G0 /\ (forall G1, ctx_sub G1 G0 -> CDefEq G1 psi psi0 a b A))).
Proof.
  apply typing_wff_iso_defeq_mutual; try split; auto;
    try solve intuition; try tauto; intros.
  (* 48 goals *)
  all : try solve [sfirstorder].
  (* 27 goals (after sfirstorder) *)
  all : try solve [hauto l: on use: ctx_sub_meet_ctx_l ctrs:Typing].
  (* 19 goals (after hauto) *)
  all : try match goal with | [ |- Ctx ?G] =>
           try solve [pick fresh x0; hauto depth:1 lq: on l: on q: on inv: Ctx simp: destruct_notin] end.
  (* 14 goals (afer hauto) *)
  - move : (ctx_sub_binds H0 b) => [psi0' [h0 h1]].
    apply E_Var with (psi0 := psi0');  hauto db:lattice_props.
  - apply E_Pi with (L := ltac:(all_union_set)).
    + intros.
      destruct_notin.
      apply H; auto.
      apply ctx_sub_app;
        hfcrush ctrs:uniq use:ctx_sub_uniq, ctx_sub_refl.
    + sfirstorder ctrs:Typing.
  - pick fresh x0.
    apply E_Abs with (L := ltac:(all_union_set)).
    + intros.
      destruct_notin.
      apply H; auto.
      apply ctx_sub_app; auto.
      apply ctx_sub_refl.
      sfirstorder ctrs:uniq.
      move : (H _ Fr).
      fcrush use:ctx_sub_uniq.
    + hauto lq:on use:ctx_sub_meet_ctx_l.
  (* Same as E_Pi *)
  - apply E_CPi with (L := ltac:(all_union_set)).
    + intros.
      destruct_notin.
      apply H; auto.
      apply ctx_sub_app;
        hfcrush ctrs:uniq use:ctx_sub_uniq, ctx_sub_refl.
    + sfirstorder ctrs:Typing.
  (* Same as E_Abs *)
  - pick fresh x0.
    apply E_CAbs with (L := ltac:(all_union_set)).
    + intros.
      destruct_notin.
      apply H; auto.
      apply ctx_sub_app; auto.
      apply ctx_sub_refl.
      sfirstorder ctrs:uniq.
      move : (H _ Fr).
      fcrush use:ctx_sub_uniq.
    + hauto lq:on use:ctx_sub_meet_ctx_l.
  (* Similar to E_Var *)
  - move : (ctx_sub_binds H0 b) => [psi0' [h0 h1]].
    eapply E_Assn with (psi0 := psi0'); hauto db:lattice_props.
  - apply E_PiCong with (L := ltac:(all_union_set)); try firstorder.
    apply H0.
    fsetdec.
    apply ctx_sub_app; auto.
    apply ctx_sub_refl; auto.
    sblast use:ctx_sub_uniq.
  (* Same as E_Abs *)
  - pick fresh x0.
    apply E_AbsCong with (L := ltac:(all_union_set)).
    + intros.
      destruct_notin.
      apply H; auto.
      apply ctx_sub_app; auto.
      apply ctx_sub_refl.
      sfirstorder ctrs:uniq.
      move : (H _ Fr).
      fcrush use:ctx_sub_uniq.
    + hauto lq:on use:ctx_sub_meet_ctx_l.
  (* Similar to E_CPi *)
  - apply E_CPiCong with (L := ltac:(all_union_set)); auto; try sfirstorder depth:1.
    intros.
    apply H0; auto.
    apply ctx_sub_app; auto.
    apply ctx_sub_refl.
    sfirstorder ctrs:uniq.
    sblast use:ctx_sub_uniq.
  (* Same as E_CAbs *)
  - pick fresh x0.
    apply E_CAbsCong with (L := ltac:(all_union_set)).
    + intros.
      destruct_notin.
      apply H; auto.
      apply ctx_sub_app; auto.
      apply ctx_sub_refl.
      sfirstorder ctrs:uniq.
      move : (H _ Fr).
      fcrush use:ctx_sub_uniq.
    + hauto lq:on use:ctx_sub_meet_ctx_l.
  - apply E_ImplAbs with (c := c).
    apply H.
    (* TODO: ctx_sub (c ~ (q_C, Co phi1) ++ G1) (c ~ (q_C, Co phi1) ++ G) is so common that it is worth its own lemma *)
    apply ctx_sub_app; auto.
    apply ctx_sub_refl.
    sfirstorder ctrs:uniq.
    sauto lq: on use: ctx_sub_uniq, ctx_sub_dom, Ctx_uniq.
    hauto l: on use: ctx_sub_meet_ctx_l.
  - inversion H; auto.
  - sauto q: on use: ctx_sub_meet_ctx_l.
  - sauto q: on use: ctx_sub_meet_ctx_l.
Qed.

(* Maybe I should split narrowing and ctx into 2 lemmas ?*)
Definition Typing_Ctx  := first  ctx_wff_narrow_mutual.
Definition PropWff_Ctx := second ctx_wff_narrow_mutual.
Definition Iso_Ctx     := third  ctx_wff_narrow_mutual.
Definition DefEq_Ctx   := fourth ctx_wff_narrow_mutual.
Definition Ctx_Ctx     := fifth ctx_wff_narrow_mutual.
Lemma CDefEq_Ctx :
  forall G0 psi psi0 a b A,CDefEq G0 psi psi0 a b A -> (Ctx G0 /\ (forall G1, ctx_sub G1 G0 -> CDefEq G1 psi psi0 a b A)).
Proof.
  hauto l: on use: ctx_wff_narrow_mutual.
Qed.

(* TODO: put these hints in a database? *)
Hint Resolve Typing_Ctx PropWff_Ctx Iso_Ctx DefEq_Ctx Ctx_Ctx CDefEq_Ctx.

Lemma lc_mutual :
  (forall G0 psi a A, Typing G0 psi a A -> lc_tm a /\ lc_tm A) /\
  (forall G0 psi phi, PropWff G0 psi phi -> lc_constraint phi) /\
  (forall G0 psi p1 p2, Iso G0 psi p1 p2 -> lc_constraint p1 /\ lc_constraint p2) /\
  (forall G0 psi phi, DefEq G0 psi phi -> lc_constraint phi) /\
  (forall G0 , Ctx G0 -> forall x psi s , binds x (psi, s) G0 -> lc_sort s) /\
  (forall G0 psi psi0 a b A,CDefEq G0 psi psi0 a b A -> lc_tm a /\ lc_tm b /\ lc_tm A).
Proof.
  apply typing_wff_iso_defeq_mutual.
  all: pre; basic_solve_n 2.
  all: split_hyp.
  all: lc_solve.
  all : try constructor; lc_solve.
  all : try sauto depth:1 lq: on.
Qed.



Definition Typing_lc  := first lc_mutual.
Definition PropWff_lc := second lc_mutual.
Definition Iso_lc     := third lc_mutual.
Definition DefEq_lc   := fourth lc_mutual.
Definition Ctx_lc     := fifth lc_mutual.
Lemma CDefEq_lc : forall G0 psi psi0 a b A,CDefEq G0 psi psi0 a b A -> lc_tm a /\ lc_tm b /\ lc_tm A.
Proof.
  pose proof lc_mutual.
  tauto.
Qed.

Lemma CTyping_lc1 : forall G0 psi a A, CTyping G0 psi a A -> lc_tm a.
Admitted.

Lemma CTyping_lc2 : forall G0 psi a A, CTyping G0 psi a A -> lc_tm A.
Admitted.

Lemma Typing_lc1 : forall G0 psi a A, Typing G0 psi a A -> lc_tm a.
Proof.
  intros. apply (first lc_mutual) in H. destruct H. auto.
Qed.
Lemma Typing_lc2 : forall G0 psi a A, Typing G0 psi a A -> lc_tm A.
Proof.
  intros. apply (first lc_mutual) in H. destruct H. auto.
Qed.

Lemma Iso_lc1 : forall G0 psi p1 p2, Iso G0 psi p1 p2 -> lc_constraint p1.
Proof.
  intros. apply (third lc_mutual) in H. destruct H. auto.
Qed.
Lemma Iso_lc2 : forall G0 psi p1 p2, Iso G0 psi p1 p2 -> lc_constraint p2.
Proof.
  intros. apply (third lc_mutual) in H. destruct H. auto.
Qed.
Lemma DefEq_lc1 : forall G0 psi A B T,   DefEq G0 psi (Eq A B T) -> lc_tm A.
Proof.
  sauto lq: on use: DefEq_lc.
Qed.
Lemma DefEq_lc2 : forall G0 psi A B T,   DefEq G0 psi (Eq A B T) -> lc_tm B.
Proof.
  sauto lq: on use: DefEq_lc.
Qed.
Lemma DefEq_lc3 : forall G0 psi A B T,   DefEq G0 psi (Eq A B T) -> lc_tm T.
Proof.
  sauto lq: on use: DefEq_lc.
Qed.
Lemma CDefEq_lc1 : forall G0 psi psi0 A B T,   CDefEq G0 psi psi0 A B T -> lc_tm A.
Proof.
  sauto lq: on use: CDefEq_lc.
Qed.
Lemma CDefEq_lc2 : forall G0 psi psi0 A B T,   CDefEq G0 psi psi0 A B T -> lc_tm B.
Proof.
  sauto lq: on use: CDefEq_lc.
Qed.
Lemma CDefEq_lc3 : forall G0 psi psi0 A B T,   CDefEq G0 psi psi0 A B T -> lc_tm T.
Proof.
  sauto lq: on use: CDefEq_lc.
Qed.

Hint Resolve CTyping_lc1 CTyping_lc2 Typing_lc1 Typing_lc2 Iso_lc1 Iso_lc2
     DefEq_lc1 DefEq_lc2 DefEq_lc3 Ctx_lc CDefEq_lc1 CDefEq_lc2 CDefEq_lc3 : lc.

Lemma Toplevel_lc : forall c psi s, binds c (psi, s) toplevel -> lc_sig_sort s.
Proof. induction Sig_toplevel.
       intros. inversion H.
       intros. destruct H2. inversion H2. subst.
       simpl in H0. eauto. eauto with lc.
       eauto.
Qed.

Lemma DefEq_uniq : (forall G psi phi,
  DefEq G psi phi -> uniq G).
Proof.
  sfirstorder use: DefEq_Ctx, Ctx_uniq.
Qed.

Lemma Typing_uniq : forall W psi a A, Typing W psi a A -> uniq W.
Proof. hauto lq: on use: Typing_Ctx, Ctx_uniq. Qed.




Lemma CGrade_Grade_lc : 
  (forall P psi a,
  Grade P psi a -> lc_tm a) /\
  (forall P psi psi0 a,
  CGrade P psi psi0 a -> lc_tm a) /\
  (forall P psi phi,
  CoGrade P psi phi -> lc_constraint phi).
Proof. 
  apply CGrade_Grade_mutual.
  all: intros; split_hyp; eauto.
Qed.

Lemma Grade_lc : forall {P psi a}, Grade P psi a -> lc_tm a.
Proof. sfirstorder use:CGrade_Grade_lc. Qed.
Lemma CGrade_lc : forall {P psi phi a}, CGrade P psi phi a -> lc_tm a.
Proof. sfirstorder use:CGrade_Grade_lc. Qed.
Lemma CoGrade_lc : forall P psi phi, CoGrade P psi phi -> lc_constraint phi.
Proof. sfirstorder use:CGrade_Grade_lc. Qed.

Lemma CEq_GEq_lc : 
  (forall P psi psi0 a b,
  CEq P psi psi0 a b -> lc_tm a /\ lc_tm b) /\
  (forall P psi a b,
    GEq P psi a b -> lc_tm a /\ lc_tm b) /\
  (forall P psi phi1 phi2, CoGEq P psi phi1 phi2 -> lc_constraint phi1 /\ lc_constraint phi2).
Proof. 
  apply CEq_GEq_mutual.
  all: pre; basic_solve_n 2.
  all: split_hyp.
  all: lc_solve.
Qed.


Lemma GEq_lc1 : forall {W a psi b}, GEq W psi a b -> lc_tm a.
Proof. hauto l: on use: CEq_GEq_lc. Qed.
Lemma GEq_lc2 : forall {W a psi b}, GEq W psi a b -> lc_tm b.
Proof. hauto l: on use: CEq_GEq_lc. Qed.
Lemma CEq_lc1 : forall {W a psi phi b}, CEq W psi phi a b -> lc_tm a.
Proof. hauto l: on use: CEq_GEq_lc. Qed.
Lemma CEq_lc2 : forall {W a psi phi b}, CEq W psi phi a b -> lc_tm b.
Proof. hauto l: on use: CEq_GEq_lc. Qed.
Lemma CoGEq_lc1 : forall {P psi phi1 phi2}, CoGEq P psi phi1 phi2 -> lc_constraint phi1.
Proof. hauto l: on use: CEq_GEq_lc. Qed.
Lemma CoGEq_lc2 : forall {P psi phi1 phi2}, CoGEq P psi phi1 phi2 -> lc_constraint phi2.
Proof. hauto l: on use: CEq_GEq_lc. Qed.
