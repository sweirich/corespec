Require Export FcEtt.imports.
Require Export FcEtt.tactics.
Require Export FcEtt.labels. 
Require Export FcEtt.ett_ind.
Require Export FcEtt.uniq. 
Require Import FcEtt.ett_ind.

Set Implicit Arguments.
Open Scope grade_scope.


Scheme Grade_ind' := Induction for Grade Sort Prop
    with CGrade_ind'   := Induction for CGrade Sort Prop
    with CoGrade_ind' := Induction for CoGrade Sort Prop.

Combined Scheme CGrade_Grade_mutual
  from Grade_ind', CGrade_ind', CoGrade_ind'.


Ltac fresh_apply_Grade x := 
  match goal with 
      | [ |- Grade ?P ?psi (a_Pi ?psi2 ?a ?b) ] => pick fresh x and apply G_Pi
      | [ |- Grade ?P ?psi (a_CPi ?psi2 ?a ?b) ] => pick fresh x and apply G_CPi
      | [ |- Grade ?P ?psi (a_UAbs ?psi2 ?b) ] => pick fresh x and apply G_Abs
      | [ |- Grade ?P ?psi (a_UCAbs ?psi2 ?b) ] => pick fresh x and apply G_CAbs
    end.

Ltac fresh_apply_GEq x := 
  match goal with 
      | [ |- GEq ?P ?psi (a_Pi ?psi2 ?a ?b) (a_Pi ?psi3 ?a2 ?b2) ] => pick fresh x and apply GEq_Pi
      | [ |- GEq ?P ?psi (a_CPi ?psi2 ?a ?b) (a_CPi ?psi3 ?a2 ?b2) ] => pick fresh x and apply GEq_CPi
      | [ |- GEq ?P ?psi (a_UAbs ?psi2 ?b) (a_UAbs ?psi3 ?b3) ] => pick fresh x and apply GEq_Abs
      | [ |- GEq ?P ?psi (a_UCAbs ?psi2 ?b) (a_UCAbs ?psi3 ?b3) ] => pick fresh x and apply GEq_CAbs
    end.



Lemma Grade_narrowing :
  (forall P psi a, Grade P psi a -> forall P', P_sub P' P -> Grade P' psi a) /\
  (forall P psi psi0 a, CGrade P psi psi0 a -> forall P', P_sub P' P -> CGrade P' psi psi0 a) /\
  (forall P psi phi, CoGrade P psi phi  -> forall P', P_sub P' P -> CoGrade P' psi phi).
Proof. 
  apply CGrade_Grade_mutual.
  all : intros; eauto using P_sub_uniq1.
  all: try solve [fresh_apply_Grade x; eauto;
    repeat spec x;
    qauto l: on ctrs: P_sub use: q_leb_refl].
  - (* Var *)
    hauto lq: on use: P_sub_binds, q_leb_trans, P_sub_uniq1 ctrs: Grade.
Qed.

Lemma CEq_GEq_narrowing : 
  (forall P psi psi0 a b,
  CEq P psi psi0 a b -> forall P', P_sub P' P -> CEq P' psi psi0 a b) /\
  (forall P psi a b,
  GEq P psi a b -> forall P', P_sub P' P -> GEq P' psi a b) /\
  (forall P psi phi1 phi2,
   CoGEq P psi phi1 phi2 -> forall P', P_sub P' P -> CoGEq P' psi phi1 phi2).
Proof. 
  apply CEq_GEq_mutual.
  all: intros; eauto using P_sub_uniq1.
  all: try solve [fresh_apply_GEq x; eauto;
    repeat spec x;
    qauto l: on ctrs: P_sub use: q_leb_refl] .
  - hauto lq: on use: P_sub_binds, q_leb_trans, P_sub_uniq1 ctrs: GEq.
Qed.

Lemma GEq_narrowing : forall P phi a b,
  GEq P phi a b -> forall P', P_sub P' P -> GEq P' phi a b.
Proof. apply CEq_GEq_narrowing; eauto. Qed.

Lemma CEq_narrowing : forall P psi psi0 a b,
    CEq P psi psi0 a b -> forall P', P_sub P' P -> CEq P' psi psi0 a b.
Proof. hauto use: CEq_GEq_narrowing. Qed.

Lemma CoGEq_narrowing : forall P psi phi1 phi2,
   CoGEq P psi phi1 phi2 -> forall P', P_sub P' P -> CoGEq P' psi phi1 phi2.
Proof. hauto use: CEq_GEq_narrowing. Qed.

Lemma Par_narrowing : 
  (  forall P1 psi a b, Par P1 psi a b -> forall P2, P_sub P2 P1 -> Par P2 psi a b) /\
  (  forall P1 psi phi1 phi2, ParProp P1 psi phi1 phi2 -> forall P2, P_sub P2 P1 -> ParProp P2 psi phi1 phi2) /\
  (  forall P1 psi psi0 a b, CPar P1 psi psi0 a b -> forall P2, P_sub P2 P1 -> CPar P2 psi psi0 a b) /\
  (  forall P1 psi psi0 phi1 phi2, CParProp P1 psi psi0 phi1 phi2 -> forall P2, P_sub P2 P1 -> CParProp P2 psi psi0 phi1 phi2).
Proof. 
  apply Par_tm_constraint_mutual.
  all : intros; pick fresh x;
    try hauto
          use:Grade_narrowing, GEq_narrowing, CPar_Nleq, P_sub_uniq1, q_leb_refl
          ctrs: P_sub, Par, CPar,ParProp,CParProp.
  apply Par_Pi with (L := dom P2 \u dom P \u L); qauto l: on use: q_leb_refl ctrs: P_sub.
  apply Par_CPi with (L := dom P2 \u dom P \u L); qauto l: on use: q_leb_refl ctrs: P_sub.
Qed.
(* for the record: the coqhammer+coq version I'm using: 1.3.2+8.15 *)

(* Lemma typing_erased_mutual: *)
(*     (forall G b A, Typing G b A -> erased_tm b) /\ *)
(*     (forall G0 phi (H : PropWff G0 phi), erased_constraint phi) /\ *)
(*      (forall G0 D p1 p2 (H : Iso G0 D p1 p2), True ) /\ *)
(*      (forall G0 D phi (H : DefEq G0 D phi), True) /\ *)
(*      (forall G0 (H : Ctx G0), True) *)

(* Lemma Typing_narrowing_mutual : *)
(*   (forall G1 psi b A, Typing G1 psi b A -> forall G2, ctx_sub G2 G1 -> ) *)


(* Lemma DefEq_narrowing :  *)
(* (forall P phi psi a b, *)
(*   CDefEq P phi psi a b -> forall P', P_sub P' P -> CDefEq P' phi psi a b) /\ *)
(* (forall P phi a b, *)
(*   DefEq P phi a b -> forall P', P_sub P' P -> DefEq P' phi a b). *)
(* Proof. *)
(*   move: (Grade_narrowing) => [ _ gn]. *)
(*   eapply CDefEq_DefEq_mutual. *)
(*   all: intros P phi a b h. *)
(*   all: intros; eauto 3 using P_sub_uniq1. *)
(*   all: try solve [fresh_apply_DefEq x; auto; *)
(*     repeat spec x; *)
(*     match goal with [ H : forall P', P_sub P' ?P -> _ |- _] => eapply H end; *)
(*     econstructor; eauto; *)
(*     reflexivity]. *)

(*   all: try solve repeat spec x; *)
(*     match goal with [ H : forall P', P_sub P' ?P -> _ |- _] => eapply H end; *)
(*     econstructor; eauto; *)
(*     reflexivity. *)

(*   eapply Eq_Trans; eauto. *)
(*   eapply Eq_Beta; eauto. *)
(*   eapply Eq_App; eauto.  *)
(*   eapply Eq_PiSnd; eauto. *)
(*   eapply Eq_WSigmaSnd; eauto. *)
(*   eapply Eq_WPair; eauto. *)
(*   eapply Eq_SSigmaSnd; eauto. *)
(*   eapply Eq_SPair; eauto. *)
(*   eapply Eq_Sum; eauto. *)
(*   eapply Eq_Case; eauto. *)

(* Qed. *)



(* Lemma Typing_narrowing : forall psi a A W1,  *)
(*     Typing W1 psi a A -> *)
(*     forall W2, ctx_sub W2 W1 -> *)
(*     Typing W2 psi a A. *)
(* Proof with eauto using ctx_sub_meet_ctx_l. *)
(*   induction 1; intros... *)
(*   all: try  move: (ctx_sub_uniq ltac:(eassumption) ltac:(eassumption)) => uu.  *)
(*   all: eauto 3. *)
(*   all: try solve [ *)
(*                  fresh_apply_Typing x;  *)
(*                  eauto using po_join_r, ctx_sub_meet_ctx_l; *)
(*                  repeat spec x; *)
(*                  eapply H4; *)
(*                  econstructor; eauto; *)
(*                  reflexivity ]. *)
(*   - (* conv *) *)
(*     have S: ctx_sub (meet_ctx_l q_C W2) (meet_ctx_l q_C W). eauto...  *)
(*     move: (ctx_sub_labels S) => Eq.  *)
(*     eapply T_Conv; eauto 2. *)
(*     eapply DefEq_narrowing; eauto. *)
(*   - (* Var *) *)
(*     move: (ctx_sub_binds ltac:(eauto) ltac:(eauto)) => [psi1 [h1 h2]]. *)
(*     eapply T_Var with (psi0 := psi1); eauto using ctx_sub_uniq. *)
(*     transitivity psi0; auto. *)
(*   - (* Pi *) *)
(*     fresh_apply_Typing x;  *)
(*     eauto using po_join_r, ctx_sub_meet_ctx_l; *)
(*     repeat spec x. *)
(*     eapply H3; *)
(*     econstructor; eauto; *)
(*     reflexivity . *)
(*   - (* WPair *) *)
(*     eapply T_WPair... *)
(*   - (* WPairI *) *)
(*     eapply T_WPairIrrel... *)
(*   - (* LetPair *) *)
(*     fresh_apply_Typing x;  *)
(*     eauto using po_join_r, ctx_sub_meet_ctx_l. *)
(*     + clear H2 H3. repeat spec x. eapply H2; econstructor; eauto.  *)
(*       reflexivity. eapply ctx_sub_meet_ctx_l; auto. *)
(*       rewrite dom_meet_ctx_l. auto. *)
(*       rewrite dom_meet_ctx_l. auto. *)
(*     + move=> y Fry. *)
(*       clear H H0 H2. *)
(*       spec x. spec y. *)
(*       eapply H0. econstructor; eauto. reflexivity. *)
(*   - (* SPair *) *)
(*     eapply T_SPair... *)
(*   - (* case *) *)
(*     fresh_apply_Typing x; eauto using po_join_r, ctx_sub_meet_ctx_l. *)
(*     repeat spec x. *)
(*     eapply H2. *)
(*     econstructor; eauto; try reflexivity. *)
(*     eapply ctx_sub_meet_ctx_l; auto. *)
(*     rewrite dom_meet_ctx_l. auto. *)
(*     rewrite dom_meet_ctx_l. auto. *)
(* Qed. *)
