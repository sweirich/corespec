(* Weakening for grade *)
Require Export FcEtt.imports.
Require Export FcEtt.tactics.
Require Export FcEtt.labels. 
Require Export FcEtt.ett_ind.
Require Export FcEtt.uniq. 
Require Import FcEtt.ett_ind.

Set Implicit Arguments.
Open Scope grade_scope.

Local Ltac weakening_ih := 
    match goal with 
    | [ H3 : forall P5 P4, [(?x, ?psi0)] ++ ?P2 ++ ?P1 = P4 ++ P5 -> _ |- _ ]
     => specialize (H3 P1 (x ~ psi0 ++ P2) ltac:(eauto) ltac:(simpl_env;auto)); simpl_env in H3
     end.


Ltac fresh_apply_Grade x := 
  match goal with 
      | [ |- Grade ?P ?psi (a_Pi ?psi2 ?a ?b) ] => pick fresh x and apply G_Pi
      | [ |- Grade ?P ?psi (a_UAbs ?psi2 ?b) ] => pick fresh x and apply G_Abs
      | [ |- Grade ?P ?psi (a_CPi ?psi2 ?a ?b) ] => pick fresh x and apply G_CPi
      | [ |- Grade ?P ?psi (a_UCAbs ?psi2 ?b) ] => pick fresh x and apply G_CAbs
    end.

Lemma concat_ECtx : forall P P1, uniq (P ++ P1) -> ECtx P -> ECtx P1 -> ECtx (P ++ P1).
Proof.
  intros.
  dependent induction H0; sauto lq: on rew: off.
Qed.

Lemma ECtx_concat : forall P P1, ECtx (P ++ P1) -> ECtx P /\ ECtx P1.
Proof.
  intros H.
  dependent induction H.
  - sfirstorder.
  - destruct a.
    destruct p.
    destruct e.
    + intros; split.
      inversion H0; subst.
      constructor; auto.
      move : (IHlist P1). sfirstorder.
      qauto l:on inv:ECtx.
    + intros; split.
      inversion H0; subst.
      constructor; auto.
      move : (IHlist P1). sfirstorder.
      qauto l:on inv:ECtx.
Qed.

(* a trivial version of weakening *)
Lemma ECtx_weakening_middle : forall P P1 P2, ECtx (P ++ P1 ++ P2) -> ECtx (P ++ P2).
Proof.
  move => P P1 P2 H.
  have h0 : ECtx P /\ (ECtx (P1 ++ P2)). sfirstorder use:ECtx_concat.
  split_hyp.
  have h1 : ECtx P1 /\ ECtx P2. hauto lq:on use:ECtx_concat.
  split_hyp.
  hauto lq: on use: uniq_remove_mid, concat_ECtx, ECtx_uniq.
Qed.

Lemma CGrade_Grade_weakening_middle : (forall P psi b,
    Grade P psi b -> forall P1 P2, P = P2 ++ P1 -> forall P3,
     uniq (P2 ++ P3 ++ P1) 
    -> Grade (P2 ++ P3 ++ P1) psi b) /\
    (forall P psi psi0 b,
    CGrade P psi psi0 b -> forall P1 P2, P = P2 ++ P1 -> forall P3,
     uniq (P2 ++ P3 ++ P1) 
    -> CGrade (P2 ++ P3 ++ P1) psi psi0 b)
     /\ (forall P psi phi,
     CoGrade P psi phi -> forall P1 P2, P = P2 ++ P1 -> forall P3,
     uniq (P2 ++ P3 ++ P1)
    -> CoGrade (P2 ++ P3 ++ P1) psi phi).
Proof.
  apply CGrade_Grade_mutual.
  all: intros; eauto.
  all: try solve [subst; eapply G_Var; eauto].
  all: try solve 
        [subst; fresh_apply_Grade x; eauto;
         repeat spec x;
         weakening_ih;
         eauto].
Qed. 

Lemma Grade_weakening_middle : forall P1 P2 P3 psi b,
    Grade (P2 ++ P1) psi b -> uniq (P2 ++ P3 ++ P1) 
    -> Grade (P2 ++ P3 ++ P1) psi b.     
Proof. 
  intros.   eapply CGrade_Grade_weakening_middle; eauto. Qed.

Lemma Grade_weakening : forall P2 P1 psi b,
    Grade P1 psi b
    -> uniq (P2 ++ P1) 
    -> Grade (P2 ++ P1) psi b.     
Proof. 
  intros.
  eapply CGrade_Grade_weakening_middle with (P2 := nil); simpl_env; eauto.
Qed.


Ltac geq_weakening_ih := 
    match goal with 
    | [ H3 : forall P3 P4, [(?x, ?psi0)] ++ ?P2 ++ ?P1 = P4 ++ P3 -> _ |- _ ]
     => specialize (H3 P1 ([(x,psi0)] ++ P2) ltac:(eauto) _ ltac:(simpl_env;eauto)); simpl_env in H3
     end.

Lemma CEq_GEq_weakening : 
  (forall P phi psi0 a b,
  CEq P phi psi0 a b -> forall P1 P2, P = P2 ++ P1 -> forall P3, uniq (P2 ++ P3 ++ P1) -> CEq (P2 ++ P3 ++ P1) phi psi0 a b) /\
  (forall P psi a b,
  GEq P psi a b -> forall P1 P2, P = P2 ++ P1 -> forall P3, uniq (P2 ++ P3 ++ P1) -> GEq (P2 ++ P3 ++ P1) psi a b) /\
  (forall P psi phi1 phi2,
  CoGEq P psi phi1 phi2 -> forall P1 P2, P = P2 ++ P1 -> forall P3, uniq (P2 ++ P3 ++ P1) -> CoGEq (P2 ++ P3 ++ P1) psi phi1 phi2).
Proof.
  apply CEq_GEq_mutual.
  all: intros; eauto.
  all: try solve [subst; eapply GEq_Var; eauto].
  all: try solve [subst;
    fresh_apply_GEq x; eauto;
    repeat spec x;
    geq_weakening_ih;
    eauto].
Qed.

Lemma GEq_weakening_middle :  (forall P phi a b,
  GEq P phi a b -> forall P1 P2, P = P2 ++ P1 -> forall P3, uniq (P2 ++ P3 ++ P1) -> GEq (P2 ++ P3 ++ P1) phi a b).
Proof.
  sfirstorder use:CEq_GEq_weakening.
Qed.


Lemma GEq_weakening : forall P phi b1 b2,
  GEq P phi b1 b2 -> forall P2, uniq (P2 ++ P) -> GEq (P2 ++ P) phi b1 b2. 
Proof.
  pose proof CEq_GEq_weakening.
  split_hyp.
  intros.
  eapply H0 with (P2 := nil); eauto.
Qed.

(* TODO: prove this in ext_weakening *)
(* Lemma CDefEq_DefEq_weakening_middle :  *)
(*   (forall P psi psi0 a b, *)
(*   CDefEq P psi psi0 a b -> forall P1 P2, P = P2 ++ P1 -> forall P3, uniq (P2 ++ P3 ++ P1) -> CDefEq (P2 ++ P3 ++ P1) psi psi0 a b) /\ *)
(*   (forall P psi a b, *)
(*   DefEq P psi a b -> forall P1 P2, P = P2 ++ P1 -> forall P3, uniq (P2 ++ P3 ++ P1) -> DefEq (P2 ++ P3 ++ P1) psi a b) *)
(* Proof. *)
(*   apply CDefEq_DefEq_mutual. *)
(*   all: intros; subst; eauto 3 using Grade_weakening_middle. *)
(*   all: try solve [subst; *)
(*     fresh_apply_DefEq x; auto; *)
(*     repeat spec x; *)
(*     geq_weakening_ih; *)
(*     eauto]. *)
(*   all: try solve [ *)
(*              pick fresh x and apply Eq_SubstIrrel; eauto 2; *)
(*              repeat spec x; *)
(*              geq_weakening_ih; *)
(*              eauto]. *)

(*   all: eauto 4 using Grade_weakening_middle. *)
(*   all: try (eapply Eq_Case; eauto 3 using Grade_weakening_middle). *)
(* Qed. *)

(* Lemma DefEq_weakening_middle :  *)
(*   (forall P phi a b, *)
(*   DefEq P phi a b -> forall P1 P2, P = P2 ++ P1 -> forall P3, uniq (P2 ++ P3 ++ P1) -> DefEq (P2 ++ P3 ++ P1) phi a b). *)
(* Proof.  *)
(*   intros. *)
(*   eapply CDefEq_DefEq_weakening_middle; eauto. *)
(* Qed. *)

(* Lemma DefEq_weakening : forall P phi b1 b2, *)
(*   DefEq P phi b1 b2 -> forall P2, uniq (P2 ++ P) -> DefEq (P2 ++ P) phi b1 b2.  *)
(* Proof. *)
(*   intros. *)
(*   eapply CDefEq_DefEq_weakening_middle with (P2 := nil); eauto. *)
(* Qed. *)

  (* (forall P psi a b, Par P psi a b -> uniq P) /\  *)
  (*   (forall P psi phi1 phi2, ParProp P psi phi1 phi2 -> uniq P) /\ *)
  (* (forall P psi psi0 a b, CPar P psi psi0 a b -> uniq P) /\  *)
  (* (forall P psi psi0 phi1 phi2, CParProp P psi psi0 phi1 phi2 -> uniq P). *)


Ltac fresh_apply_Par x := 
  match goal with 
      | [ |- Par ?P ?psi (a_Pi ?psi2 ?a ?b) (a_Pi ?psi3 ?a2 ?b2) ] => pick fresh x and apply Par_Pi
      | [ |- Par ?P ?psi (a_UAbs ?psi2 ?b) (a_UAbs ?psi3 ?b3) ] => pick fresh x and apply Par_Abs
      | [ |- Par ?P ?psi (a_CPi ?psi2 ?a ?b) (a_CPi ?psi3 ?a2 ?b2) ] => pick fresh x and apply Par_CPi
      | [ |- Par ?P ?psi (a_UCAbs ?psi2 ?b) (a_UCAbs ?psi3 ?b3) ] => pick fresh x and apply Par_CAbs
    end.


Lemma CPar_Par_weakening_middle :
  (forall G0 psi a b, Par G0 psi a b ->
                 forall E F G, (G0 = F ++ G) -> uniq (F ++ E ++ G) ->  Par (F ++ E ++ G) psi a b) /\
  (forall G0 psi phi1 phi2, ParProp G0 psi phi1 phi2 -> forall E F G, (G0 = F ++ G) -> uniq (F ++ E ++ G) ->  ParProp (F ++ E ++ G) psi phi1 phi2) /\
  (forall G0 psi psi0 a b, CPar G0 psi psi0 a b ->
  forall E F G, (G0 = F ++ G) -> uniq (F ++ E ++ G) ->  CPar (F ++ E ++ G) psi psi0 a b) /\
  (forall G0 psi psi0 phi1 phi2, CParProp G0 psi psi0 phi1 phi2 -> forall E F G, (G0 = F ++ G) -> uniq (F ++ E ++ G) ->  CParProp (F ++ E ++ G) psi psi0 phi1 phi2).
Proof.
  apply Par_tm_constraint_mutual.
  all: intros; subst; eauto 3 using Grade_weakening_middle.
  all: try solve [
  subst; fresh_apply_Par x; auto; repeat spec x;
  match goal with 
  | [ H3 : forall E F0 G0, [(?x, ?psi0)] ++ ?F ++ ?G = F0 ++ G0 -> _ |- _ ]
    =>  specialize (H3 E ([(x,psi0)] ++ F) G ltac:(simpl_env;eauto) ltac:(simpl_env;eauto)) ;
  simpl_env in H3 end; eauto].
  all: eauto 5 using Grade_weakening_middle.
Qed.

Lemma Par_weakening_middle :
  forall G0 a psi b, Par G0 psi a b ->
  forall E F G, (G0 = F ++ G) -> uniq (F ++ E ++ G) ->  Par (F ++ E ++ G) psi a b.
Proof. 
  intros. eapply CPar_Par_weakening_middle; eauto.
Qed.


Lemma Par_weakening :
  forall G a psi b, Par G psi a b ->
  forall E, uniq (E ++ G) ->  Par (E ++ G) psi a b.
Proof.
  intros. eapply Par_weakening_middle with (F := nil); eauto.
Qed.



(* TODO: prove these mutually recursively in ext_weak *)
(* Lemma Typing_weakening_middle : forall W2 W1 q b B,  *)
(*     Typing (W2 ++ W1) q b B -> *)
(*     forall W, uniq (W2 ++ W ++ W1) -> *)
(*     Typing (W2 ++ W ++ W1) q b B. *)
(* Proof. *)
(*   intros W2 W1 q b B h. dependent induction h. *)
(*   all: intros; subst; eauto 3 using DefEq_weakening_middle. *)
(*   all: have UL1: uniq (meet_ctx_l q_C W2 ++ meet_ctx_l q_C W ++ meet_ctx_l q_C W1) by *)
(*     unfold meet_ctx_l; solve_uniq. *)
(*   all: have UL2: uniq (labels (meet_ctx_l q_C W2) ++ labels (meet_ctx_l q_C W) ++ labels (meet_ctx_l q_C W1)) by *)
(*    unfold labels; solve_uniq. *)
(*   (* easy cases *) *)
(*   all: try solve [eapply T_App; eauto]. *)
(*   all: try solve [ *)
(*              eapply T_AppIrrel; simpl_env; eauto; *)
(*              eapply IHh2; simpl_env; eauto]. *)
(*   all: try solve [ *)
(*              eapply T_WPair; simpl_env; eauto; *)
(*              eapply IHh1; simpl_env; eauto]. *)
(*   all: try solve [ *)
(*              eapply T_WPairIrrel; simpl_env; eauto; *)
(*              try eapply IHh1; simpl_env; eauto; *)
(*              try eapply IHh2; simpl_env; eauto]. *)
(*   all: try solve [ *)
(*              eapply T_SPair; simpl_env; eauto; *)
(*              try eapply IHh1; simpl_env; eauto; *)
(*              try eapply IHh2; simpl_env; eauto]. *)
(*   all: try solve [ *)
(*              apply T_Sum; simpl_env; eauto; *)
(*              try eapply IHh1; simpl_env; eauto; *)
(*              try eapply IHh2; simpl_env; eauto]. *)
(*   all: try solve [ *)
(*              eapply T_Inj1; simpl_env; eauto; *)
(*              eapply IHh2; simpl_env; eauto]. *)
(*   all: try solve [ *)
(*              eapply T_Inj2; simpl_env; eauto; *)
(*              eapply IHh2; simpl_env; eauto]. *)
(*   all: try solve [eapply T_Eq; simpl_env; eauto]. *)
  
(*   (* conversion *) *)
(*   all: try match goal with [ H : DefEq _ _ _ _ |- _ ] =>  *)
(*                   eapply T_Conv; eauto 3; *)
(*                     simpl_env in *; *)
(*                     try eapply DefEq_weakening_middle; eauto end. *)

(*   (* pi *) *)
(*   subst; fresh_apply_Typing x; eauto 1; auto; repeat spec x; *)
(*   match goal with  *)
(*   | [ H2 : forall F0 G0, [(?x, ?psi0)] ++ ?F ++ ?G ~= F0 ++ G0 -> _ |- _ ] *)
(*     => specialize (H2 ([(x,psi0)] ++ F) G ltac:(simpl_env;eauto 3)); *)
(*   simpl_env in H2; eauto 3; try eapply H2; try solve_uniq end. *)

(*   (* abs *) *)
(*   subst; fresh_apply_Typing x; simpl_env; try eapply IHh; simpl_env; eauto; repeat spec x; *)
(*   try match goal with  *)
(*   | [ H3 : forall F0 G0, [(?x, ?psi0)] ++ ?F ++ ?G ~= F0 ++ G0 -> _ |- _ ] *)
(*     => specialize (H3 ([(x,psi0)] ++ F) G ltac:(simpl_env;eauto 3) W) ; *)
(*   simpl_env in H3 ; eauto 3; try eapply H3 end.  *)

(*   (* wsigma *) *)
(*   subst; fresh_apply_Typing x; eauto 1; auto; repeat spec x; *)
(*   match goal with  *)
(*   | [ H3 : forall F0 G0, [(?x, ?psi0)] ++ ?F ++ ?G ~= F0 ++ G0 -> _ |- _ ] *)
(*     => specialize (H3 ([(x,psi0)] ++ F) G ltac:(simpl_env;eauto 3)) ; *)
(*   simpl_env in H3; eauto 3; try eapply H3; try solve_uniq end. *)

(*   (* letpair *) *)
(*   - subst; fresh_apply_Typing x. *)
(*     + clear H H1 H2 IHh. *)
(*     repeat spec x. simpl_env. *)
(*     match goal with  *)
(*     | [ H3 : forall F0 G0, [(?x, ?psi0)] ++ meet_ctx_l q_C (?F ++ ?G) ~= F0 ++ G0 -> _ |- _ ]  *)
(*       => specialize (H3 ([(x,psi0)] ++ meet_ctx_l q_C F) (meet_ctx_l q_C G) ltac:(simpl_env;eauto 3) (meet_ctx_l q_C W)); *)
(*           simpl_env in H3; eapply H3 end. *)
(*     eapply uniq_cons_3; auto. repeat rewrite dom_app. repeat rewrite dom_meet_ctx_l. auto. *)
(*     + eapply IHh; auto. *)
(*     + move => y Fry. *)
(*       clear H H0 H1 IHh. *)
(*       spec x. spec y. *)
(*       specialize (H0 ([(x, (psi0 * psi,A))] ++ W2) W1 ltac:(simpl_env; auto) W). *)
(*       simpl_env in H0. eapply H0. solve_uniq. *)

(*   (* ssigma *) *)
(*   - subst; fresh_apply_Typing x; eauto 1; auto; repeat spec x; *)
(*       match goal with  *)
(*       | [ H3 : forall F0 G0, [(?x, ?psi0)] ++ ?F ++ ?G ~= F0 ++ G0 -> _ |- _ ] *)
(*         => specialize (H3 ([(x,psi0)] ++ F) G ltac:(simpl_env;eauto 3)) ; *)
(*             simpl_env in H3; eauto 3; try eapply H3; try solve_uniq end. *)
(*   - (* case *)  *)
(*     fresh_apply_Typing x; auto. *)
(*     repeat spec x. *)
(*     simpl_env. *)
(*     match goal with  *)
(*     | [ H3 : forall F0 G0, [(?x, ?psi0)] ++ meet_ctx_l q_C (?F ++ ?G) ~= F0 ++ G0 -> _ |- _ ] *)
(*       => specialize (H3 ([(x,psi0)] ++ meet_ctx_l q_C F) (meet_ctx_l q_C G) ltac:(simpl_env;eauto 3) *)
(*                    (meet_ctx_l q_C W)); *)
(*           simpl_env in H3 ; eapply H3 end. *)
(*     eapply uniq_cons_3; auto. repeat rewrite dom_app. repeat rewrite dom_meet_ctx_l. auto. *)
(* Qed.     *)

(* Lemma Typing_weakening : forall W1 q b B,  *)
(*     Typing W1 q b B -> *)
(*     forall W2, uniq (W2 ++ W1) ->  *)
(*     Typing (W2 ++ W1) q b B. *)
(* Proof.  *)
(*   intros. *)
(*   eapply Typing_weakening_middle with (W2 := nil); simpl_env; eauto. *)
(* Qed. *)

