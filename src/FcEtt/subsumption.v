Require Import FcEtt.tactics.
Require Import FcEtt.utils.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.
Require Export FcEtt.labels.
Require Export FcEtt.grade_sig.
Require Import FcEtt.toplevel.
Require Import FcEtt.ext_wf.
Require Export FcEtt.pumping.
Open Scope grade_scope.

Lemma Typing_meet_ctx_l : forall G psi b B q,
    Typing G psi b B ->
    Typing (meet_ctx_l q G) psi b B.
Proof.
  scrush use: Typing_Ctx, meet_ctx_l_ctx_sub.
Qed.

Lemma Typing_pumping_front :  forall {psi b A x B psi0 F psi1} (H : Typing ([(x, (psi0, B))] ++  F) psi b A),
    psi1 <= psi -> 
    Typing ([(x, (psi0 * psi1, B))] ++ F) psi b A.
Proof. intros.
       rewrite_env (nil ++ [(x, (psi0 * psi1, B))] ++ F).
       rewrite_env (nil ++ x ~ (psi0, B) ++ F) in H.
       hauto l: on use: Typing_pumping_middle_mutual.
Qed.

(* Lemma DefEq_pumping_front :  forall {psi phi x B psi0 F psi1} (H : DefEq ([(x, (psi0, B))] ++  F) psi phi), *)
(*     psi1 <= psi ->  *)
(*     DefEq ([(x, (psi0 * psi1, B))] ++ F) psi phi. *)
(* Proof. intros. *)
(*        rewrite_env (nil ++ [(x, (psi0 * psi1, B))] ++ F). *)
(*        rewrite_env (nil ++ x ~ (psi0, B) ++ F) in H. *)
(*        hauto l: on use: Typing_pumping_middle_mutual. *)
(* Qed. *)

Lemma Typing_pumping_front2 :  forall {psi b A x B psi0 F psi1} (H : Typing ([(x, (psi0 * psi1, B))] ++  F) psi b A),
    psi1 <= psi ->
    Typing ([(x, (psi0 * psi, B))] ++ F) psi b A.
Proof. intros.
       rewrite_env (nil ++ [(x, (psi0 * psi, B))] ++ F).
       rewrite_env (nil ++ x ~ (psi0 * psi1, B) ++ F) in H.
       have h0 : (psi0 * psi1) * psi = psi0 * psi.
       rewrite <- join_assoc.
       rewrite (join_leq psi1 psi); auto.
       hauto lq: on drew: off use: Typing_pumping_middle_mutual, q_leb_refl.
Qed.

(* Lemma DefEq_pumping_front2 :  forall {psi phi x B psi0 F psi1} (H : DefEq ([(x, (psi0 * psi1, B))] ++  F) psi phi), *)
(*     psi1 <= psi -> *)
(*     DefEq ([(x, (psi0 * psi, B))] ++ F) psi phi. *)
(* Proof. intros. *)
(*        rewrite_env (nil ++ [(x, (psi0 * psi, B))] ++ F). *)
(*        rewrite_env (nil ++ x ~ (psi0 * psi1, B) ++ F) in H. *)
(*        have h0 : (psi0 * psi1) * psi = psi0 * psi. *)
(*        rewrite <- join_assoc. *)
(*        rewrite (join_leq psi1 psi); auto. *)
(*        hauto lq: on drew: off use: Typing_pumping_middle_mutual, q_leb_refl. *)
(* Qed. *)

(* Lemma DefEq_pumping_self : forall {psi phi x B psi0 F} (H : DefEq ([(x, (psi0, B))] ++  F) psi phi), *)
(*     psi0 <= psi ->  *)
(*     DefEq ([(x, (psi, B))] ++ F) psi phi. *)
(* Proof. *)
(*   intros. *)
(*   have h0 : psi <= psi by reflexivity. *)
(*   move : (DefEq_pumping_front H h0). *)
(*   rewrite join_leq; auto. *)
(* Qed. *)

Lemma Typing_pumping_self :  forall {psi b A x B psi0 F} (H : Typing ([(x, (psi0, B))] ++  F) psi b A),
    psi0 <= psi -> 
    Typing ([(x, (psi, B))] ++ F) psi b A.
Proof.
  intros.
  have h0 : psi <= psi by reflexivity.
  move : (Typing_pumping_front H h0).
  rewrite join_leq; auto.
Qed.

Lemma typing_subsumption_mutual :
  (forall G0 psi a A, Typing G0 psi a A -> forall psi', psi <= psi' -> psi' <= q_C -> Typing G0 psi' a A) /\
  (forall G0 psi phi,   PropWff G0 psi phi -> forall psi', psi <= psi' -> psi' <= q_C -> PropWff G0 psi' phi) /\
  (forall G0 psi p1 p2, Iso G0 psi p1 p2 -> True) /\
  (forall G0 psi phi,   DefEq G0 psi phi -> True) /\
  (forall G0, Ctx G0 -> True) /\
  (forall G0 psi psi0 a b A,CDefEq G0 psi psi0 a b A -> True).
Proof.
  ext_induction CON; intros.
  (* 44 goals *)
  all : eauto 3.
  (* 9 goals *)
  all : try solve [eapply CON; eauto 3 using q_leb_trans, leq_join_r].
  (* 7 goals *)
  (* the following tactic handles Pi and Abs *)
  all : try solve [pick fresh y and apply CON; 
                   sfirstorder depth:1 use:Typing_pumping_self,Typing_pumping_front2;
                   try pick fresh z; auto].
  (* 3 goals *)
  (* var *)
  - sfirstorder use:q_leb_trans.
  (* AppRel *)
  - eapply CON; sfirstorder depth:1 use: po_join_r, join_lub.
  (* Fam *)
  - hfcrush use: q_leb_trans.
Qed.
