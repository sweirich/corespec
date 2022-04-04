Require Import FcEtt.tactics.
Require Import FcEtt.grade_sig.
Require Import FcEtt.utils.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
(* Require Export FcEtt.ett_par. *)
Require Export FcEtt.ett_ind.
Require Export FcEtt.subsumption.
Require Export FcEtt.ext_wf.
Require Import FcEtt.ett_ind.

(* Module ext_weak (wf: ext_wf_sig). *)

(* Include wf. *)

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Ltac binds_cons :=
  let H5 := fresh in
  match goal with
    [
      H4 : (∃ phi : constraint, binds ?x (Co phi) ?G) → False
      |- ((exists phi, binds ?x (Co phi) ([(?y, ?s)] ++ ?G)) -> False) ] =>
    intro H5; destruct H5; apply H4; simpl in H5;
    destruct (binds_cons_1 _ x y _ s G H5); split_hyp; subst;
    try done; eauto
  end.


Lemma typing_meet_ctx_l_C : forall G psi b B,
    Typing G psi b B ->
    Typing (meet_ctx_l q_C G) q_C b B.
Proof.
  move => G psi b B H.
  have h0 : psi <= q_C by sfirstorder use:Typing_leq_C.
  hauto use:Typing_meet_ctx_l, Typing_subsumption, q_leb_refl.
Qed.

Lemma propwff_meet_ctx_l_C : forall G psi phi,
    PropWff G psi phi ->
    PropWff (meet_ctx_l q_C G) q_C phi.
Proof.
  move => G psi phi H.
  have h0 : psi <= q_C by sfirstorder use:Typing_leq_C.
  sfirstorder use:PropWff_meet_ctx_l, Typing_subsumption_mutual, q_leb_refl.
Qed.

Lemma Ctx_meet_l_C : forall {G} , Ctx G -> Ctx (meet_ctx_l q_C G).
Proof.
  induction 1; simpl; constructor; auto;
    hauto lq:on use:meet_ctx_l_meet_ctx_l, dom_meet_ctx_l.
Qed.
  
Lemma weakening_helper_typing : forall {F E G0 a A}
  (H0 : ∀ E F0 G : list (atom * (grade * sort)),
      meet_ctx_l q_C (F ++ G0) = F0 ++ G → Ctx (F0 ++ E ++ G) → Typing (F0 ++ E ++ G) q_C a A),
  Ctx (F ++ E ++ G0) ->
  Typing (meet_ctx_l q_C (F ++ E ++ G0)) q_C a A.
Proof.
  intros.
  simpl_env.
    apply H0; auto.
    hauto q: on simp: simpl_env.
    move : (Ctx_meet_l_C H) => h0.
    simpl_env in h0.
    assumption.
Qed.

Lemma weakening_helper_defeq : forall {F E G0 psi phi }
  (H0 : ∀ E F0 G : list (atom * (grade * sort)),
      meet_ctx_l q_C (F ++ G0) = F0 ++ G → Ctx (F0 ++ E ++ G) → DefEq (F0 ++ E ++ G) psi phi),
  Ctx (F ++ E ++ G0) ->
  DefEq (meet_ctx_l q_C (F ++ E ++ G0)) psi phi.
Proof.
  intros.
  simpl_env.
    apply H0; auto.
    hauto q: on simp: simpl_env.
    move : (Ctx_meet_l_C H) => h0.
    simpl_env in h0.
    assumption.
Qed.

Lemma weakening_helper_cdefeq : forall {F E psi0 G0 A B T}
  (H0 : ∀ E F0 G : list (atom * (grade * sort)),
      meet_ctx_l q_C (F ++ G0) = F0 ++ G → Ctx (F0 ++ E ++ G) → CDefEq (F0 ++ E ++ G) q_C psi0 A B T),
  Ctx (F ++ E ++ G0) ->
  CDefEq (meet_ctx_l q_C (F ++ E ++ G0)) q_C psi0 A B T.
Proof.
  intros.
  simpl_env.
    apply H0; auto.
    hauto q: on simp: simpl_env.
    move : (Ctx_meet_l_C H) => h0.
    simpl_env in h0.
    assumption.
Qed.

Lemma weakening_helper_propwff : forall {F E G0 phi}
  (H0 : ∀ E F0 G : list (atom * (grade * sort)),
      meet_ctx_l q_C (F ++ G0) = F0 ++ G → Ctx (F0 ++ E ++ G) → PropWff (F0 ++ E ++ G) q_C phi),
  Ctx (F ++ E ++ G0) ->
  PropWff (meet_ctx_l q_C (F ++ E ++ G0)) q_C phi.
Proof.
  intros.
  simpl_env.
    apply H0; auto.
    hauto q: on simp: simpl_env.
    move : (Ctx_meet_l_C H) => h0.
    simpl_env in h0.
    assumption.
Qed.

Lemma typing_weakening_mutual:
  (forall G0 psi a A,     Typing G0 psi a A ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> Typing (F ++ E ++ G) psi a A) /\
  (forall G0 psi phi,     PropWff G0 psi phi ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> PropWff (F ++ E ++ G) psi phi) /\
  (forall G0 psi p1 p2, Iso G0 psi p1 p2 ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> Iso (F ++ E ++ G) psi p1 p2) /\
  (forall G0 psi phi, DefEq G0 psi phi ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> DefEq (F ++ E ++ G) psi phi) /\
  (forall G0,         Ctx G0 ->
     True) /\
  (forall G0 psi psi0 A B T, CDefEq G0 psi psi0 A B T ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> CDefEq (F ++ E ++ G) psi psi0 A B T) /\
  (forall G0 psi a A,     CTyping G0 psi a A ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> CTyping (F ++ E ++ G) psi a A).
Proof.
  ext_induction CON.
  all: intros; subst; try done.
  all: try solve [eapply CON; eauto 2 using
                    weakening_helper_typing,
                    weakening_helper_defeq,
                    weakening_helper_propwff].
  (* Pi *)
  - pick fresh y and apply CON; auto.
    rewrite_env ((y ~ (psi, Tm A) ++ F) ++ E ++ G0).
    apply_first_hyp; auto.
    simpl_env.
    constructor; auto 1.
    sfirstorder use:typing_meet_ctx_l_C.
  (* Abs *)
  - pick fresh y and apply CON; spec y ; auto.
    rewrite_env ((y ~ (psi0 * psi, Tm A) ++ F) ++ E ++ G0).
    apply_first_hyp; auto.
    simpl_env.
    constructor; auto 1.
    sfirstorder use:weakening_helper_typing.
    sfirstorder use:weakening_helper_typing.
  (* CPi *)
  - pick fresh y and apply CON; auto.
    rewrite_env ((y ~ (psi, Co phi) ++ F) ++ E ++ G0).
    apply_first_hyp; auto.
    simpl_env.
    constructor; auto 1.
    sfirstorder use:propwff_meet_ctx_l_C.
  (* CAbs *)
  - pick fresh y and apply CON; auto.
    rewrite_env ((y ~ (psi0 * psi, Co phi) ++ F) ++ E ++ G0).
    apply_first_hyp; auto.
    simpl_env.
    constructor; auto 1.
    sfirstorder use:weakening_helper_propwff.
    sfirstorder use:weakening_helper_propwff.
  (* WffImpl *)
  - pick fresh y and apply CON; auto.
    rewrite_env ((y ~ (psi, Co phi1) ++ F) ++ E ++ G0).
    apply_first_hyp; auto.
    simpl_env.
    constructor; auto 1.
    hauto lq: on use: propwff_meet_ctx_l_C.
  - pick fresh y and apply CON; auto.
    rewrite_env ((y ~ (q_Top, Co phi1) ++ F) ++ E ++ G0).
    apply_first_hyp; auto.
    simpl_env.
    constructor; auto 1.
    hauto lq:on use:propwff_meet_ctx_l_C.
  (* PiCong *)
  - pick fresh y and apply CON; auto.
    rewrite_env ((y ~ (psi, Tm A1) ++ F) ++ E ++ G0).
    apply_first_hyp; auto.
    simpl_env.
    constructor; auto 1.
    sfirstorder use:typing_meet_ctx_l_C.
  (* AbsCong *)
  - pick fresh y and apply CON; spec y ; auto.
    rewrite_env ((y ~ (psi0, Tm A1) ++ F) ++ E ++ G0).
    apply_first_hyp; auto.
    simpl_env.
    constructor; auto 1.
    sfirstorder use:weakening_helper_typing.
    sfirstorder use:weakening_helper_typing.
  (* CPiCong *)
  - pick fresh y and apply CON; auto.
    rewrite_env ((y ~ (q_Top, Co phi1) ++ F) ++ E ++ G0).
    apply_first_hyp; auto.
    simpl_env.
    constructor; auto 1.
    sfirstorder use:propwff_meet_ctx_l_C.
  - pick fresh y and apply CON; spec y ; auto.
    rewrite_env ((y ~ (q_Top, Co phi1) ++ F) ++ E ++ G0).
    apply_first_hyp; auto.
    simpl_env.
    constructor; auto 1.
    sfirstorder use:weakening_helper_propwff.
    sfirstorder use:weakening_helper_propwff.
  (* Impl: won't go through because Impl's introduction rule is existential *)
  - pick fresh y and apply CON; spec y ; auto.
    rewrite_env ((y ~ (psi, Co phi1) ++ F) ++ E ++ G0).
    apply_first_hyp; auto.
    simpl_env.
    constructor; auto 1.
    sfirstorder use:weakening_helper_propwff.
    sfirstorder use:weakening_helper_propwff.
Qed.


Lemma Typing_weakening : ∀ (E F G: context) psi (a A : tm),  Typing (F ++ G) psi a A →  Ctx (F ++ E ++ G) ->
                                                          Typing (F ++ E ++ G) psi a A.
Proof. sfirstorder use:typing_weakening_mutual. Qed.

Lemma Typing_weakening_front : ∀ (E G: context) psi (a A : tm),  Typing G psi a A →  Ctx (E ++ G) ->
                                                          Typing (E ++ G) psi a A.
Proof.
  move => E G psi a A H0 H1.
  suff : Typing (nil ++ E ++ G) psi a A => //.
  hauto lq: on use: Typing_weakening.
Qed.

Lemma PropWff_weakening : forall (E F G : context) psi phi, PropWff (F ++ G) psi phi -> Ctx (F ++ E ++ G) → PropWff (F ++ E ++ G) psi phi.
Proof. sfirstorder use:typing_weakening_mutual. Qed.

Lemma Iso_weakening : ∀ (E F G : context) psi (p1 p2 : constraint),
       Iso (F ++ G) psi p1 p2 -> Ctx (F ++ E ++ G) → Iso (F ++ E ++ G) psi p1 p2.
Proof. sfirstorder use:typing_weakening_mutual. Qed.

Lemma DefEq_weakening : ∀ (E F G : context) psi phi,
    DefEq (F ++ G) psi phi → Ctx (F ++ E ++ G) → DefEq (F ++ E ++ G) psi phi.
Proof. sfirstorder use:typing_weakening_mutual. Qed.

(* I don't think anyone would want this *)
(* Lemma Ctx_weakening : ∀ (E F G: context), *)
(*        Ctx (F ++ G) → Ctx (F ++ E ++ G) → Ctx (F ++ E ++ G). *)
(* Proof. intros. apply (fifth typing_weakening_mutual) with (G0 := F ++ G)(F:=F)(E:=E)(G:=G); auto. Qed. *)


(* subsumed by the meet_ctx_l lemmas? *)
(* Lemma Iso_weakening_dom : *)
(*    ∀ (E F G : context) (D : available_props) (p1 p2 : constraint), *)
(*        Iso (F ++ G) (dom (F ++ G)) p1 p2 -> Ctx (F ++ E ++ G) → Iso (F ++ E ++ G) (dom(F ++ E ++ G)) p1 p2. *)
(* Proof. *)
(*   intros. *)
(*   eapply Iso_weaken_available. *)
(*   eapply Iso_weakening. *)
(*   eassumption. *)
(*   auto. *)
(* Qed. *)

(* Lemma DefEq_weakening_dom : ∀ (E F G : context) (D : available_props) (A B T : tm), *)
(*     DefEq (F ++ G) (dom (F ++ G)) A B T → Ctx (F ++ E ++ G) → DefEq (F ++ E ++ G) (dom (F ++ E ++ G)) A B T. *)
(* Proof. *)
(*   intros. *)
(*   eapply DefEq_weaken_available. *)
(*   eapply DefEq_weakening. *)
(*   eassumption. *)
(*   auto. *)
(* Qed. *)
