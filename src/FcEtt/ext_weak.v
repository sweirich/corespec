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
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> CDefEq (F ++ E ++ G) psi psi0 A B T).
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
  (* PiCong *)
  - pick fresh y and apply CON; auto.
    rewrite_env ((y ~ (psi, Tm A1) ++ F) ++ E ++ G0).
    apply_first_hyp; auto.
    simpl_env.
    constructor; auto 1.
    sfirstorder use:typing_meet_ctx_l_C.
  (* AbsCong *)
  - pick fresh y and apply CON; spec y ; auto.
    rewrite_env ((y ~ (psi0 * psi, Tm A1) ++ F) ++ E ++ G0).
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
  - admit.
Admitted.    
    
    

 E_pick_fresh y; try auto_rew_env; apply_first_hyp; try simpl_env; eauto 3.
  constructor; auto.
  apply H0.
    
    all: try solve [E_pick_fresh y; try auto_rew_env; apply_first_hyp; try simpl_env; eauto 3].
    simpl_env.
  (*
  eapply E_LeftRel with (b:=b)(b':=b'); eauto 2;
    try eapply DefEq_weaken_available; eauto 2.
  eapply E_LeftIrrel with (b:=b)(b':=b'); eauto 2;
    try eapply DefEq_weaken_available; eauto 2.
  eapply E_Right with (a:=a)(a':=a'); eauto 2;
    try eapply DefEq_weaken_available; eauto 2.
  *)
Qed.


Definition Typing_weakening  := first  typing_weakening_mutual.
Definition PropWff_weakening := second typing_weakening_mutual.
Definition Iso_weakening     := third  typing_weakening_mutual.
Definition DefEq_weakening   := fourth typing_weakening_mutual.
Definition Ctx_weakening     := fifth  typing_weakening_mutual.


(*
Lemma Typing_weakening : ∀ (E F G : context) (a A : tm),  Typing (F ++ G) a A →  Ctx (F ++ E ++ G) ->
                                                          Typing (F ++ E ++ G) a A.
Proof. intros. apply (first typing_weakening_mutual) with (G0 := F ++ G)(F:=F)(E:=E)(G:=G); auto. Qed.


Lemma PropWff_weakening : forall (E F G : context) phi, PropWff (F ++ G) phi -> Ctx (F ++ E ++ G) → PropWff (F ++ E ++ G) phi.
Proof. intros. apply (second typing_weakening_mutual) with (G0 := F ++ G)(F:=F)(E:=E)(G:=G); auto. Qed.

Lemma Iso_weakening : ∀ (E F G : context) (D : available_props) (p1 p2 : constraint),
       Iso (F ++ G) D p1 p2 -> Ctx (F ++ E ++ G) → Iso (F ++ E ++ G) D p1 p2.
Proof. intros. apply (third typing_weakening_mutual) with (G0 := F ++ G)(F:=F)(E:=E)(G:=G); auto. Qed.

Lemma DefEq_weakening : ∀ (E F G : context) (D : available_props) (A B T : tm),
    DefEq (F ++ G) D A B T → Ctx (F ++ E ++ G) → DefEq (F ++ E ++ G) D A B T.
Proof. intros. apply (fourth typing_weakening_mutual) with (G0 := F ++ G)(F:=F)(E:=E)(G:=G); auto. Qed.

Lemma Ctx_weakening : ∀ (E F G: context),
       Ctx (F ++ G) → Ctx (F ++ E ++ G) → Ctx (F ++ E ++ G).
Proof. intros. apply (fifth typing_weakening_mutual) with (G0 := F ++ G)(F:=F)(E:=E)(G:=G); auto. Qed.


Lemma Iso_weakening_dom :
   ∀ (E F G : context) (D : available_props) (p1 p2 : constraint),
       Iso (F ++ G) (dom (F ++ G)) p1 p2 -> Ctx (F ++ E ++ G) → Iso (F ++ E ++ G) (dom(F ++ E ++ G)) p1 p2.
Proof.
  intros.
  eapply Iso_weaken_available.
  eapply Iso_weakening.
  eassumption.
  auto.
Qed.

Lemma DefEq_weakening_dom : ∀ (E F G : context) (D : available_props) (A B T : tm),
    DefEq (F ++ G) (dom (F ++ G)) A B T → Ctx (F ++ E ++ G) → DefEq (F ++ E ++ G) (dom (F ++ E ++ G)) A B T.
Proof.
  intros.
  eapply DefEq_weaken_available.
  eapply DefEq_weakening.
  eassumption.
  auto.
Qed.
*)


End ext_weak.
