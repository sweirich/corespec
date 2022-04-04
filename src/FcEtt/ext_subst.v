Require Import FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.
Require Export FcEtt.fset_facts.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.

Require Export FcEtt.beta.
Require Export FcEtt.ext_wf.
Require Export FcEtt.ett_value.
Require Export FcEtt.ext_weak.
Require Export FcEtt.subsumption.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.


(* Module ext_subst (weak : ext_weak_sig) <: ext_subst_sig. *)
(*   Include weak. *)

Lemma Ctx_strengthen : forall G1 G2, Ctx (G2 ++ G1) -> Ctx G1.
  induction G2; [ | inversion 1]; simpl; auto.
Qed.

Lemma binds_to_PropWff: forall G0 psi0 phi c,
    Ctx G0 ->
    binds c (psi0, (Co phi)) G0 -> PropWff (meet_ctx_l q_C G0) q_C phi.
Proof.
  induction G0; auto; try done.
  move => psi0 phi c H H0.
  destruct a.
  destruct p.
  case H0; try done.
  -  move => h0.
    inversion H; subst; auto.
    have h1:   PropWff (meet_ctx_l q_C G0) q_C phi by scongruence.
    simpl.
    rewrite cons_app_one -[_ ++ _]app_nil_l.
    apply : PropWff_weakening => //.
    inversion h0; subst.
    simpl.
    rewrite cons_app_one -[_ ++ _]app_nil_l.
    apply : PropWff_weakening => // /=.
    move : H => /Ctx_meet_l_C //.
  - move => h0.
    simpl.
    rewrite cons_app_one -[_ ++ _]app_nil_l.
    apply : PropWff_weakening => // /=.
    sauto lq:on.
    hauto q:on use:Ctx_meet_l_C.
Qed.

Lemma tm_subst_fresh_1 :
forall G psi a A a0 x s,
  Typing G psi a A -> Ctx ((x ~ s) ++ G) -> tm_subst_tm_tm a0 x A = A.
Proof.
  qauto l: on l: on use: tm_subst_tm_tm_fresh_eq, Typing_context_fv inv: sort, Ctx.
Qed.

Lemma tm_subst_co_fresh_1 :
forall G psi a A a0 c s,
  Typing G psi a A -> Ctx ((c ~ s) ++ G) -> co_subst_co_tm a0 c A = A.
Proof.
  qauto l: on l: on use: co_subst_co_tm_fresh_eq, Typing_context_fv inv: sort, Ctx.
Qed.

Lemma tm_subst_fresh_2 :
forall G psi a A a0 x s,
  Typing G psi a A -> Ctx ((x ~ s) ++ G) -> tm_subst_tm_tm a0 x a = a.
Proof.
  qauto l: on l: on use: tm_subst_tm_tm_fresh_eq, Typing_context_fv inv: sort, Ctx.
Qed.

Lemma co_subst_fresh :
forall G psi phi a0 x s,
  PropWff G psi phi -> Ctx ((x ~ s) ++ G) -> tm_subst_tm_constraint a0 x phi = phi.
Proof.
  qauto l: on use: tm_subst_tm_constraint_fresh_eq, ProfWff_context_fv inv: Ctx.
Qed.

Lemma bind_map_tm_subst_tm_sort: forall c psi F phi x a,
    binds c (psi, (Co phi)) F ->
    binds c (psi, (Co (tm_subst_tm_constraint a x phi))) (subst_ctx a x F).
Proof.
  induction F; auto.
  move : a => [? [ ? [? | ?]]] /ltac:(sfirstorder).
Qed.

Lemma binds_map_4: forall x A F c0,
    binds x (Tm A) F ->
    binds x (Tm (co_subst_co_tm g_Triv c0 A)) (map (co_subst_co_sort g_Triv c0) F).
Proof.
  induction F; try done.
  intros c0 H.
  case H.
  move => h1.
  inversion h1; subst.
  simpl.
  fsetdec.
  move => h0.
  right.
  apply IHF; auto.
Qed.

Lemma binds_map_5: forall c A B T F c1 ,
    binds c (Co (Eq A B T) ) F ->
    binds c (Co (Eq (co_subst_co_tm g_Triv c1 A) (co_subst_co_tm g_Triv c1 B) (co_subst_co_tm g_Triv c1 T)) ) (map (co_subst_co_sort g_Triv c1) F).
Proof.
  induction F; try done.
  intros c1 H.
  case H.
  move => h1; subst.
  simpl.
  fsetdec.
  move => h0.
  right.
  apply IHF; auto.
Qed.

Lemma tm_subst_tm_tm_dom_invariance: forall x a F, dom F = dom (map (tm_subst_tm_sort a x) F).
Proof.
  induction F; eauto; try fsetdec.
  destruct a0.
  simpl.
  rewrite IHF; auto.
Qed.

(* subsumed by grade related structural rules? *)
(* Lemma subst_rho: forall L G a A x y b rho *)
(*     (T : Typing G a A) *)
(*     (Neq: x <> y) *)
(*     (Fr: y `notin` fv_tm_tm_tm a) *)
(*     (Fr2: y `notin` L) *)
(*     (K : (forall x, x `notin` L -> RhoCheck rho x (open_tm_wrt_tm b (a_Var_f x)))), *)
(*     RhoCheck rho y  (tm_subst_tm_tm a x (open_tm_wrt_tm b (a_Var_f y))). *)
(* Proof. *)
(*   intros. *)
(*   RhoCheck_inversion y; eauto with lngen lc. *)
(* Qed. *)

(* Rewrite the context in to the appropriate form for the induction
   hypothesis (in the cases with binding).
   This rewriting is specific for substitution lemmas.
*)

(* ((y ~ (psi, Tm (tm_subst_tm_tm a x A)) ++ map_snd (tm_subst_tm_sort a x) F) ++ G0) *)
  (* (y ~ (psi, Tm (tm_subst_tm_tm a x A)) ++ subst_ctx a x F ++ G0) *)
Ltac rewrite_subst_context :=
  match goal with
  | [ |- context [([(?y, (?psi, ?C (_ _ _ ?T)))] ++ subst_ctx ?a ?x ?F ++ ?G0)] ] =>
    rewrite_env (subst_ctx a x ((y ~ (psi, (C T))) ++ F) ++ G0)
  end.

(*
 These are constructors for the E judgements that
   - do not bind variables
   - are syntax directed
   - are not variables
 Therefore, they are safe to just use in the substitution lemmas
 below.
*)

Ltac eapply_E_subst :=
  first [ eapply E_Star     |
          eapply E_App      |
          eapply E_CApp     |
(*          eapply E_Const    | *)
          eapply E_IsoConv  |
          eapply E_AppCong  |
          eapply E_CAppCong |
          eapply E_PiSnd    |
          eapply E_CPiSnd].

Lemma tm_substitution_mutual :
  (forall G0 psi b B (H : Typing G0 psi b B),
      forall G a psi0 A (H0 : CTyping G psi0 a A),
               forall F x, G0 = (F ++ (x ~ (psi0, Tm A)) ++ G) ->
                      Typing (subst_ctx a x F ++ G) psi
                             (tm_subst_tm_tm a x b)
                             (tm_subst_tm_tm a x B)) /\
    (forall G0 psi phi (H : PropWff G0 psi phi),
        forall G a psi0 A (H0 : CTyping G psi0 a A),
                 forall F x, G0 = (F ++ (x ~ (psi0, Tm A)) ++ G) ->
                        PropWff (subst_ctx a x F ++ G) psi
                                (tm_subst_tm_constraint a x phi)) /\
    (forall G0 psi p1 p2 (H : Iso G0 psi p1 p2),
        forall G a psi0 A (H0 : CTyping G psi0 a A),
                 forall F x, G0 = (F ++ (x ~ (psi0, Tm A)) ++ G) ->
                Iso (subst_ctx a x F ++ G) psi
                    (tm_subst_tm_constraint a x p1)
                    (tm_subst_tm_constraint a x p2)) /\
    (forall G0 psi phi (H : DefEq G0 psi phi),
       forall G a psi0 A0, CTyping G psi0 a A0 ->
                 forall F x, G0 = (F ++ (x ~ (psi0, Tm A0)) ++ G) ->
                        DefEq (subst_ctx a x F ++ G) psi
                              (tm_subst_tm_constraint a x phi)) /\
    (forall G0 (H : Ctx G0),
       forall G a psi0 A (H0 : CTyping G psi0 a A),
                 forall F x, G0 = (F ++ (x ~ (psi0, Tm A)) ++ G) ->
                        Ctx (subst_ctx a x F ++ G)) /\
    (forall G0 psi psi0 a b T (H : CDefEq G0 psi psi0 a b T),
       forall G a0 psi1 A (H0 : CTyping G psi1 a0 A),
                 forall F x, G0 = (F ++ (x ~ (psi1, Tm A)) ++ G) ->
                        CDefEq (subst_ctx a0 x F ++ G) psi psi0
                               (tm_subst_tm_tm a0 x a)
                               (tm_subst_tm_tm a0 x b)
                               (tm_subst_tm_tm a0 x T)) /\
   (forall G0 psi b B (H : CTyping G0 psi b B),
      forall G a psi0 A (H0 : CTyping G psi0 a A),
               forall F x, G0 = (F ++ (x ~ (psi0, Tm A)) ++ G) ->
                      CTyping (subst_ctx a x F ++ G) psi
                             (tm_subst_tm_tm a x b)
                             (tm_subst_tm_tm a x B)).
Proof.
  ext_induction CON;
    intros; subst; simpl.
  (* 44 goals *)
  all : try solve [eapply CON; eauto 2].
  (* 35 goals *)
  (* var *)
  - destruct (x == x0).
    + subst.
      have [HA HB]: Tm A = Tm A0 /\ psi0 = psi1 by hauto l:on use:binds_mid_eq.
      inversion HA; inversion HB. subst.
      inversion H0; subst; auto.
      * have S : tm_subst_tm_tm a x0 A0 = A0
          by sfirstorder use:tm_subst_fresh_1,Ctx_strengthen.
        hauto l: on l: on q: on use:Typing_weakening_front, Typing_subsumption.
      * exfalso.
        sfirstorder use:Typing_leq_C, q_leb_trans, q_leb_antisym.
    + eapply E_Var; eauto.
      apply binds_remove_mid in b; auto.
      destruct (binds_app_1 _ _ _ _ _ b).
      * eapply binds_map with (f := fun '(q, A) => (q, tm_subst_tm_sort a x0 A)) in H1.
        eapply binds_app_2; auto.
      * eapply binds_app_3.
        apply Ctx_strengthen in c.
        hauto b: on use: Ctx_strengthen, Typing_leq_C, tm_subst_fresh_1.
  (* Pi *)
  - pick fresh y and apply CON; eauto;
    autorewrite with subst_open_var; eauto 2 with lc;
    rewrite_subst_context; qauto depth:1 l:on.
  (* abs *)
  - pick fresh y and apply CON; eauto.
    autorewrite with subst_open_var; eauto 2 with lc.
    rewrite_subst_context; qauto l:on.
    simpl_env.
    apply : H0.
    sfirstorder use:CTyping_meet_ctx_l simp:simpl_env.
    simpl_env.
    done.
  (* App *)
  - inversion c; subst;
    autorewrite with subst_open; hauto q:on db:lc.
  (* Conv *)
  - eapply CON with (psi:=psi); simpl_env; eauto 3.
    + eapply H0; eauto using CTyping_meet_ctx_l.
      simpl_env.
      done.
    + eapply H1; eauto using CTyping_meet_ctx_l.
      simpl_env.
      done.
  (* E_CPi *)
  - pick fresh y and apply CON; eauto;
    autorewrite with subst_open_var; eauto 2 with lc;
    rewrite_subst_context; qauto l:on.
  (* CAbs *)
  - pick fresh y and apply CON; eauto.
    autorewrite with subst_open_var; eauto 2 with lc.
    rewrite_subst_context; qauto l:on.
    simpl_env.
    apply : H0.
    sfirstorder use:CTyping_meet_ctx_l simp:simpl_env.
    simpl_env.
    done.
  (* CApp *)
  - autorewrite with subst_open; eauto 2 with lc.
    eapply CON with (phi := tm_subst_tm_constraint a x phi).
    apply : H; eauto 3.
    simpl_env.
    hauto l: on use: CTyping_meet_ctx_l, map_app.
  (* Fam *)
  - (* eapply CON; eauto 3. *)
    have h0: Typing nil psi0 a A  by eauto using toplevel_closed.
    eapply E_Fam with (a:= tm_subst_tm_tm a0 x a); eauto.
    apply typing_meet_ctx_l_C in h0.
    simpl in h0.
    erewrite (tm_subst_fresh_2 _ t0); eauto.
    erewrite (tm_subst_fresh_1 _ h0); eauto.
    erewrite (tm_subst_fresh_2 _ h0); auto.
    hauto l:on use:typing_meet_ctx_l_C.
  (* ImplWff *)
  - pick fresh y and apply CON; eauto.
    autorewrite with subst_open_var; eauto 2 with lc;
      rewrite_subst_context; qauto l:on.
  - apply CON; sfirstorder depth:1.
  - eapply CON; sfirstorder depth:1.
  - pick fresh y and apply CON; eauto 2.
    autorewrite with subst_open_var; eauto 2 with lc;
      rewrite_subst_context; qauto l:on.
  (* E_Assn *)
  - destruct (c == x).
    + subst.
      hauto l: on use: binds_mid_eq.
    + apply CON with (psi := psi) (psi0 := psi0) (c := c); eauto.
      apply binds_remove_mid in b; auto.
      destruct (binds_app_1 _ _ _ _ _ b); auto.
      * sfirstorder use:binds_app_1, binds_app_2, binds_app_3, bind_map_tm_subst_tm_sort.
      * apply binds_app_3.
        apply Ctx_strengthen in c0.
        move : (Ctx_strengthen _ _ c0) => h1.
        move : (binds_to_PropWff _ _ _ h1 H1) => h2.
        erewrite co_subst_fresh; eauto.
        apply Ctx_meet_l_C in c0.
        apply c0.
  (* Beta *)
  - hauto q: on ctrs:- use: Beta_tm_subst db: lc.
  (* PiCong *)
  - pick fresh y and apply CON; eauto 2.
    + sfirstorder.
    + autorewrite with subst_open_var; eauto 2 with lc.
      rewrite_subst_context.
      eapply H0; eauto.
  (* AbsCong *)
  (* YL: automation overall seems very brittle here. *)
  (* eauto works for Abs but fails for AbsCong *)
  (* maybe hammer can generate more robust tactics? *)
  - pick fresh y and apply CON; eauto 2.
    autorewrite with subst_open_var; eauto 2 with lc.
    rewrite_subst_context.
    eapply H; eauto.
    simpl_env.
    apply : H0.
    sfirstorder use:CTyping_meet_ctx_l simp:simpl_env.
    simpl_env.
    done.
  (* AppCong *)
  - inversion c; subst;
      autorewrite with subst_open; eauto 2 with lc.
    + hauto l:on.
    + hfcrush.
  (* PiFst *)
  - eapply CON; sfirstorder.
  (* PiSnd *)
  - autorewrite with subst_open; eauto 2 with lc.
    hauto l:on.
  (* CPiCong *)
  - pick fresh y and apply CON; eauto 2.
    autorewrite with subst_open_var; eauto 2 with lc.
    rewrite_subst_context. eapply H0; eauto 2.
  (* CAbsCong *)
  - pick fresh y and apply CON; eauto 2.
    autorewrite with subst_open_var; eauto 2 with lc.
    rewrite_subst_context.
    eapply H; eauto.
    simpl_env.
    apply : H0.
    sfirstorder use:CTyping_meet_ctx_l simp:simpl_env.
    simpl_env.
    done.
  (* CAppCong *)
  - autorewrite with subst_open; eauto 2 with lc.
    eapply CON with (phi := tm_subst_tm_constraint a x phi).
    apply : H; eauto 3.
    simpl_env.
    hauto l: on use: CTyping_meet_ctx_l, map_app.
  (* CPiSnd *)
  - autorewrite with subst_open; eauto 2 with lc.
    apply /CON.
    + sfirstorder.
    + simpl_env.
      eapply H0.
      sfirstorder use : CTyping_meet_ctx_l.
      by simpl_env.
    + simpl_env.
      apply /H1.
      apply /CTyping_meet_ctx_l; eauto.
      by simpl_env.
  (* EqConv *)
  - apply /CON; first by sfirstorder.
    simpl_env.
    eapply H0.
    sfirstorder use : CTyping_meet_ctx_l.
    by simpl_env.
  (* EtaRel *)
  - pick fresh y and apply CON.
    sfirstorder.
    autorewrite with subst_open_var; eauto 2 using CTyping_lc1.
    rewrite e; auto.
    move => /=.
    case (y == x) => // h0.
    exfalso.
    fsetdec.
  (* EtaC *)
  - pick fresh y and apply CON.
    sfirstorder.
    autorewrite with subst_open_var; eauto 2 using CTyping_lc1.
    rewrite e; auto.
  (* ImplApp *)
  - rewrite tm_subst_tm_constraint_open_constraint_wrt_co; eauto 2 using CTyping_lc1.
    hauto l:on.
  (* ImplAbs *)
  - pick fresh y and apply CON.
    + rewrite tm_subst_tm_constraint_open_constraint_wrt_co_var;
        eauto 2 using CTyping_lc1.
      rewrite_subst_context; qauto l:on.
    + simpl_env.
      eapply H0.
      sfirstorder use:CTyping_meet_ctx_l.
      by simpl_env.
  (* Ctx_Nil *)
  - move : H.
    by case F.
  (* Ctx_Cons_tm *)
  - destruct F.
    + scongruence.
    + inversion H2; subst.
      simpl.
      apply : CON.
      by sfirstorder.
      simpl_env.
      apply : H0.
      by sfirstorder use:CTyping_meet_ctx_l.
      by simpl_env.
      simpl_env.
      rewrite dom_subst_ctx.
      simpl_env in n.
      fsetdec.
  - destruct F.
    + scongruence.
    + inversion H2; subst.
      simpl.
      apply : CON.
      by sfirstorder.
      simpl_env.
      apply : H0.
      by sfirstorder use:CTyping_meet_ctx_l.
      by simpl_env.
      simpl_env.
      rewrite dom_subst_ctx.
      simpl_env in n.
      fsetdec.
  - apply CE_Top; last by assumption.
    simpl_env.
    apply : H.
    apply CTyping_meet_ctx_l.
    eassumption.
    by simpl_env.
    Unshelve. all:auto.
Qed.

Lemma Typing_tm_subst : forall G psi x psi0 A b B (H : Typing ((x ~ (psi0, Tm A)) ++ G) psi b B),
  forall a, CTyping G psi0 a A ->
       Typing G psi (tm_subst_tm_tm a x b) (tm_subst_tm_tm a x B).
Proof.
  move => G psi x psi0 A b B.
  rewrite -[_++_]app_nil_l.
  qauto l: on ctrs: - use:tm_substitution_mutual.
Qed.

(* Lemma co_subst_rho: forall L x y a rho *)
(*     (Neq: x <> y) *)
(*     (Fr2: y `notin` L) *)
(*     (K : (forall x, x `notin` L -> RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x)))), *)
(*     RhoCheck rho y  (co_subst_co_tm g_Triv x (open_tm_wrt_tm a (a_Var_f y))). *)
(* Proof. *)
(*   intros. *)
(*   RhoCheck_inversion y; eauto with lngen lc. *)
(* Qed. *)

Lemma co_substitution_mutual :
    (forall G0 b B (H : Typing G0 b B),
        forall G D A1 A2 T F c ,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T) ) ++ G)
          -> DefEq G D A1 A2 T
          -> Typing (map (co_subst_co_sort g_Triv c) F ++ G) (co_subst_co_tm g_Triv c b) (co_subst_co_tm g_Triv c B)) /\
    (forall G0 phi (H : PropWff G0 phi),
        forall G D A1 A2 T F c,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T) ) ++ G)
          -> DefEq G D A1 A2 T
          -> PropWff (map (co_subst_co_sort g_Triv c) F ++ G) (co_subst_co_constraint g_Triv c phi)) /\
    (forall G0 D0 p1 p2 (H : Iso G0 D0 p1 p2),
          forall G D A1 A2 T F c,
            G0 = (F ++ (c ~ Co (Eq A1 A2 T) ) ++ G)
            -> DefEq G D A1 A2 T
            -> Iso (map (co_subst_co_sort g_Triv c) F ++ G) (union D (remove c D0))
                    (co_subst_co_constraint g_Triv c p1)
                    (co_subst_co_constraint g_Triv c p2)) /\
    (forall G0 D0 A B T (H : DefEq G0 D0 A B T),
        forall G D F c A1 A2 T1,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T1) ) ++ G)
          -> DefEq G D A1 A2 T1
          -> DefEq (map (co_subst_co_sort g_Triv c) F ++ G) (union D (remove c D0))
                  (co_subst_co_tm g_Triv c A) (co_subst_co_tm g_Triv c B)
                  (co_subst_co_tm g_Triv c T)) /\
    (forall G0 (H : Ctx G0),
        forall G D F c A1 A2 T,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T) ) ++ G)
          -> DefEq G D A1 A2 T
          -> Ctx (map (co_subst_co_sort g_Triv c) F ++ G)).
Proof.
  apply typing_wff_iso_defeq_mutual; auto; intros; subst; simpl.
  Focus 22. destruct rho. Unfocus. 
   all: try first [ E_pick_fresh y; autorewrite with subst_open_var; eauto 2 with lc;
                    try rewrite_subst_context; eauto 3
                  | autorewrite with subst_open; eauto 2 with lc ].
  all: try eapply_E_subst; eauto 2.
  all: try solve [eapply co_subst_rho; eauto 2].
  all: try solve [eapply_first_hyp; eauto; auto].
  all: try solve [eapply DefEq_weaken_available; eauto].
  - apply binds_app_1 in b.
    case:b; try done.
    + move => h0.
      apply E_Var; auto.
      * apply (H _ D _ _ A1 A2 T); auto.
      * apply binds_app_2.
        apply binds_map_4; auto.
    + intros b.
      apply binds_app_1 in b.
      case:b; try solve [move => h0; inversion h0; inversion H0].
      move => h0.
      rewrite co_subst_co_tm_fresh_eq.
      apply E_Var; auto.
        by apply (H _ D _ _ A1 A2 T).
      pose K := Ctx_strengthen ([(c0, Co (Eq A1 A2 T) )] ++ G0) F c.
      clearbody K.
      inversion K; subst.
      have: Typing G0 (a_Var_f x) A; auto => h1.
      move: (Typing_context_fv h1) => ?. split_hyp. auto.
  - eapply E_Conv; eauto 3.
    eapply DefEq_weaken_available; eauto 1.
    eapply_first_hyp; eauto 2.
(*  - have h0: Typing nil A a_Star by eauto using toplevel_closed.
    rewrite co_subst_co_tm_fresh_eq; auto.
    move: (Typing_context_fv h0) => hyp. split_hyp. fsetdec.
  - have h0: Typing nil A a_Star.  eapply toplevel_to_const; eauto.
    rewrite co_subst_co_tm_fresh_eq; auto.
    move: (Typing_context_fv h0) => hyp. split_hyp. fsetdec. *)
  -  have h0: Typing nil a A by eapply toplevel_closed; eauto.
    erewrite (tm_subst_co_fresh_1 _ h0); eauto.
  - apply (E_Wff _ _ _  (co_subst_co_tm g_Triv c A)); eauto 3.
  - apply E_PropCong; eauto 3.
  - eapply E_CPiFst; eauto 3.
    (* eapply H; eauto. *)
  -  destruct (binds_cases G0 F c _ c1 _ (Ctx_uniq c0) b0) as [ (bf & NE & Fr) | [(E1 & E2) | (bg & NE & Fr)]].
    + eapply E_Assn; eauto 3.
      apply binds_app_2.
      apply binds_map_5. eauto 1.
    + inversion E2. subst. clear E2.
      have: Ctx ([(c1, Co (Eq A1 A2 T1))] ++ G0).
      apply (Ctx_strengthen _ F); auto.
      move => Hi2.
      inversion Hi2; subst; clear Hi2.
      inversion H5; subst; clear H5.
      repeat rewrite co_subst_co_tm_fresh_eq; eauto 2.
      ++ rewrite_env (nil ++(map (co_subst_co_sort g_Triv c1) F) ++ G0).
         eapply (fourth weaken_available_mutual).
         pose K := DefEq_weakening.
         apply (K _ _ _ _ _ H1); eauto 2.
         (* eapply H;  *)
         (* eauto 2. *)
         auto.
      ++ move : (Typing_context_fv H8) => ?. split_hyp. auto.
      ++ move : (Typing_context_fv H9) => ?. split_hyp. auto.
      ++ move: (Typing_context_fv H8) => ?. split_hyp. auto.
    + have: Ctx ([(c1, Co (Eq A1 A2 T1))] ++ G0). by apply (Ctx_strengthen _ F); auto.
      move => h2.
      have: Ctx G0 by eapply Ctx_strengthen; eauto. move => h3.
      have: PropWff G0 (Eq a b A). eapply binds_to_PropWff; eauto 1. move => h4.
      inversion h4. subst. clear h4.
      have: c1 `notin` dom G0. inversion h2; auto.
      move => Fr1.
      repeat rewrite co_subst_co_tm_fresh_eq.
      eapply E_Assn; eauto 1.
      eapply H; eauto 1.
      eapply binds_app_3; eauto 1.
      eauto.
      all:
        move: (Typing_context_fv H5) => ?;
        move: (Typing_context_fv H6) => ?;
        split_hyp;
        unfold "[<=]" in *; eauto.
  - eauto.
  - eauto.
  - eapply E_Trans; eauto 2.
  - eapply E_Beta; eauto 2.
    eapply Beta_co_subst; eauto.
  - eapply E_PiFst; simpl in *; eauto 3.
  - eapply E_Cast.
    eapply H; eauto.
    eapply H0; eauto.
  - eapply E_EqConv; eauto 2.
    eapply DefEq_weaken_available; eauto 1.
    eauto 2.
  - eapply E_IsoSnd; eauto 1.
    eapply H; eauto.
  - rewrite e; eauto.
  (* Left/Right. Do not remove.
  - eapply E_LeftRel with (b := co_subst_co_tm g_Triv c b) (b':= co_subst_co_tm g_Triv c b'); eauto 2.
    eapply Path_co_subst_co_tm; eauto 2 with lc.
    eapply Path_co_subst_co_tm; eauto 2 with lc.
    autorewrite with open_subst; eauto 2 with lc.
    autorewrite with open_subst; eauto 2 with lc.
    eapply DefEq_weaken_available; eauto 2.

  - eapply E_LeftIrrel with (b := co_subst_co_tm g_Triv c b)
                              (b':= co_subst_co_tm g_Triv c b'); eauto 2.
    eapply Path_co_subst_co_tm; eauto 2 with lc.
    eapply Path_co_subst_co_tm; eauto 2 with lc.
    autorewrite with open_subst; eauto 2 with lc.
    eapply H3; eauto.
    autorewrite with open_subst; eauto 2 with lc.
    eapply DefEq_weaken_available; eauto 2.
  - eapply E_Right with (a := co_subst_co_tm g_Triv c a)
                        (a':= co_subst_co_tm g_Triv c a'); eauto 2.
    eapply Path_co_subst_co_tm; eauto 2 with lc.
    eapply Path_co_subst_co_tm; eauto 2 with lc.
    eapply H; eauto 2.
    eapply H1; eauto 2.
    autorewrite with open_subst; eauto 2 with lc.
    autorewrite with open_subst; eauto 2 with lc.
    eapply DefEq_weaken_available; eauto 2.
  - eapply E_CLeft; eauto 2.
    eapply Path_co_subst_co_tm; eauto 2 with lc.
    eapply Path_co_subst_co_tm; eauto 2 with lc.
    eapply H; eauto 2.
    eapply H0; eauto 2.
    eapply DefEq_weaken_available; eauto 2.
    replace g_Triv with (co_subst_co_co g_Triv c g_Triv).
    autorewrite with open_subst; eauto 2 with lc.
    auto. *)
  - rewrite e; eauto. 
  - rewrite e; eauto.
  - induction F; done.
  - induction F; try done.
    destruct a.
    destruct s; try inversion H1.
    + simpl.
      apply E_ConsTm; auto.
      * simpl in H1.
        inversion H1.
        apply (H _ D _ _ A1 A2 T); auto.
      * simpl in H0.
        inversion H1; subst; clear H1.
        apply (H0 _ D A1 A2 T _ _); auto.
      * inversion H1; subst; clear H1.
        auto.
  - inversion H1; subst; clear H1.
    induction F; try done.
    + inversion H4; subst; clear H4; auto.
    + destruct a.
      destruct s; try inversion H4.
      simpl; subst.
      apply E_ConsCo; auto.
      * apply (H _ D _ _ A1 A2 T); auto.
      * inversion H4; subst; clear H4.
         apply (H0 G0 D A1 A2 T F c1); auto.
Qed.

Lemma Typing_co_subst:
   forall G D c a1 a2 A b B (H : Typing (c ~ (Co (Eq a1 a2 A)) ++ G) b B),
     DefEq G D a1 a2 A ->
     Typing G (co_subst_co_tm g_Triv c b) (co_subst_co_tm g_Triv c B).
Proof.
  intros.
  move: (first co_substitution_mutual) => ho.
  eapply ho with (F := nil); eauto.
  simpl; auto.
Qed.

(* -------------------- *)


Lemma Typing_swap : forall x1 x G a A B,
      x1 `notin` fv_tm_tm_tm a \u fv_tm_tm_tm B
    -> x `notin` dom G \u {{ x1 }}
    -> Typing ([(x1, Tm A)] ++ G) (open_tm_wrt_tm a (a_Var_f x1))
             (open_tm_wrt_tm B (a_Var_f x1))
    -> Typing ([(x, Tm A)] ++ G) (open_tm_wrt_tm a (a_Var_f x))
             (open_tm_wrt_tm B (a_Var_f x)).
Proof.
  intros.
  assert (AC: Ctx ((x1 ~ Tm A) ++ G)). eauto.
  inversion AC; subst.
  assert (TV : Typing ([(x,Tm A)] ++ G) (a_Var_f x) A); eauto.
  assert (CTX : Ctx ([(x1,Tm A)] ++ [(x, Tm A)] ++ G)).
  econstructor; auto.
  pose M1 := (Typing_weakening H6 [(x,Tm A)] nil G).
  simpl_env in M1; eapply M1; eauto.

  pose K1 := Typing_weakening H1 [(x,Tm A)] [(x1, Tm A)] G eq_refl CTX;
               clearbody K1.
  pose K2 := Typing_tm_subst K1 TV.
  clearbody K2.
  repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K2; auto.
  rewrite tm_subst_tm_tm_var in K2;
  repeat rewrite tm_subst_tm_tm_fresh_eq in K2.
  auto.
  eauto.
  eauto.
Qed.

Lemma DefEq_swap : forall x1 x G A1 D b1 b2 B,
   x1 `notin` fv_tm_tm_tm b1 \u fv_tm_tm_tm b2 \u fv_tm_tm_tm B
  -> x `notin` dom G \u {{ x1 }}
  -> DefEq ([(x1, Tm A1)] ++ G) D
          (open_tm_wrt_tm b1 (a_Var_f x1)) (open_tm_wrt_tm b2 (a_Var_f x1))
          (open_tm_wrt_tm B (a_Var_f x1))
  -> DefEq ([(x, Tm A1)] ++ G) D
          (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x))
          (open_tm_wrt_tm B (a_Var_f x)).
Proof.
  intros.
  assert (AC: Ctx ((x1 ~ Tm A1) ++ G)). eauto.
  inversion AC; subst.
  assert (TV : Typing ([(x,Tm A1)] ++ G) (a_Var_f x) A1).
  { econstructor; eauto. }
  assert (CTX : Ctx ([(x1,Tm A1)] ++ [(x, Tm A1)] ++ G)).
  { econstructor; auto.
  pose M1 := (Typing_weakening H6 [(x,Tm A1)] nil G).
  simpl_env in M1; eapply M1; eauto. }

  move: (DefEq_weakening H1 [(x,Tm A1)] [(x1, Tm A1)] G eq_refl CTX) => K1.
  move: (fourth tm_substitution_mutual _ _ _ _ _ K1 _ _ _ TV nil _ eq_refl) => K2.
  simpl_env in K2.
  rewrite -tm_subst_tm_tm_intro in K2; auto.
  rewrite -tm_subst_tm_tm_intro in K2; auto.
  rewrite -tm_subst_tm_tm_intro in K2; auto.
Qed.

(* -------------------- *)


Lemma E_Pi_exists : forall x (G : context) (rho : relflag) (A B : tm),
      x `notin` dom G \u fv_tm_tm_tm B
      -> Typing ([(x, Tm A)] ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Star
      -> Typing G A a_Star -> Typing G (a_Pi rho A B) a_Star.
Proof.
  intros.
  pick fresh y and apply E_Pi.
  replace a_Star with (open_tm_wrt_tm a_Star (a_Var_f y)); auto.
  eapply Typing_swap; eauto.
  auto.
Qed.


Lemma E_Abs_exists :  forall x (G : context) (rho : relflag) (a A B : tm),
    x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm B
    -> Typing ([(x, Tm A)] ++ G) (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))
    -> Typing G A a_Star
    -> RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x))
    -> Typing G (a_UAbs rho a) (a_Pi rho A B).
Proof.
  intros.
  pick fresh y and apply E_Abs; auto.
  eapply (@Typing_swap x); eauto.
  eapply rho_swap with (x := x); eauto.
Qed.




(* End ext_subst. *)
