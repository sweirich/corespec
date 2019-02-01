
Require Import FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.
Require Export FcEtt.fset_facts.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ind.

Require Export FcEtt.beta.
Require Export FcEtt.ext_wf.
Require Import FcEtt.ett_path.
Require Import FcEtt.ext_weak.
Require Import FcEtt.ett_roleing.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Lemma Ctx_strengthen : forall G1 G2, Ctx (G2 ++ G1) -> Ctx G1.
  induction G2; [ | inversion 1]; simpl; auto.
Qed.

Lemma binds_to_PropWff: forall G0 A B T R c,
    Ctx G0 ->
    binds c (Co (Eq A B T R)) G0 -> PropWff G0 (Eq A B T R).
Proof.
  induction G0; auto; try done.
  intros A B T R c H H0.
  destruct a.
  destruct s; auto; try done.
  - case H0; try done.
    move => h0.
    inversion H; subst.
    have:   PropWff ( G0) (Eq A B T R) . 
    apply (IHG0 _ _ _ _ c H4); eauto.
    move => h1.
    rewrite_env (nil ++ [(a, Tm A0)] ++ G0).
    eapply PropWff_weakening; eauto.
  - destruct H0; subst.
    inversion H0; subst.
    inversion H; subst.
    rewrite_env (nil ++ [(c, Co (Eq A B T R))] ++ G0).
    eapply PropWff_weakening; eauto.
    rewrite_env (nil ++ [(a, Co phi)] ++ G0).
    eapply PropWff_weakening; eauto.
    simpl.
    inversion H.
    eapply IHG0; eauto 2.
Qed.

Lemma tm_subst_fresh_1 :
forall G a A a0 x s,
  Typing G a A -> Ctx ((x ~ s) ++ G) -> tm_subst_tm_tm a0 x A = A.
Proof.
  intros G a A a0 x s H H0.
  destruct s.
  - apply tm_subst_tm_tm_fresh_eq.
    inversion H0; subst; clear H0.
    show_fresh.
  - apply tm_subst_tm_tm_fresh_eq.
    inversion H0; subst; clear H0.
    show_fresh.
Qed.

Lemma tm_subst_co_fresh_1 :
forall G a A a0 c s,
  Typing G a A -> Ctx ((c ~ s) ++ G) -> co_subst_co_tm a0 c A = A.
Proof.
  intros G a A a0 x s H H0.
  destruct s.
  - apply co_subst_co_tm_fresh_eq.
    inversion H0; subst; clear H0.
    show_fresh.
  - apply co_subst_co_tm_fresh_eq.
    inversion H0; subst; clear H0.
    show_fresh.
Qed.

Lemma tm_subst_fresh_2 :
forall G a A a0 x s,
  Typing G a A -> Ctx ((x ~ s) ++ G) -> tm_subst_tm_tm a0 x a = a.
Proof.
  intros G a A a0 x s H H0.
  apply tm_subst_tm_tm_fresh_eq.
  inversion H0; subst; auto;
  show_fresh.
Qed.

Lemma tm_subst_co_fresh_2 :
forall G A a0 c s,
  Typing G A a_Star -> Ctx ((c ~ s) ++ G) -> co_subst_co_tm a0 c A = A.
Proof.
  intros G A a0 x s H H0.
  destruct s.
  - apply co_subst_co_tm_fresh_eq.
    inversion H0; subst; clear H0.
    show_fresh.
  - apply co_subst_co_tm_fresh_eq.
    inversion H0; subst; clear H0.
    show_fresh.
Qed.

Lemma co_subst_fresh :
forall G phi  a0 x s,
  PropWff G phi -> Ctx ((x ~ s) ++ G) -> tm_subst_tm_constraint a0 x phi = phi.
Proof.
  intros G phi  a0 x s H H0.
  apply tm_subst_tm_constraint_fresh_eq.
  move: (ProfWff_context_fv H) => ?. split_hyp.
  inversion H0; subst; auto.
Qed.

Lemma bind_map_tm_subst_tm_sort: forall c F A B T x a R,
    binds c (Co (Eq A B T R)) F ->
    binds c (Co (Eq (tm_subst_tm_tm a x A)
                    (tm_subst_tm_tm a x B) (tm_subst_tm_tm a x T) R)) (map (tm_subst_tm_sort a x) F).
Proof.
  induction F; try done.
  destruct a.
  destruct s; auto; try done.
  - intros A0 B T x a0 R0 H.
    right.
    (case H; try done) => h0.
    apply IHF; auto.
  - intros A B T x a0 R0 H.
    case H; auto.
    + inversion 1; subst.
      left; auto.
    + move => h0.
      right.
      apply IHF; auto.
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

Lemma binds_map_5: forall c A B T F c1 R,
    binds c (Co (Eq A B T R) ) F ->
    binds c (Co (Eq (co_subst_co_tm g_Triv c1 A) (co_subst_co_tm g_Triv c1 B) (co_subst_co_tm g_Triv c1 T) R) ) (map (co_subst_co_sort g_Triv c1) F).
Proof.
  induction F; try done.
  intros c1 R H.
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

Lemma subst_rho: forall L G a A x y b rho
    (T : Typing G a A)
    (Neq: x <> y)
    (Fr: y `notin` fv_tm_tm_tm a)
    (Fr2: y `notin` L)
    (K : (forall x, x `notin` L -> RhoCheck rho x (open_tm_wrt_tm b (a_Var_f x)))),
    RhoCheck rho y  (tm_subst_tm_tm a x (open_tm_wrt_tm b (a_Var_f y))).
Proof.
  intros.
  RhoCheck_inversion y; eauto with lngen lc.
Qed.

(* Rewrite the context in to the appropriate form for the induction
   hypothesis (in the cases with binding).
   This rewriting is specific for substitution lemmas.
*)
Ltac rewrite_subst_context :=
  match goal with
  | [ |- context [( (?y ~ ?C (_ _ _ ?T)) ++ map ?sub ?F ++ ?G0)] ] =>
    rewrite_env (map sub ((y ~ (C T)) ++ F) ++ G0)
  | [ |- context [([(?y, ?C (_ _ _ ?T) ?R)] ++ map ?sub ?F ++ ?G0)] ] =>
    rewrite_env (map sub ((y ~ (C T R)) ++ F) ++ G0)  
  | [ |- context [( (?y ~ ?C (?D (_ _ _ ?a) (_ _ _ ?b) (_ _ _ ?T) ?R)) 
                    ++ map ?sub ?F ++ ?G0)] ] =>
    rewrite_env (map sub ((y ~ (C (D a b T R))) ++ F) ++ G0) 
  | [ |- context [([(?y, ?C (?D (_ _ _ ?a) (_ _ _ ?b) (_ _ _ ?T) ?R))]
                    ++ map ?sub ?F ++ ?G0)] ] =>
    rewrite_env (map sub ((y ~ (C (D a b T R))) ++ F) ++ G0) 
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
          eapply E_IApp     |
          eapply E_CApp     |
          eapply E_TApp     |
          eapply E_IsoConv  |
          eapply E_AppCong  |
          eapply E_IAppCong |
          eapply E_TAppCong |
          eapply E_CAppCong |
          eapply E_PiSnd    |
          eapply E_CPiSnd].



Lemma tm_substitution_mutual :
   (forall G0 b B (H : Typing G0 b B),
      forall G a A, Typing G a A ->
               forall F x, G0 = (F ++ (x ~ (Tm A)) ++ G) ->
                      Typing (map (tm_subst_tm_sort a x) F ++ G)
                             (tm_subst_tm_tm a x b)
                             (tm_subst_tm_tm a x B)) /\
    (forall G0 phi  (H : PropWff G0 phi),
        forall G a A, Typing G a A ->
                 forall F x, G0 = (F ++ (x ~ (Tm A)) ++ G) ->
                        PropWff (map (tm_subst_tm_sort a x) F ++ G)
                                (tm_subst_tm_constraint a x phi) ) /\
    (forall G0 D p1 p2  (H : Iso G0 D p1 p2 ),
        forall G a A, Typing G a A ->
                 forall F x, G0 = (F ++ (x ~ (Tm A)) ++ G) ->
                Iso (map (tm_subst_tm_sort a x) F ++ G) D
                    (tm_subst_tm_constraint a x p1)
                    (tm_subst_tm_constraint a x p2) ) /\
    (forall G0 D A B T R'' (H : DefEq G0 D A B T R''),
       forall G a A0, Typing G a A0 ->
                 forall F x, G0 = (F ++ (x ~ (Tm A0)) ++ G) ->
                        DefEq (map (tm_subst_tm_sort a x) F ++ G) D
                              (tm_subst_tm_tm a x A)
                              (tm_subst_tm_tm a x B) (tm_subst_tm_tm a x T) R'') /\
    (forall G0 (H : Ctx G0),
        forall G a A, Typing G a A ->
                 forall F x, G0 = (F ++ (x ~ (Tm A)) ++ G) ->
                        Ctx (map (tm_subst_tm_sort a x) F ++ G)).
Proof. 
  ext_induction CON; 
(*  eapply typing_wff_iso_defeq_mutual; *)
    intros; subst; simpl.
  all: try first [ E_pick_fresh y;
                   autorewrite with subst_open_var; eauto 2 with lc;
                   try rewrite_subst_context; eauto 3 |
                   autorewrite with subst_open; eauto 2 with lc ].
  all: try solve [econstructor; simpl in *; eauto 2].
  all: try eapply_E_subst.
  all: try solve [eapply subst_rho; eauto 2].
  all: try solve [eapply_first_hyp; eauto 2].
  all: try solve [eapply RolePath_subst; eauto 2 with lc].
  all: try solve [eapply DefEq_weaken_available; eauto 2].
  (* 16 *)
  - destruct (x == x0).
    + subst.
      assert (HA: Tm A = Tm A0). eapply binds_mid_eq; eauto.
      inversion HA. subst.
      assert (S : tm_subst_tm_tm a x0 A0 = A0). eapply tm_subst_fresh_1. eauto.
      apply Ctx_strengthen with (G2 := F). eauto.
      rewrite S.
      rewrite_env (nil ++ map (tm_subst_tm_sort a x0) F ++ G0).
      eapply Typing_weakening; eauto 2. simpl_env.
      apply (H _ _ A0); auto.
    + apply binds_remove_mid in b; auto.
      destruct (binds_app_1 _ _ _ _ _ b).
      (* after x *)
      eapply E_Var; eauto 2.
      eapply binds_app_2.
      assert (EQ : tm_subst_tm_sort a x0 (Tm A) = Tm (tm_subst_tm_tm a x0 A)). auto.
      rewrite <- EQ.
      eapply binds_map_2. auto.
      (* before x *)
      eapply E_Var; eauto 2.
      apply Ctx_strengthen in c.
      assert (EQ: tm_subst_tm_tm a x0 A = A). eapply tm_subst_fresh_1.
      eapply E_Var.
      eapply Ctx_strengthen. eauto. eauto. eauto.
      rewrite EQ.
      eauto.
  - (* conversion *)
    eapply E_Conv; try eapply DefEq_weaken_available; eauto 3. 
  - admit. (* have h0: Typing nil A a_Star by eauto using toplevel_closed.
    eapply E_Const. eauto 2.
    erewrite (tm_subst_fresh_2 _ h0); auto. eauto 2.
    erewrite (tm_subst_fresh_2 _ h0); eauto 2. *)
  - move: (toplevel_inversion b) => [X [G [B [h1 [h0 [h3 h4]]]]]]. 
    eapply E_Fam with (a:= tm_subst_tm_tm a0 x a); eauto 2.
    admit.
    admit.
    (* Need to reason about the freshness of toplevel definitions *)
(*    erewrite (tm_subst_fresh_2 _ h0); auto.
    erewrite (tm_subst_fresh_1 _ h0); auto. eauto 1. eauto 2. eauto 2. 
    erewrite (tm_subst_fresh_1 _ h0); eauto 2. *)
  - (* E_Case *)
    admit.
  - (* E_Assn *)
    destruct (c == x).
    + subst.
      apply binds_mid_eq in b0; auto; try done.
    + apply binds_remove_mid in b0; auto.
      destruct (binds_app_1 _ _ _ _ _ b0).
      * apply (E_Assn _ D _ _ _ _ c); auto.
           by apply (H _ _ A0).
           have:  binds c (Co (Eq (tm_subst_tm_tm a0 x a) (tm_subst_tm_tm a0 x b) (tm_subst_tm_tm a0 x A) R)) (map (tm_subst_tm_sort a0 x) F); auto.
           apply bind_map_tm_subst_tm_sort; auto.
       * apply (E_Assn _ D _ _ _ _ c); auto.
           by apply (H _ _ A0).
         have: Ctx ([(x, Tm A0)] ++ G0) by apply (Ctx_strengthen _ F); auto.
         inversion 1; subst.
         have: PropWff G0 (Eq a b A R) by apply (binds_to_PropWff _ _ _ _ c); auto.
         inversion 1; subst.
         repeat rewrite tm_subst_tm_tm_fresh_eq; auto.
         all: show_fresh.
  - eapply E_Beta; eauto.
    eapply Beta_tm_subst; eauto 2 with lc.
  - eapply E_EqConv; eauto 2.
    eapply DefEq_weaken_available; eauto.
  - eapply E_LeftRel with (b := tm_subst_tm_tm a0 x b)
                          (b':= tm_subst_tm_tm a0 x b'); eauto 2.
    eapply ValuePath_subst; eauto 2 with lc.
    eapply ValuePath_subst; eauto 2 with lc.
    autorewrite with open_subst; eauto 2 with lc.
    eapply H3; eauto.
    autorewrite with open_subst; eauto 2 with lc.
    eapply DefEq_weaken_available; eauto 2.
  - eapply E_LeftIrrel with (b := tm_subst_tm_tm a0 x b)
                          (b':= tm_subst_tm_tm a0 x b'); eauto 2.
    eapply ValuePath_subst; eauto 2 with lc.
    eapply ValuePath_subst; eauto 2 with lc.
    autorewrite with open_subst; eauto 2 with lc.
    eapply H3; eauto.
    autorewrite with open_subst; eauto 2 with lc.
    eapply DefEq_weaken_available; eauto 2.
  - eapply E_Right with (a := tm_subst_tm_tm a0 x a)
                        (a':= tm_subst_tm_tm a0 x a'); eauto 2.
    eapply ValuePath_subst; eauto 2 with lc.
    eapply ValuePath_subst; eauto 2 with lc.
    eapply H; eauto 2.
    eapply H1; eauto 2.
    autorewrite with open_subst; eauto 2 with lc.
    autorewrite with open_subst; eauto 2 with lc.
    eapply DefEq_weaken_available; eauto 2.
  - eapply E_CLeft; eauto 2.
    eapply ValuePath_subst; eauto 2 with lc.
    eapply ValuePath_subst; eauto 2 with lc.
    eapply H; eauto 2.
    eapply H0; eauto 2.
    eapply DefEq_weaken_available; eauto 2.
    replace g_Triv with (tm_subst_tm_co a0 x g_Triv).
    autorewrite with open_subst; eauto 2 with lc.
    auto.
  - destruct  F; try done.
  - induction F; try done.
    simpl; simpl in H2.
    inversion H2; subst; auto.
    destruct a0.
    destruct s.
    + simpl.
      eapply E_ConsTm; auto.
      * simpl in H2.
        inversion H2.
        apply (H _ _ _ H1); auto.
      * simpl in H0.
        inversion H2; subst; clear H2.
        apply (H0 _ _ _ H1); auto.
      * inversion H2; subst; clear H2; auto.
    + inversion H2.
  - inversion H2; subst; clear H2.
    induction F; try done.
    destruct a0.
    destruct s.
    + simpl; subst.
      inversion H4.
    + simpl; subst.
      apply E_ConsCo; auto.
      * apply (H _ _ _ H1); auto.
         inversion H4; auto.
      * inversion H4; subst; clear H4.
        apply (H0 _ _ A); auto.
      * inversion H4; subst; clear H4.
        auto. Unshelve. all:auto.
Admitted.

Lemma Typing_tm_subst : forall G x A b B (H : Typing ((x ~ Tm A) ++ G) b B),
  forall a, Typing G a A ->
       Typing G (tm_subst_tm_tm a x b) (tm_subst_tm_tm a x B).
Proof.
  intros.
  pose K := @first _ _ _ _ _ tm_substitution_mutual _ b B H G a A H0 nil x.
  clearbody K. simpl in K.
  apply K. auto.
Qed.

Lemma co_subst_rho: forall L x y a rho
    (Neq: x <> y)
    (Fr2: y `notin` L)
    (K : (forall x, x `notin` L -> RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x)))),
    RhoCheck rho y  (co_subst_co_tm g_Triv x (open_tm_wrt_tm a (a_Var_f y))).
Proof.
  intros.
  RhoCheck_inversion y; eauto with lngen lc.
Qed.

Lemma co_substitution_mutual :
    (forall G0 b B (H : Typing G0 b B),
        forall G D A1 A2 T R' F c ,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T R') ) ++ G)
          -> DefEq G D A1 A2 T R'
          -> Typing (map (co_subst_co_sort g_Triv c) F ++ G) (co_subst_co_tm g_Triv c b) (co_subst_co_tm g_Triv c B)) /\
    (forall G0 phi  (H : PropWff G0 phi ),
        forall G D A1 A2 T R' F c,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T R') ) ++ G)
          -> DefEq G D A1 A2 T R'
          -> PropWff (map (co_subst_co_sort g_Triv c) F ++ G) (co_subst_co_constraint g_Triv c phi) ) /\
    (forall G0 D0 p1 p2  (H : Iso G0 D0 p1 p2 ),
          forall G D A1 A2 T R' F c,
            G0 = (F ++ (c ~ Co (Eq A1 A2 T R') ) ++ G)
            -> DefEq G D A1 A2 T R'
            -> Iso (map (co_subst_co_sort g_Triv c) F ++ G) (union D (remove c D0))
                    (co_subst_co_constraint g_Triv c p1)
                    (co_subst_co_constraint g_Triv c p2) ) /\
    (forall G0 D0 A B T R'' (H : DefEq G0 D0 A B T R''),
        forall G D F c A1 A2 T1 R',
          G0 = (F ++ (c ~ Co (Eq A1 A2 T1 R') ) ++ G)
          -> DefEq G D A1 A2 T1 R'
          -> DefEq (map (co_subst_co_sort g_Triv c) F ++ G) (union D (remove c D0))
                  (co_subst_co_tm g_Triv c A) (co_subst_co_tm g_Triv c B)
                  (co_subst_co_tm g_Triv c T) R'') /\
    (forall G0 (H : Ctx G0),
        forall G D F c A1 A2 T R',
          G0 = (F ++ (c ~ Co (Eq A1 A2 T R') ) ++ G)
          -> DefEq G D A1 A2 T R'
          -> Ctx (map (co_subst_co_sort g_Triv c) F ++ G)).
Proof.
  ext_induction CON; 
  (* adds an assumption to the context saying what branch we are in. *)
  (* apply typing_wff_iso_defeq_mutual; *)
  auto; intros; subst; simpl.
  all: try first [ E_pick_fresh y; autorewrite with subst_open_var; eauto 2 with lc;
                    try rewrite_subst_context; eauto 3
                  | autorewrite with subst_open; eauto 2 with lc ].
  all: try eapply_E_subst; eauto 2.
  all: try solve [eapply co_subst_rho; eauto 2].
  all: try solve [eapply_first_hyp; eauto 2; auto].
  all: try solve [eapply RolePath_subst_co; eauto 2 with lc].
  all: try solve [eapply DefEq_weaken_available; eauto 2].
  (* - eapply E_SubRole with R1. assumption. eapply H. auto. apply H1. *)
  - apply binds_app_1 in b.
    case:b; try done.
    + move => h0.
      apply E_Var; auto.
      * apply (H _ D _ _ A1 A2 T R'); auto.
      * apply binds_app_2.
        apply binds_map_4; auto.
    + intros b.
      apply binds_app_1 in b.
      case:b; try solve [move => h0; inversion h0; inversion H0].
      move => h0.
      rewrite co_subst_co_tm_fresh_eq.
      admit.
      apply E_Var; auto.
        by apply (H _ D _ _ A1 A2 T R').
(*      pose K := Ctx_strengthen ([(c0, Co (Eq A1 A2 T R') )] ++ G0) F c.
      clearbody K.
      inversion K; subst.
      have: Typing G0 (a_Var_f x) A R; auto => h1.
      move: (Typing_context_fv h1) => ?. split_hyp. auto. *)
  - eapply E_Conv; eauto 3.
  - (* E_Const *) 
    admit. (* have h0: Typing nil A a_Star Rep by eauto using toplevel_closed. 
    eapply E_Const. eauto 2. erewrite tm_subst_co_fresh_2; eauto 2.
    erewrite tm_subst_co_fresh_2; eauto 2. *)
  - (* E_Fam *) 
    admit.
    (* have h0: Typing nil a A R by eapply toplevel_closed; eauto. 
    erewrite (tm_subst_co_fresh_1 _ h0); eauto. *)
  - (* E_Case *) admit. 
(*  - eapply E_Pat; try eapply DefEq_weaken_available; eauto.
  - eapply (E_Wff _ _ _ (co_subst_co_tm g_Triv c A)); eauto 3.
  - apply E_PropCong; eauto 3. *)
  - eapply E_CPiFst; eauto 3.
    eapply H; eauto.
  -  destruct (binds_cases G0 F c _ c1 _ (Ctx_uniq c0) b0) as [ (bf & NE & Fr) | [(E1 & E2) | (bg & NE & Fr)]].
    + eapply E_Assn; eauto 3.
      apply binds_app_2.
      apply binds_map_5. eauto 1.
    + inversion E2. subst. clear E2.
      have: Ctx ([(c1, Co (Eq A1 A2 T1 R'))] ++ G0).
      apply (Ctx_strengthen _ F); auto.
      move => Hi2.
      inversion Hi2; subst; clear Hi2.
      inversion H5; subst; clear H5.
      repeat rewrite co_subst_co_tm_fresh_eq; eauto 2.
      all: try show_fresh.
      rewrite_env (nil ++(map (co_subst_co_sort g_Triv c1) F) ++ G0).
      eapply (fourth weaken_available_mutual).
      pose K := DefEq_weakening.
      apply (K _ _ _ _ _ _ H1); eauto 2.
      eapply H; eauto 2. auto.
    + have: Ctx ([(c1, Co (Eq A1 A2 T1 R'))] ++ G0). by apply (Ctx_strengthen _ F); auto.
      move => h2.
      have: Ctx G0 by eapply Ctx_strengthen; eauto. move => h3.
      have: PropWff G0 (Eq a b A R). 
      eapply binds_to_PropWff; eauto 1. move => h4.
      inversion h4. subst. clear h4.
      have: c1 `notin` dom G0. inversion h2; auto.
      move => Fr1.
      repeat rewrite co_subst_co_tm_fresh_eq.
      all: try show_fresh.
      eapply E_Assn; eauto 1.
      eapply H; eauto 1.
      eapply binds_app_3; eauto 1.
      eauto.
(*  - eauto.
  - eauto.
  - eapply E_Trans; eauto 2.
  - eapply E_Sub. eapply H. auto. assumption. assumption. *)
  - eapply E_Beta; eauto 2.
    eapply Beta_co_subst; eauto.
  - eapply E_PiFst; simpl in *; eauto 3.
(*  - eapply E_Cast.
    eapply H; eauto.
    eapply H0; eauto. *)
  - eapply E_EqConv; eauto 2.
    eapply DefEq_weaken_available; eauto 1.
    eauto 2.
  - eapply E_IsoSnd; eauto 1.
    eapply H; eauto.
  - eapply E_LeftRel with (b := co_subst_co_tm g_Triv c b) (b':= co_subst_co_tm g_Triv c b'); eauto 2.
    eapply ValuePath_subst_co; eauto 2 with lc.
    eapply ValuePath_subst_co; eauto 2 with lc.
    autorewrite with open_subst; eauto 2 with lc.
    eapply H3; eauto.
    autorewrite with open_subst; eauto 2 with lc.
    eapply DefEq_weaken_available; eauto 2.

  - eapply E_LeftIrrel with (b := co_subst_co_tm g_Triv c b)
                              (b':= co_subst_co_tm g_Triv c b'); eauto 2.
    eapply ValuePath_subst_co; eauto 2 with lc.
    eapply ValuePath_subst_co; eauto 2 with lc.
    autorewrite with open_subst; eauto 2 with lc.
    eapply H3; eauto.
    autorewrite with open_subst; eauto 2 with lc.
    eapply DefEq_weaken_available; eauto 2.
  - eapply E_Right with (a := co_subst_co_tm g_Triv c a)
                        (a':= co_subst_co_tm g_Triv c a'); eauto 2.
    eapply ValuePath_subst_co; eauto 2 with lc.
    eapply ValuePath_subst_co; eauto 2 with lc.
    admit. (* eapply H; eauto 2. *)
    admit. (* eapply H1; eauto 2. *)
    admit.
    eapply DefEq_weaken_available; eauto 2 with lc.
    admit.

  - eapply E_CLeft; eauto 2.
    eapply ValuePath_subst_co; eauto 2 with lc.
    eapply ValuePath_subst_co; eauto 2 with lc.
    eapply H; eauto 2.
    eapply H0; eauto 2.
    eapply DefEq_weaken_available; eauto 2.
    replace g_Triv with (co_subst_co_co g_Triv c g_Triv).
    autorewrite with open_subst; eauto 2 with lc.
    auto.
  - induction F; done.
  - induction F; try done.
    destruct a.
    destruct s; try inversion H1.
    + simpl.
      eapply E_ConsTm; auto.
      * simpl in H1.
        inversion H1.
        eapply (H _ D _ _ A1 A2 T R'); eauto.
      * simpl in H0.
        inversion H1; subst; clear H1.
        apply (H0 _ D A1 A2 T R' _ _); auto.
      * inversion H1; subst; clear H1.
        auto.
  - inversion H1; subst; clear H1.
    induction F; try done.
    + inversion H4; subst; clear H4; auto.
    + destruct a.
      destruct s; try inversion H4.
      simpl; subst.
      apply E_ConsCo; auto.
      * apply (H _ D _ _ A1 A2 T R'); auto.
      * inversion H4; subst; clear H4.
         apply (H0 G0 D A1 A2 T R' F c1); auto.
         Unshelve. all:auto.
Admitted.

Lemma Typing_co_subst:
   forall G D c a1 a2 A R' b B (H : Typing (c ~ (Co (Eq a1 a2 A R')) ++ G) b B),
     DefEq G D a1 a2 A R' ->
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
  assert (AC: Ctx ((x1 ~ Tm A) ++ G)). 
  {apply ctx_wff_mutual in H1. assumption. }
  inversion AC; subst.
  assert (TV : Typing ([(x,Tm A)] ++ G) (a_Var_f x) A). 
  { eapply E_Var; eauto 3. 
    eapply E_ConsTm; eauto 2. }
  assert (CTX : Ctx ([(x1,Tm A)] ++ [(x, Tm A)] ++ G)).
  { eapply E_ConsTm; eauto 2. 
  pose M1 := (Typing_weakening H6 [(x,Tm A)] nil G).
  simpl_env in M1; eapply M1; eauto.
  } 
  pose K1 := Typing_weakening H1 [(x,Tm A)] [(x1, Tm A)] G eq_refl CTX;
               clearbody K1.
  pose K2 := Typing_tm_subst K1 TV.
  clearbody K2.
  repeat rewrite tm_subst_tm_tm_open_tm_wrt_tm in K2; auto.
  rewrite tm_subst_tm_tm_var in K2;
  repeat rewrite tm_subst_tm_tm_fresh_eq in K2.
  auto.
  eauto.
  eauto. Unshelve. constructor. 
Qed.

Lemma DefEq_swap : forall x1 x G A1 D b1 b2 B R,
   x1 `notin` fv_tm_tm_tm b1 \u fv_tm_tm_tm b2 \u fv_tm_tm_tm B
  -> x `notin` dom G \u {{ x1 }}
  -> DefEq ([(x1, Tm A1)] ++ G) D
          (open_tm_wrt_tm b1 (a_Var_f x1)) (open_tm_wrt_tm b2 (a_Var_f x1))
          (open_tm_wrt_tm B (a_Var_f x1)) R
  -> DefEq ([(x, Tm A1)] ++ G) D
          (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x))
          (open_tm_wrt_tm B (a_Var_f x)) R.
Proof.
  intros.
  assert (AC: Ctx ((x1 ~ Tm A1) ++ G)). eauto.
  inversion AC; subst.
  assert (TV : Typing ([(x,Tm A1)] ++ G) (a_Var_f x) A1).
  { eapply E_Var; eauto 3. 
    eapply E_ConsTm; eauto 2. }
  assert (CTX : Ctx ([(x1,Tm A1)] ++ [(x, Tm A1)] ++ G)).
  { eapply E_ConsTm; eauto 2.
  pose M1 := (Typing_weakening H6 [(x,Tm A1)] nil G).
  simpl_env in M1; eapply M1; eauto. }

  move: (DefEq_weakening H1 [(x,Tm A1)] [(x1, Tm A1)] G eq_refl CTX) => K1.
  move: (fourth tm_substitution_mutual _ _ _ _ _ _ K1 _ _ _ TV nil _ eq_refl) => K2.
  simpl_env in K2.
  rewrite -tm_subst_tm_tm_intro in K2; auto.
  rewrite -tm_subst_tm_tm_intro in K2; auto.
  rewrite -tm_subst_tm_tm_intro in K2; auto.
  Unshelve. all: auto.
Qed.

(* -------------------- *)


Lemma E_Pi_exists : forall x (G : context) (rho : relflag) (A B : tm),
      x `notin` dom G \u fv_tm_tm_tm B
      -> Typing ([(x, Tm A)] ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Star
      -> Typing G A a_Star
      -> Typing G (a_Pi rho A B) a_Star.
Proof.
  intros.
  pick fresh y and apply E_Pi; auto.
  replace a_Star with (open_tm_wrt_tm a_Star (a_Var_f y)); auto.
  eapply Typing_swap; eauto.
Qed.


Lemma E_Abs_exists :  forall x (G : context) (rho : relflag) (a A B : tm),
    x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm B
    -> Typing ([(x, Tm A)] ++ G) (open_tm_wrt_tm a (a_Var_f x)) 
                 (open_tm_wrt_tm B (a_Var_f x))
    -> Typing G A a_Star
    -> RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x))
    -> Typing G (a_UAbs rho a) (a_Pi rho A B).
Proof.
  intros.
  pick fresh y and apply E_Abs; eauto 2.
  eapply (@Typing_swap x); eauto.
  eapply rho_swap with (x := x); eauto.
Qed.
