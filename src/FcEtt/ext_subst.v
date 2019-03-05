
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
Require Import FcEtt.ett_match.
Require Import FcEtt.ett_roleing.

Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Generalizable All Variables.

Lemma Ctx_strengthen : forall G1 G2, Ctx (G2 ++ G1) -> Ctx G1.
  induction G2; [ | inversion 1]; simpl; auto.
Qed. 


Lemma binds_to_PropWff: forall G0 c phi,
    Ctx G0 ->
    binds c (Co phi) G0 -> PropWff G0 phi.
Proof.
  induction G0; auto; try done.
  intros c phi H H0.
  destruct a.
  destruct s; auto; try done.
  - case H0; try done.
    move => h0.
    inversion H; subst.
    have:   PropWff ( G0) phi . 
    apply (IHG0 c phi H4); eauto.
    move => h1.
    rewrite_env (nil ++ [(a, Tm A)] ++ G0).
    eapply PropWff_weakening; eauto.
  - destruct H0; subst.
    inversion H0; subst.
    inversion H; subst.
    rewrite_env (nil ++ [(c, Co phi)] ++ G0).
    eapply PropWff_weakening; eauto.
    rewrite_env (nil ++ [(a, Co phi0)] ++ G0).
    eapply PropWff_weakening; eauto.
    simpl.
    inversion H.
    eapply IHG0; eauto 2.
Qed.

Lemma binds_to_Typing : forall x A G, Ctx G -> binds x (Tm A) G -> Typing G A a_Star.
Proof.
  induction G; auto; try done.
  move=> CTX b.
  destruct a.
  destruct s; auto; try done.
  - inversion CTX. subst.
    case b; try done.
    move => h0.    
    inversion h0; subst.
    rewrite_env (nil ++ [(x, Tm A)] ++ G).
    eapply Typing_weakening; eauto.
    move => h1.
    rewrite_env (nil ++ [(a, Tm A0)] ++ G).
    eapply Typing_weakening; eauto.
  - inversion CTX. subst.
    case b; try done.
    move=> h0.
    rewrite_env (nil ++ [(a, Co phi)] ++ G).
    eapply Typing_weakening; eauto.
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

(* The second premise is no longer needed. *)
Lemma tm_subst_co_fresh_1 :
forall G a A a0 c s,
  Typing G a A -> Ctx ((c ~ s) ++ G) -> co_subst_co_tm a0 c A = A.
Proof.
  intros G a A a0 x s H H0.
  move: (Typing_context_fv H) => ?. split_hyp.
  apply co_subst_co_tm_fresh_eq.
  fsetdec.
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
  move: (Typing_context_fv H) => ?. split_hyp.
  apply co_subst_co_tm_fresh_eq.
  fsetdec.
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

Lemma tm_subst_tm_tm_a_App : forall a0 x a nu b,
   tm_subst_tm_tm a0 x (a_App a nu b) = a_App (tm_subst_tm_tm a0 x a) nu (tm_subst_tm_tm a0 x b).
Proof. intros. simpl. auto. Qed.

Lemma tm_subst_tm_tm_apply_pattern_args : forall a0 x pattern_args5 b, 
    (tm_subst_tm_tm a0 x (apply_pattern_args b pattern_args5)) = 
    (apply_pattern_args (tm_subst_tm_tm a0 x b) 
                        (List.map (tm_subst_tm_pattern_arg a0 x) pattern_args5)).
Proof.
  intros a0 x pa. induction pa; intros.
  simpl; auto.
  simpl.
  destruct a. simpl.
  rewrite IHpa. simpl. auto.
  simpl. rewrite IHpa. simpl. auto.
Qed.


Lemma BranchTyping_tm_subst :  
      forall G0 n R b B b2 aa B2 B3 C (H : BranchTyping G0 n R b B b2 aa B2 B3 C),
      forall G a A, Typing G a A ->
               forall F x, G0 = (F ++ (x ~ (Tm A)) ++ G) ->
                      BranchTyping (map (tm_subst_tm_sort a x) F ++ G) n R
                                   (tm_subst_tm_tm a x b)
                                   (tm_subst_tm_tm a x B)
                                   (tm_subst_tm_tm a x b2)
                                   (List.map (tm_subst_tm_pattern_arg a x) aa)
                                   (tm_subst_tm_tm a x B2)
                                   (tm_subst_tm_tm a x B3)
                                   (tm_subst_tm_tm a x C).
Proof.
  induction 1; intros; subst; simpl.
  all: try solve [
    cbn; E_pick_fresh y;
    autofresh with y;
    rewrite_subst_context;
    happly H0;
      uha;
      (autorewrite with subst_open_var std using move=>//=);
      move=>//; try fsetdec_fast; eauto 2 with lc;
    case: (y == x) => //; intros; subst; exfalso; fsetdec_fast].

  - autorewrite with subst_open; eauto 3 with lc.
    have LC: lc_tm a0. eauto 3 with lc.
    rewrite tm_subst_tm_tm_apply_pattern_args.
    eapply BranchTyping_Base; eauto 4 using tm_subst_tm_tm_lc_tm.

  Unshelve.
  all: unfold one; try match goal with |- _ = _ => reflexivity end; ea.
Qed.


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
    eapply E_Conv; try eapply DefEq_weaken_available; eauto 2. 
  - (* constants *)
    have h0: Typing nil A a_Star by eauto using toplevel_closed_const.
    eapply E_Const. eauto 2.
    erewrite (tm_subst_fresh_2 _ h0); auto. eauto 2.
    erewrite (tm_subst_fresh_2 _ h0); eauto 2.
  - move: (toplevel_inversion b) => [X [G [B [h1 [h0 [h3 h4]]]]]].
    erewrite (tm_subst_fresh_2 _ t); auto.
    eapply E_Fam; eauto 2.
  - (* E_Case *)
    eapply CON;
      try solve [match goal with H : _ |- _ => eapply H; eauto 3 end].
    all: exactly 1 goal.
    move: BranchTyping_tm_subst.
    try (let l := fresh l in rename F into l).
    with F do fun T =>
      move/(_ _ _ _ _ _ (a_Fam T) []) => /=.
    by apply; try ea; try done.
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
         have: PropWff G0 (Eq a b A R) by eapply binds_to_PropWff with (c:=c);  auto.
         inversion 1; subst.
         repeat rewrite tm_subst_tm_tm_fresh_eq; auto.
         all: show_fresh.
  - eapply E_Beta; eauto.
    eapply Beta_tm_subst; eauto 2 with lc.
  - autorewrite with open_subst.
    eauto. eauto using Typing_lc1.
  - eapply E_EqConv; eauto 2.
    eapply DefEq_weaken_available; eauto.
  - try rename F into get_OUT.
    eapply CON; eauto 3;
      move: BranchTyping_tm_subst;
      with F do fun T =>
        move/(_ _ _ _ _ _ (a_Fam T) []);
      apply; try ea; try done.
  - eapply E_LeftRel with (b := tm_subst_tm_tm a0 x b)
                          (b':= tm_subst_tm_tm a0 x b'); eauto 2.
    move: (CasePath_subst_tm x c (Typing_lc H5).1) => h. eauto.
    move: (CasePath_subst_tm x c0 (Typing_lc H5).1) => h. eauto.
    autorewrite with open_subst; eauto 2 with lc.
    autorewrite with open_subst; eauto 2 with lc.
    eapply DefEq_weaken_available; eauto 2.
  - eapply E_LeftIrrel with (b := tm_subst_tm_tm a0 x b)
                          (b':= tm_subst_tm_tm a0 x b'); eauto 2.
    move: (CasePath_subst_tm x c (Typing_lc H5).1) => h. eauto.
    move: (CasePath_subst_tm x c0 (Typing_lc H5).1) => h. eauto.
    autorewrite with open_subst; eauto 2 with lc.
    eapply H3; eauto.
    autorewrite with open_subst; eauto 2 with lc.
    eapply DefEq_weaken_available; eauto 2.
  - eapply E_Right with (a := tm_subst_tm_tm a0 x a)
                        (a':= tm_subst_tm_tm a0 x a'); eauto 2.
    move: (CasePath_subst_tm x c (Typing_lc H5).1) => h. eauto.
    move: (CasePath_subst_tm x c0 (Typing_lc H5).1) => h. eauto.
    eapply H; eauto 2.
    eapply H1; eauto 2.
    autorewrite with open_subst; eauto 2 with lc.
    autorewrite with open_subst; eauto 2 with lc.
    eapply DefEq_weaken_available; eauto 2.
  - eapply E_CLeft; eauto 2.
    move: (CasePath_subst_tm x c (Typing_lc H3).1) => h. eauto.
    move: (CasePath_subst_tm x c0 (Typing_lc H3).1) => h. eauto.
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
        auto. 
   Unshelve. all: try exact Rep.
   all: eauto.
Qed.

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

Lemma co_subst_rho_g: forall L x y a rho g
    (Neq: x <> y)
    (Fr2: y `notin` L \u fv_tm_tm_co g)
    (LC: lc_co g)
    (K : (forall x, x `notin` L -> RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x)))),
    RhoCheck rho y  (co_subst_co_tm g x (open_tm_wrt_tm a (a_Var_f y))).
Proof.
  intros.
  RhoCheck_inversion y; eauto with lngen lc.
Qed.

Lemma co_subst_rho_g2: forall L x y a rho g
    (Neq: x <> y)
    (Fr2: y `notin` L \u fv_tm_tm_co g)
    (LC: lc_co g)
    (K : (forall x, x `notin` L -> RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x)))),
    RhoCheck rho y (open_tm_wrt_tm (co_subst_co_tm g x a) (a_Var_f y)).
Proof.
  intros.
  RhoCheck_inversion y; eauto with lngen lc.
  replace (a_Var_f y) with (co_subst_co_tm g x (a_Var_f y)).
  autorewrite with open_subst; eauto with lngen lc.
  simpl. auto.
Qed.



Lemma co_subst_co_tm_apply_pattern_args: `{
  co_subst_co_tm g c (apply_pattern_args b pat_args) =
  apply_pattern_args
    (co_subst_co_tm g c b)
    (List.map (co_subst_co_pattern_arg g c) pat_args)}.
Proof.
  intros; move: b.
  induction pat_args; try done; move=> b /=.
  match goal with |- ?T => match T with context ctx [match ?x with | _ => _ end] => destruct x end end.
  all: by rewrite -> IHpat_args.
Qed.

Lemma BranchTyping_co_subst :
      forall G0 n R b B b2 aa B2 B3 C (H : BranchTyping G0 n R b B b2 aa B2 B3 C),
      forall G D A1 A2 T R' F c g,
        G0 = (F ++ (c ~ Co (Eq A1 A2 T R') ) ++ G)
        -> DefEq G D A1 A2 T R'
        -> lc_co g
        -> BranchTyping (map (co_subst_co_sort g c) F ++ G) n R
                                   (co_subst_co_tm g c b)
                                   (co_subst_co_tm g c B)
                                   (co_subst_co_tm g c b2)
                                   (List.map (co_subst_co_pattern_arg g c) aa)
                                   (co_subst_co_tm g c B2)
                                   (co_subst_co_tm g c B3)
                                   (co_subst_co_tm g c C).
Proof.
  induction 1; intros; subst.

  - move: BranchTyping_Base => /=.
    rewrite co_subst_co_tm_apply_pattern_args.
    apply.
    all: try eapply co_subst_co_tm_lc_tm; try done.
    solve_uniq.
    move: co_subst_co_tm_open_tm_wrt_co.
    move/(_ _ _ g_Triv) => /= <- //=.
  - cbn; E_pick_fresh y;
    autofresh with y;
    rewrite_subst_context; auto.
    happly H0.
      (autorewrite with subst_open_var std using move=>//).
      (autorewrite with subst_open_var std using move=>//).
      auto.
      (autorewrite with subst_open_var std using move=>//).
      auto.
    Unshelve.
    all: try simpl_env.
    all: try reflexivity.
    all: eauto 1.
  - cbn; E_pick_fresh y;
    autofresh with y;
    rewrite_subst_context; auto.
    happly H0.
      (autorewrite with subst_open_var std using move=>//).
      (autorewrite with subst_open_var std using move=>//).
      auto.
      (autorewrite with subst_open_var std using move=>//).
      auto.
    Unshelve.
    all: try simpl_env.
    all: try reflexivity.
    all: eauto 1.
  - cbn; E_pick_fresh y;
    autofresh with y;
    rewrite_subst_context; auto.
    happly H0.
      (autorewrite with subst_open_var std using move=>//).
      (autorewrite with subst_open_var std using move=>//).
      auto.
      (autorewrite with subst_open_var std using move=>//).
      auto.
    Unshelve.
    all: try simpl_env.
    all: try reflexivity.
    all: eauto 1.
  - cbn; E_pick_fresh y;
    autofresh with y;
    rewrite_subst_context; auto.
    happly H0.
      (autorewrite with subst_open_var std using move=>//).
      (autorewrite with subst_open_var std using move=>//).
      unhide Fr. auto.
      auto.
      (autorewrite with subst_open_var std using move=>//).
      unhide Fr. auto.
      auto.
    Unshelve.
    all: try simpl_env.
    all: try reflexivity.
    all: eauto 1.
Qed.


Lemma co_substitution_mutual :
    (forall G0 b B (H : Typing G0 b B),
        forall G D A1 A2 T R' F c g,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T R') ) ++ G)
          -> DefEq G D A1 A2 T R'
          -> lc_co g
          -> Typing (map (co_subst_co_sort g c) F ++ G)
                   (co_subst_co_tm g c b) (co_subst_co_tm g c B)) /\
    (forall G0 phi  (H : PropWff G0 phi ),
        forall G D A1 A2 T R' F c g,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T R') ) ++ G)
          -> DefEq G D A1 A2 T R'
          -> lc_co g
          -> PropWff (map (co_subst_co_sort g c) F ++ G) (co_subst_co_constraint g c phi) ) /\
    (forall G0 D0 p1 p2  (H : Iso G0 D0 p1 p2 ),
          forall G D A1 A2 T R' F c g,
            G0 = (F ++ (c ~ Co (Eq A1 A2 T R') ) ++ G)
            -> DefEq G D A1 A2 T R'
            -> lc_co g
            -> Iso (map (co_subst_co_sort g c) F ++ G) (union D (remove c D0))
                    (co_subst_co_constraint g c p1)
                    (co_subst_co_constraint g c p2) ) /\
    (forall G0 D0 A B T R'' (H : DefEq G0 D0 A B T R''),
        forall G D F c A1 A2 T1 R' g,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T1 R') ) ++ G)
          -> DefEq G D A1 A2 T1 R'
          -> lc_co g
          -> DefEq (map (co_subst_co_sort g c) F ++ G) (union D (remove c D0))
                  (co_subst_co_tm g c A) (co_subst_co_tm g c B)
                  (co_subst_co_tm g c T) R'') /\
    (forall G0 (H : Ctx G0),
        forall G D F c A1 A2 T R' g,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T R') ) ++ G)
          -> DefEq G D A1 A2 T R'
          -> lc_co g
          -> Ctx (map (co_subst_co_sort g c) F ++ G)).
Proof.
  ext_induction CON; 
  (* adds an assumption to the context saying what branch we are in. *)
  (* apply typing_wff_iso_defeq_mutual; *)
  auto; intros; subst; simpl.
  all: try first [ E_pick_fresh y; autorewrite with subst_open_var; eauto 2 with lc;
                    try rewrite_subst_context; eauto 3
                  | autorewrite with subst_open; eauto 2 with lc ].
  all: try eapply_E_subst; eauto 2.
  all: try solve [eapply (@co_subst_rho_g L); eauto 2].
  all: try solve [eapply_first_hyp; eauto 2; auto].
  all: try solve [eapply RolePath_subst_co; eauto 2 with lc].
  all: try solve [eapply DefEq_weaken_available; eauto 2].

  - apply binds_app_1 in b.
    case:b; try done.
    + move => h0.
      apply E_Var; auto.
      * apply (H _ D _ _ A1 A2 T R'); auto.
      * apply binds_app_2.
        eapply binds_map_2 with (f:= (co_subst_co_sort g c0)) in h0.
        simpl in h0. auto.
    + intros b.
      apply binds_app_1 in b.
      case:b; try solve [move => h0; inversion h0; inversion H0].
      move => h0.
      rewrite co_subst_co_tm_fresh_eq.
      move: (Ctx_uniq c) => u. destruct_uniq.

      have TA: Typing G0 A a_Star. eauto using binds_to_Typing.
      move: (Typing_context_fv TA) => ?. split_hyp. auto.
      apply E_Var; auto.
        by apply (H _ D _ _ A1 A2 T R').
  - eapply E_Conv; eauto 3.
  - (* E_Const *) 
    have h0: Typing nil A a_Star by eauto using toplevel_closed_const. 
    eapply E_Const. eauto 2. erewrite tm_subst_co_fresh_2; eauto 2.
    erewrite tm_subst_co_fresh_2; eauto 2. 
  - (* E_Fam *) 
    move: (toplevel_inversion b) => [X [G [B [h1 [h0 [h3 h4]]]]]].
    erewrite (tm_subst_co_fresh_2 _ t); auto.
    eapply E_Fam; eauto 2.
  - (* E_Case *) 
    eapply CON; try done;
      try solve [match goal with H : _ |- _ => eapply H; eauto 3 end].
      move: BranchTyping_co_subst => bt.
     happly bt.
     unshelve instantiate (1:= _); [refine (a_Fam _) | reflexivity].
     unshelve instantiate (1:= _); [refine ([]) | reflexivity].
  - eapply E_CPiFst; eauto 3.
    eapply H; eauto.
  -  destruct (binds_cases G0 F c _ c1 _ (Ctx_uniq c0) b0) as [ (bf & NE & Fr) | [(E1 & E2) | (bg & NE & Fr)]].
    + eapply E_Assn; eauto 3.
      apply binds_app_2.
      eapply binds_map_2 with (f := (co_subst_co_sort g c1)) in bf.
      simpl in bf.
      auto.
    + inversion E2. subst. clear E2.
      have: Ctx ([(c1, Co (Eq A1 A2 T1 R'))] ++ G0).
      apply (Ctx_strengthen _ F); auto.
      move => Hi2.
      inversion Hi2; subst; clear Hi2.
      inversion H6; subst; clear H6.
      repeat rewrite co_subst_co_tm_fresh_eq; eauto 2.
      all: try show_fresh. fsetdec. fsetdec.
      rewrite_env (nil ++(map (co_subst_co_sort g c1) F) ++ G0).
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
      all: try show_fresh. fsetdec. fsetdec.
      eapply E_Assn; eauto 1.
      eapply H; eauto 1.
      eapply binds_app_3; eauto 1.
      eauto.
  - eapply E_Beta; eauto 2.
    eapply Beta_co_subst; eauto.
  - autorewrite with open_subst.
    eauto 2.
    auto.
  - eapply E_PiFst; simpl in *; eauto 3.
  - eapply E_EqConv; eauto 2.
    eapply DefEq_weaken_available; eauto 1.
    eauto 2.
  - eapply E_IsoSnd; eauto 1.
    eapply H; eauto.
  - eapply CON; try done;
      try solve [match goal with H : _ |- _ => eapply H; eauto 3 end];
    move: BranchTyping_co_subst => bt;
    happly bt;
    only 1, 3: (unshelve instantiate (1:= _); [refine (a_Fam _) | reflexivity]);
    do 2 (only 1: unshelve instantiate (1:= _); [refine ([]) | reflexivity]).
  - eapply E_LeftRel with (b := co_subst_co_tm g c1 b) (b':= co_subst_co_tm g c1 b'); eauto 2.
    move: (CasePath_subst_co c1 c H7) => h. eauto.
    move: (CasePath_subst_co c1 c0 H7) => h. eauto.
    autorewrite with open_subst; eauto 2 with lc.
    (* eapply H3; eauto. *)
    autorewrite with open_subst; eauto 2 with lc.
    eapply DefEq_weaken_available; eauto 2.

  - eapply E_LeftIrrel with (b := co_subst_co_tm g c1 b)
                              (b':= co_subst_co_tm g c1 b'); eauto 2.
    move: (CasePath_subst_co c1 c H7) => h. eauto.
    move: (CasePath_subst_co c1 c0 H7) => h. eauto.
    autorewrite with open_subst; eauto 2 with lc.
    eapply H3; eauto.
    autorewrite with open_subst; eauto 2 with lc.
    eapply DefEq_weaken_available; eauto 2.
  - eapply E_Right with (a := co_subst_co_tm g c1 a)
                        (a':= co_subst_co_tm g c1 a'); eauto 2.
    move: (CasePath_subst_co c1 c H7) => h. eauto.
    move: (CasePath_subst_co c1 c0 H7) => h. eauto.
    simpl in H. eapply H; eauto 2.
    simpl in H1. eapply H1; eauto 2.
    autorewrite with open_subst; auto.
    simpl in H3. eapply H3; eauto 2.
    autorewrite with open_subst; auto.
    eapply DefEq_weaken_available; eauto 2.
  - eapply E_CLeft; eauto 2.
    move: (CasePath_subst_co c1 c H5) => h. eauto.
    move: (CasePath_subst_co c1 c0 H5) => h. eauto.
    eapply H; eauto 2.
    eapply H0; eauto 2.
    eapply DefEq_weaken_available; eauto 2.
    replace g_Triv with (co_subst_co_co g c1 g_Triv).
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
    + inversion H5; subst; clear H5; auto.
    + destruct a.
      destruct s; try inversion H5.
      simpl; subst.
      apply E_ConsCo; auto.
      * apply (H _ D _ _ A1 A2 T R'); auto.
      * inversion H5; subst; clear H5.
         apply (H0 G0 D A1 A2 T R' F c1); auto.

  Unshelve.
  all: unfold one; try match goal with |- _ = _ => reflexivity | |- DefEq _ _ _ _ _ _ => ea end; auto; ea.
Qed.

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

Ltac co_subst_hyp :=
  match goal with
  | [a0 : Typing _ (a_UAbs ?rho ?A1 ?b) _  |-  
          Typing _ (a_UAbs ?rho (_ ?A1) (_ ?b)) _ ] =>
      eapply (first co_substitution_mutual _ _ _ a0); eauto
  | [a0 :  Typing _ (a_Pi ?rho ?A1 ?B1) _ |- 
           Typing _ (a_Pi ?rho (_ ?A1) (_ ?B1)) _  ] =>
      eapply (first co_substitution_mutual _ _ _ a0); eauto
  | [a0 : Typing _ (a_UCAbs ?phi ?B) _  |- Typing _ (a_UCAbs (_ ?phi) (_ ?B)) _ ] =>
      eapply (first co_substitution_mutual _ _ _ a0); eauto
  | [a0 : Typing _ (a_CPi ?phi ?B) _ |- Typing _ (a_CPi (_ ?phi) (_ ?B)) _ ] =>
    eapply (first co_substitution_mutual _ _ _ a0); eauto
  | [ a0 : Typing _ (a_App ?a1 ?rho ?a2) _ |- 
           Typing _ (a_App (_ ?a1) ?rho (_ ?a2)) _ ] =>
    eapply (first co_substitution_mutual _ _ _ a0); eauto
  | [ a0 : Typing _ (a_CApp ?a1 ?g2) _ |- Typing _ (a_CApp (_ ?a1) (_ ?g2)) _ ] =>
    eapply (first co_substitution_mutual _ _ _ a0); eauto
  | [a0 : DefEq _  _  (a_CPi ?phi1 ?B1) (a_CPi ?phi2 ?B2) _  _ |-
     DefEq _ _  (a_CPi (_ ?phi1) _) (a_CPi (_ ?phi2) _) _ _  ] =>
    eapply DefEq_weaken_available;
    eapply (fourth co_substitution_mutual _ _ _ _ _ a0);
    eauto
  | [a0 : PropWff _ (Eq ?a ?b ?A ?R) |- PropWff _ (Eq (_ ?a) (_ ?b) (_ ?A) ?R) ] =>
    eapply (second co_substitution_mutual _ _ a0); eauto
  | [ a0 : Typing _ ?a _ |- Typing _ (_ ?a) _ ] =>
    eapply (first co_substitution_mutual _ _ _ a0); eauto
  | [a0 : DefEq _ _ ?a _ _ _ |- DefEq _ _ (_ ?a) _ _ _ ] =>
      eapply DefEq_weaken_available;
      eapply (fourth co_substitution_mutual _ _ _ _ _ a0);
      eauto
  end.

Ltac prepare_env :=
  match goal with
    | [ |- context[ (?x' ~ (?S (?sub ?a1 ?x ?A))) ++ map (?tm_subst_tm_sort ?a1 ?x) ?F ++ ?G ] ] =>
    rewrite app_assoc;
    replace (x' ~ (S (sub a1 x A)) ++  map (co_subst_co_sort a1 x) F) with
    (map (co_subst_co_sort a1 x) (x' ~ S A ++ F)); eauto 2 using map_app
    | [ |- context[ (?x' ~ (?S (Eq (?sub ?a) (?sub ?b) (?sub ?A) ?R))) ++ map (?tm_subst_tm_sort ?a1 ?x) ?F ++ ?G ] ] =>
    rewrite app_assoc;
    replace (x' ~ (S (Eq (sub a) (sub b) (sub A) R)) ++  map (co_subst_co_sort a1 x) F) with
    (map (co_subst_co_sort a1 x) (x' ~ S (Eq a b A R) ++ F)); eauto 2 using map_app

  end.



(* The co_swap version needs a special version of the 
   substitution lemma. *)

Lemma co_substitution_mutual2 :
    (forall G0 b B, Typing G0 b B -> True) /\
    (forall G0 phi, PropWff G0 phi -> True) /\
    (forall G0 D0 p1 p2 (H : Iso G0 D0 p1 p2),
        forall D G g A1 A2 A3 R F c, G0 = (F ++ (c ~ Co (Eq A1 A2 A3 R)) ++ G)
                              -> DefEq G D A1 A2 A3 R
                              -> lc_co g
                              -> c `notin` D0
                              -> Iso (map (co_subst_co_sort g c) F ++ G)
                                       D0
                                       (co_subst_co_constraint g c p1)
                                       (co_subst_co_constraint g c p2)) /\
    (forall G0 D0 a b A R1 (H : DefEq G0 D0 a b A R1),
        forall G D g F c A1 A2 A3 R, G0 = (F ++ (c ~ Co (Eq A1 A2 A3 R)) ++ G)
                              -> DefEq G D A1 A2 A3 R
                              -> lc_co g
                              -> c `notin` D0
                              -> DefEq (map (co_subst_co_sort g c) F ++ G) D0
                                         (co_subst_co_tm g c a) 
                                         (co_subst_co_tm g c b)
                                         (co_subst_co_tm g c A) R1) /\
    (forall G0, Ctx G0 -> True).
Proof. 
  ext_induction CON; 
  (* adds an assumption to the context saying what branch we are in. *)
  (* apply typing_wff_iso_defeq_mutual; *)
  intros; subst; auto.

  all: simpl co_subst_co_tm in *;
       simpl co_subst_co_co in *;
       simpl co_subst_co_constraint in *.

  all: match goal with
         [H1 : DefEq ?G0 ?D ?A1 ?A2 ?A3 ?R |- _ ] =>
         move: (DefEq_lc H1) => [? [? ?]] end.

  all: try (E_pick_fresh x'; eauto 2; try (have neq: c <> x' by fsetdec_fast)).


  all: (* rho check *)
      try (apply (@co_subst_rho_g2 L); auto).

  all: (* substitution dance for the body *)
       try (autorewrite with subst_open_var; auto;
            rewrite_body;
            autorewrite with subst_open; auto;
            try (simpl; case: (x' == c) => [?|//]; by subst)).

  all: try (prepare_env; repeat autorewrite with subst_open_var => //;
       eauto using app_assoc).

  all: try (autorewrite with open_subst; eauto 2; 
            eapply DefEq_weaken_available; eauto 2).

  all: try co_subst_hyp.

  all: try (autorewrite with subst_open; auto).

  all: try solve [eapply CON; eauto 2; try co_subst_hyp].

  - simpl; simpl in H.
    apply binds_app_1 in b0.
    case:b0; try done.
    + move => h0.
      * eapply E_Assn; eauto 2.
        eapply (fifth co_substitution_mutual); eauto.
        apply binds_app_2.
        apply binds_map with (f:= co_subst_co_sort g c1) in h0; eauto.
    + move => h0.
      destruct (eq_dec c c1); first subst c1. done.
      destruct (binds_app_1 _ c _ _ _ h0).
      pose K := ( binds_one_1 _ _ _ _ _ H0). done.
      eapply E_Assn; eauto 2.
      eapply (fifth co_substitution_mutual); eauto 1.
      assert (c1 `notin` dom G0).
      eapply fresh_mid_tail. eapply Ctx_uniq. eauto 1.
      assert (PropWff G0 (Eq a b A R)).
      eapply binds_to_PropWff; eauto 1.
      eapply Ctx_strengthen.
      eapply Ctx_strengthen. eauto 2.
      inversion H5. subst.
      move: (Typing_context_fv H10) => ?. 
      move: (Typing_context_fv H12) => ?.
      split_hyp.
      rewrite co_subst_co_tm_fresh_eq; auto. fsetdec.
      apply binds_app_3; eauto.
      rewrite co_subst_co_tm_fresh_eq.
      fsetdec.
      rewrite co_subst_co_tm_fresh_eq.
      fsetdec.
      auto.
  - eapply E_Beta; try co_subst_hyp; eauto.
    eapply Beta_co_subst; auto.
  - eapply E_TAppCong; eauto 2.
    eapply RolePath_subst_co; eauto.
    eapply RolePath_subst_co; eauto.
    autorewrite with open_subst.
    co_subst_hyp.
    auto.
  - eapply (first co_substitution_mutual _ _ _ t); eauto.
  - eapply (first co_substitution_mutual _ _ _ t0); eauto.
  - eapply (second co_substitution_mutual _ _ p); eauto.
  - eapply E_CAppCong; eauto 2.
    autorewrite with open_subst. 
    eapply DefEq_weaken_available.
    eapply (fourth co_substitution_mutual _ _ _ _ _ _ d0); eauto.
  - simpl. eapply CON; eauto 2. 
    eapply DefEq_weaken_available.
    eapply (fourth co_substitution_mutual _ _ _ _ _ _ d0); eauto.
    eapply DefEq_weaken_available.
    eapply (fourth co_substitution_mutual _ _ _ _ _ _ d1); eauto.
  - eapply CON; eauto 2.
    eapply DefEq_weaken_available.
    eapply (fourth co_substitution_mutual _ _ _ _ _ _ d0); eauto.
    co_subst_hyp.
  - eapply CON; eauto 2.
    replace nil with (List.map (co_subst_co_pattern_arg g c) nil); auto.
    replace (a_Fam F5) with (co_subst_co_tm g c (a_Fam F5)); try auto. 
    eapply BranchTyping_co_subst; eauto 2.
    replace nil with (List.map (co_subst_co_pattern_arg g c) nil); auto.
    replace (a_Fam F5) with (co_subst_co_tm g c (a_Fam F5)); try auto. 
    eapply BranchTyping_co_subst; eauto 2.
    replace (a_Fam F5) with (co_subst_co_tm g c (a_Fam F5)); try auto. 
    co_subst_hyp.
  - eapply CON; eauto 2.
    eapply (CasePath_subst_co _ c); auto.
    eapply (CasePath_subst_co _ c0); auto.
    all: try co_subst_hyp.
    all: fold co_subst_co_tm.
    autorewrite with open_subst; auto.
    eapply H3; eauto 2.
    replace a_Star with (co_subst_co_tm g c1 a_Star).
    autorewrite with open_subst; auto.
    eapply DefEq_weaken_available.
    eapply (fourth co_substitution_mutual _ _ _ _ _ _ d0); eauto.
    auto.
  - eapply CON; eauto 2.
    eapply (CasePath_subst_co _ c); auto.
    eapply (CasePath_subst_co _ c0); auto.
    all: try co_subst_hyp.
    eapply (first co_substitution_mutual _ _ _ t0); eauto.
    eapply (first co_substitution_mutual _ _ _ t2); eauto.
    autorewrite with open_subst; auto.
    eapply H3; eauto 2.
    eapply DefEq_weaken_available.
    autorewrite with open_subst; auto.
    replace a_Star with (co_subst_co_tm g c1 a_Star).
    eapply (fourth co_substitution_mutual _ _ _ _ _ _ d0); eauto.
    reflexivity.
  - eapply CON; eauto 2.
    eapply (CasePath_subst_co _ c); auto.
    eapply (CasePath_subst_co _ c0); auto.
    all: try co_subst_hyp.
    all: fold co_subst_co_tm.
    autorewrite with open_subst; auto.
    eapply H3; eauto 2.
    eapply DefEq_weaken_available.
    autorewrite with open_subst; auto.
    replace a_Star with (co_subst_co_tm g c1 a_Star).
    eapply (fourth co_substitution_mutual _ _ _ _ _ _ d0); eauto.
    reflexivity.
  - eapply CON; eauto 2.
    eapply (CasePath_subst_co _ c); auto.
    eapply (CasePath_subst_co _ c0); auto.
    all: try co_subst_hyp.
    all: fold co_subst_co_tm.
    eapply DefEq_weaken_available.
    eapply (fourth co_substitution_mutual _ _ _ _ _ _ d); eauto.
    replace (open_tm_wrt_co (co_subst_co_tm g c1 B) g_Triv) with 
        (co_subst_co_tm g c1 (open_tm_wrt_co B g_Triv)).
    eapply H2; eauto 2.
    autorewrite with subst_open. simpl. auto. auto.
Unshelve. 
  all: try eauto 1.
Qed.



Lemma DefEq_swap_co : forall x1 x G phi D b1 b2 B R,
   x1 `notin` fv_co_co_tm b1 \u fv_co_co_tm b2 \u fv_co_co_tm B \u dom G \u D
  -> x `notin` dom G \u {{ x1 }}
  -> DefEq ([(x1, Co phi)] ++ G) D
          (open_tm_wrt_co b1 (g_Var_f x1)) (open_tm_wrt_co b2 (g_Var_f x1))
          (open_tm_wrt_co B (g_Var_f x1)) R
  -> DefEq ([(x, Co phi)] ++ G) D
          (open_tm_wrt_co b1 (g_Var_f x)) (open_tm_wrt_co b2 (g_Var_f x))
          (open_tm_wrt_co B (g_Var_f x)) R.
Proof.
  intros.

  destruct phi as [a0 b0 A0 R0].
  assert (AC: Ctx ((x ~ Co (Eq a0 b0 A0 R0) ++ G))).
  move: (DefEq_Ctx H1) => h0. inversion h0. eauto.
  inversion AC; subst.

  assert (TV : DefEq ([(x,Co (Eq a0 b0 A0 R0))] ++ G) 
                   (dom ([(x,Co (Eq a0 b0 A0 R0))] ++ G)) a0 b0 A0 R0).
  { eapply E_Assn; eauto 3. 
    simpl. auto. }
  assert (CTX : Ctx ([(x1,Co (Eq a0 b0 A0 R0))] ++ [(x, Co (Eq a0 b0 A0 R0))] ++ G)).
  { eapply E_ConsCo; eauto 2.
  with PropWff do ltac:(fun h => 
    pose M1 := (PropWff_weakening h [(x,Co (Eq a0 b0 A0 R0))] nil G)).
  simpl_env in M1; eapply M1; eauto. }

  move: (DefEq_weakening H1 [(x,Co (Eq a0 b0 A0 R0))] 
                            [(x1, Co (Eq a0 b0 A0 R0))] G eq_refl CTX) => K1.
  move: (fourth co_substitution_mutual2 _ _ _ _ _ _ K1 
                ([(x,Co (Eq a0 b0 A0 R0))] ++ G) _ (g_Var_f x) 
                nil x1 _ _ _ _  eq_refl TV ltac:(auto)) => K2.  
  simpl_env in K2.
  rewrite -co_subst_co_tm_intro in K2; auto.
  rewrite -co_subst_co_tm_intro in K2; auto.
  rewrite -co_subst_co_tm_intro in K2; auto.
Qed.


Lemma BranchTyping_swap : forall x1 x G a b A A1 B C C' Apps args,
      x1 `notin` fv_tm_tm_tm a \u fv_tm_tm_tm b \u fv_tm_tm_tm A1 \u dom G
                  \u fv_tm_tm_tm C' \u fv_tm_tm_tm B \u fv_tm_tm_tm C
    -> Typing G A a_Star
    -> x `notin` dom G \u {{ x1 }}
    -> BranchTyping ([(x1, Tm A)] ++ G) Apps Nom a A1 b 
                   args
                   (open_tm_wrt_tm B (a_Var_f x1))
                   (open_tm_wrt_tm C (a_Var_f x1))
                   C'
    -> BranchTyping ([(x, Tm A)] ++ G) Apps Nom a A1 b 
                   (List.map (tm_subst_tm_pattern_arg (a_Var_f x) x1) args)
                   (open_tm_wrt_tm B (a_Var_f x))
                   (open_tm_wrt_tm C (a_Var_f x))
                   C'.
Proof. 
  intros.
  assert (AC: Ctx ((x1 ~ Tm A) ++ G)). constructor; eauto.
  inversion AC; subst.
  assert (TV : Typing ([(x,Tm A)] ++ G) (a_Var_f x) A).
  { eapply E_Var; eauto 3. 
    eapply E_ConsTm; eauto 2. }
  assert (CTX : Ctx ([(x1,Tm A)] ++ [(x, Tm A)] ++ G)).
  { eapply E_ConsTm; eauto 2.
  with (Typing G A a_Star) do ltac:(fun h => 
    pose M1 := (Typing_weakening h [(x,Tm A)] nil G)).
  simpl_env in M1; eapply M1; eauto. }

  with BranchTyping do ltac:(fun h => 
     move: (BranchTyping_weakening h [(x,Tm A)] [(x1, Tm A)] G eq_refl (Ctx_uniq CTX)) => K1).
  move: (BranchTyping_tm_subst K1 TV nil x1 eq_refl) => K2. 
  simpl_env in K2.
  rewrite (tm_subst_tm_tm_fresh_eq a) in K2; auto.
  rewrite (tm_subst_tm_tm_fresh_eq A1) in K2; auto.
  rewrite (tm_subst_tm_tm_fresh_eq b) in K2; auto.


  rewrite -tm_subst_tm_tm_intro in K2; auto.
  rewrite -tm_subst_tm_tm_intro in K2; auto.
  rewrite (tm_subst_tm_tm_fresh_eq C') in K2; auto.
  Unshelve. all: try exact Rep.
Qed.


Lemma BranchTyping_swap_co : forall x1 x G a b A1 B C C' Apps args phi,
      x1 `notin` fv_co_co_tm a \u fv_co_co_tm b \u fv_co_co_tm A1 \u dom G
                  \u fv_co_co_tm C' \u fv_co_co_tm B \u fv_co_co_tm C
    -> PropWff G phi
    -> x `notin` dom G \u {{ x1 }}
    -> BranchTyping ([(x1, Co phi)] ++ G) Apps Nom a A1 b 
                   args
                   (open_tm_wrt_co B (g_Var_f x1))
                   (open_tm_wrt_co C (g_Var_f x1))
                   C'
    -> BranchTyping ([(x, Co phi)] ++ G) Apps Nom a A1 b 
                   (List.map (co_subst_co_pattern_arg (g_Var_f x) x1) args)
                   (open_tm_wrt_co B (g_Var_f x))
                   (open_tm_wrt_co C (g_Var_f x))
                   C'.
Proof. 
  intros.
  destruct phi as [a0 b0 A0 R0].
  assert (AC: Ctx ((x ~ Co (Eq a0 b0 A0 R0) ++ G))). constructor; eauto.
  inversion AC; subst.

  assert (TV : DefEq ([(x,Co (Eq a0 b0 A0 R0))] ++ G) 
                   (dom ([(x,Co (Eq a0 b0 A0 R0))] ++ G)) a0 b0 A0 R0).
  { eapply E_Assn; eauto 3. 
    simpl. auto. }
  assert (CTX : Ctx ([(x1,Co (Eq a0 b0 A0 R0))] ++ [(x, Co (Eq a0 b0 A0 R0))] ++ G)).
  { eapply E_ConsCo; eauto 2.
  with PropWff do ltac:(fun h => 
    pose M1 := (PropWff_weakening h [(x,Co (Eq a0 b0 A0 R0))] nil G)).
  simpl_env in M1; eapply M1; eauto. } 

  with BranchTyping do ltac:(fun h => 
     move: (BranchTyping_weakening h [(x,Co (Eq a0 b0 A0 R0))] [(x1, Co (Eq a0 b0 A0 R0))] G eq_refl (Ctx_uniq CTX)) => K1).
  move: (BranchTyping_co_subst K1) => K2. 
  move: (@K2 ([(x,Co (Eq a0 b0 A0 R0))] ++ G)
              (dom ([(x,Co (Eq a0 b0 A0 R0))] ++ G)) a0 b0 A0 R0 nil x1 (g_Var_f x)) => K3.
 
  move: (K3 eq_refl TV ltac:(auto)) => K4. 
  rewrite (co_subst_co_tm_fresh_eq a) in K4; auto.
  rewrite (co_subst_co_tm_fresh_eq A1) in K4; auto.
  rewrite (co_subst_co_tm_fresh_eq b) in K4; auto.
  rewrite -co_subst_co_tm_intro in K4; auto.
  rewrite -co_subst_co_tm_intro in K4; auto.
  rewrite (co_subst_co_tm_fresh_eq C') in K4; auto.
Qed.


Lemma tm_subst_tm_pattern_args_fresh_eq : forall args x a,
  x `notin` fv_tm_tm_pattern_args args
  → List.map (tm_subst_tm_pattern_arg a x) args = args.
Proof.
  induction args. simpl; auto.
  intros. simpl in *.
  f_equal; auto.
  destruct a; simpl in *.
  rewrite tm_subst_tm_tm_fresh_eq; auto.
  rewrite tm_subst_tm_co_fresh_eq; auto.
Qed.

Lemma co_subst_co_pattern_args_fresh_eq : forall args x a,
  x `notin` fv_co_co_pattern_args args
  → List.map (co_subst_co_pattern_arg a x) args = args.
Proof.
  induction args. simpl; auto.
  intros. simpl in *.
  f_equal; auto.
  destruct a; simpl in *.
  rewrite co_subst_co_tm_fresh_eq; auto.
  rewrite co_subst_co_co_fresh_eq; auto.
Qed.



Lemma  BranchTyping_PiRole_exists : forall x, 
   `{ 
      BranchTyping (x ~ Tm A ++ G) Apps5 Nom a A1 b
                 (pattern_args5 ++ one (p_Tm (Role R) (a_Var_f x)))
                 (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm C (a_Var_f x)) C'
    -> x `notin` fv_tm_tm_tm A \u dom G \u fv_tm_tm_tm a \u fv_tm_tm_tm A1
             \u fv_tm_tm_tm b \u fv_tm_tm_pattern_args pattern_args5 
             \u fv_tm_tm_tm B \u fv_tm_tm_tm C \u fv_tm_tm_tm C'
    -> Typing G A a_Star 
    -> BranchTyping G (A_cons (A_Tm (Role R)) Apps5) Nom a A1 b pattern_args5
                      (a_Pi Rel A B) (a_Pi Rel A C) C' }.
Proof. 
  intros. 
  pick fresh y and apply BranchTyping_PiRole; auto.
  replace (pattern_args5 ++ one (p_Tm (Role R) (a_Var_f y))) with 
        (List.map (tm_subst_tm_pattern_arg (a_Var_f y) x)
                  (pattern_args5 ++ one (p_Tm (Role R) (a_Var_f x)))).
  eapply BranchTyping_swap; auto.
  rewrite map_app.
  simpl. 
  case h: (x == x); try done.
  f_equal.
  rewrite tm_subst_tm_pattern_args_fresh_eq; auto.
Qed.



Lemma BranchTyping_PiRel_exists : forall x,
   `{ BranchTyping (x ~ Tm A ++ G) Apps5 Nom a A1 b
                 (pattern_args5 ++ one (p_Tm (Rho Rel) (a_Var_f x)))
                 (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm C (a_Var_f x)) C' 
   -> x `notin` fv_tm_tm_tm A \u dom G \u fv_tm_tm_tm a \u fv_tm_tm_tm A1
             \u fv_tm_tm_tm b \u fv_tm_tm_pattern_args pattern_args5 
             \u fv_tm_tm_tm B \u fv_tm_tm_tm C \u fv_tm_tm_tm C'
   -> Typing G A a_Star
   -> BranchTyping G (A_cons (A_Tm (Rho Rel)) Apps5) Nom a A1 b pattern_args5
    (a_Pi Rel A B) (a_Pi Rel A C) C'}.
Proof. 
  intros. 
  pick fresh y and apply BranchTyping_PiRel; auto.
  replace (pattern_args5 ++ one (p_Tm (Rho Rel) (a_Var_f y))) with 
        (List.map (tm_subst_tm_pattern_arg (a_Var_f y) x)
                  (pattern_args5 ++ one (p_Tm (Rho Rel) (a_Var_f x)))).
  eapply BranchTyping_swap; auto.
  rewrite map_app.
  simpl. 
  case h: (x == x); try done.
  f_equal.
  rewrite tm_subst_tm_pattern_args_fresh_eq; auto.
Qed.

Lemma BranchTyping_PiIrrel_exists: forall x,
  `{  BranchTyping (x ~ Tm A ++ G) Apps5 Nom a A1 b
                 (pattern_args5 ++ one (p_Tm (Rho Irrel) a_Bullet))
                 (open_tm_wrt_tm B (a_Var_f x)) (open_tm_wrt_tm C (a_Var_f x)) C'
  -> x `notin` fv_tm_tm_tm A \u dom G \u fv_tm_tm_tm A1 \u fv_tm_tm_tm a
             \u fv_tm_tm_tm b \u fv_tm_tm_pattern_args pattern_args5 
             \u fv_tm_tm_tm B \u fv_tm_tm_tm C \u fv_tm_tm_tm C'
    -> Typing G A a_Star
    -> BranchTyping G (A_cons (A_Tm (Rho Irrel)) Apps5) Nom a A1 b pattern_args5
    (a_Pi Irrel A B) (a_Pi Irrel A C) C' }.
Proof. 
 intros. 
  pick fresh y and apply BranchTyping_PiIrrel; auto.
  replace (pattern_args5 ++ one (p_Tm (Rho Irrel) a_Bullet)) with 
        (List.map (tm_subst_tm_pattern_arg (a_Var_f y) x)
                  (pattern_args5 ++ one (p_Tm (Rho Irrel) a_Bullet))).
  eapply BranchTyping_swap; auto.
  rewrite map_app.
  simpl. 
  case h: (x == x); try done.
  f_equal.
  rewrite tm_subst_tm_pattern_args_fresh_eq; auto.
Qed.

Lemma BranchTyping_CPi_exists : forall c,
    `{ BranchTyping (c ~ Co phi ++ G) Apps5 Nom a A
                    b (pattern_args5 ++ one (p_Co g_Triv))
                    (open_tm_wrt_co B (g_Var_f c))
                    (open_tm_wrt_co C (g_Var_f c)) C'
     -> c `notin` 
           union (fv_co_co_tm a)
            (union (fv_co_co_tm b)
               (union (fv_co_co_tm A)
                  (union (dom G)
                     (union (fv_co_co_tm C') (union (fv_co_co_tm B) 
                                               (union (fv_co_co_pattern_args pattern_args5)     (fv_co_co_tm C)))))))
     -> PropWff G phi
     -> BranchTyping G (A_cons A_Co Apps5) Nom a A b pattern_args5
        (a_CPi phi B) (a_CPi phi C) C'}.
Proof. 
  intros. 
  pick fresh y and apply BranchTyping_CPi; auto.
  replace (pattern_args5 ++ one (p_Co g_Triv)) with 
        (List.map (co_subst_co_pattern_arg (g_Var_f y) c)
                  (pattern_args5 ++ one (p_Co g_Triv))).
  eapply BranchTyping_swap_co; auto.
  rewrite map_app.
  simpl.
  rewrite co_subst_co_pattern_args_fresh_eq; auto.
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
