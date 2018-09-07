Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Import FcEtt.utils.

Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.
Require Export FcEtt.toplevel.
Require Export FcEtt.fix_typing.
Require Import FcEtt.ett_roleing.
Require Import FcEtt.ett_path.
Require Import FcEtt.ett_par.

Require Import Coq.Sorting.Permutation.
Require Import Omega.

(** Patterns, agreement and substitution function **)

Inductive Pattern : tm -> Prop :=
  | Pattern_Fam : forall F, Pattern (a_Fam F)
  | Pattern_AppR : forall a1 R x, Pattern a1 -> Pattern (a_App a1 (Role R) (a_Var_f x))
  | Pattern_IApp : forall a1, Pattern a1 -> Pattern (a_App a1 (Rho Irrel) a_Bullet)
  | Pattern_CApp : forall a1, Pattern a1 -> Pattern (a_CApp a1 g_Triv).

Hint Constructors Pattern.

Inductive Pattern_like_tm : tm -> Prop :=
  | Pat_tm_Fam : forall F, Pattern_like_tm (a_Fam F)
  | Pat_tm_AppR : forall a1 R a2, Pattern_like_tm a1 ->
                                  Pattern_like_tm (a_App a1 (Role R) a2)
  | Pat_tm_IApp : forall a1, Pattern_like_tm a1 ->
                             Pattern_like_tm (a_App a1 (Rho Irrel) a_Bullet)
  | Pat_tm_CApp : forall a1, Pattern_like_tm a1 ->
                             Pattern_like_tm (a_CApp a1 g_Triv).

Hint Constructors Pattern_like_tm.

Fixpoint matchsubst a p b : tm := match (a,p) with
  | (a_Fam F, a_Fam F') => b
  | (a_App a1 (Role Nom) a2, a_App p1 (Role Nom) (a_Var_f x)) =>
         tm_subst_tm_tm a2 x (matchsubst a1 p1 b)
  | (a_App a1 (Role Rep) a2, a_App p1 (Role Rep) (a_Var_f x)) =>
         tm_subst_tm_tm a2 x (matchsubst a1 p1 b)
  | (a_App a1 (Rho Irrel) a_Bullet, a_App p1 (Rho Irrel) a_Bullet) =>
         matchsubst a1 p1 b
  | (a_CApp a1 g_Triv, a_CApp p1 g_Triv) => matchsubst a1 p1 b
  | (_,_) => b
  end.

Fixpoint head_const (a : tm) : tm := match a with
  | a_Fam F => a_Fam F
  | a_App a' nu b => head_const a'
  | a_CApp a' g_Triv => head_const a'
  | _ => a_Bullet
  end.


Lemma patctx_pattern : forall W G F p B A, PatternContexts W G F A p B ->
      Pattern p.
Proof. intros. induction H; eauto.
Qed.

Lemma patctx_pattern_head : forall W G F p B A, PatternContexts W G F A p B ->
      head_const p = a_Fam F.
Proof. intros. induction H; simpl; eauto.
Qed.

Lemma axiom_pattern : forall F p b A R1 Rs,
      binds F (Ax p b A R1 Rs) toplevel -> Pattern p.
Proof. intros. assert (P : Sig toplevel). apply Sig_toplevel.
       induction P. inversion H. inversion H. inversion H2. eauto.
       inversion H. inversion H5; subst. eapply patctx_pattern; eauto.
       eauto.
Qed.

Lemma axiom_pattern_head : forall F p b A R1 Rs,
      binds F (Ax p b A R1 Rs) toplevel -> head_const p = a_Fam F.
Proof. intros. assert (P : Sig toplevel). apply Sig_toplevel.
       induction P. inversion H. inversion H. inversion H2. eauto.
       inversion H. inversion H5; subst. eapply patctx_pattern_head; eauto.
       eauto.
Qed.

Lemma matchsubst_ind_fun : forall a p b b',
      MatchSubst a p b b' -> matchsubst a p b = b'.
Proof. intros. induction H.
        - simpl. auto.
        - destruct R; simpl. rewrite IHMatchSubst. auto.
          rewrite IHMatchSubst. auto.
        - simpl. auto.
        - simpl. auto.
Qed.

Corollary MatchSubst_function : forall a p b b1 b2,
      MatchSubst a p b b1 -> MatchSubst a p b b2 -> b1 = b2.
Proof. intros. apply matchsubst_ind_fun in H.
       apply matchsubst_ind_fun in H0. rewrite H in H0. auto.
Qed.

Lemma tm_pattern_agree_tm : forall a p, tm_pattern_agree a p -> Pattern_like_tm p.
Proof. intros. induction H; eauto.
Qed.

Lemma tm_pattern_agree_pattern : forall a p, tm_pattern_agree a p -> Pattern p.
Proof. intros. induction H; eauto.
Qed.

Lemma tm_pattern_agree_const_same : forall a p, tm_pattern_agree a p ->
         head_const a = head_const p.
Proof. intros. induction H; simpl; eauto.
Qed.

Lemma MatchSubst_match : forall a p b b', MatchSubst a p b b' ->
                                            tm_pattern_agree a p.
Proof. intros. induction H; eauto.
Qed.

Corollary MatchSubst_nexists : forall a p, ~(tm_pattern_agree a p) ->
                      forall b b', ~(MatchSubst a p b b').
Proof. intros. intro H'. apply MatchSubst_match in H'. contradiction.
Qed.

Lemma tm_pattern_agree_bullet_bullet : forall a p, tm_pattern_agree a p ->
                                       MatchSubst a p a_Bullet a_Bullet.
Proof. intros. induction H; eauto.
       assert (a_Bullet = tm_subst_tm_tm a2 x a_Bullet) by auto.
       assert (MatchSubst (a_App a1 (Role R) a2) (a_App p1 (Role R) (a_Var_f x))
       a_Bullet (tm_subst_tm_tm a2 x a_Bullet)). eauto. rewrite <- H1 in H2.
       auto.
Qed.

Lemma tm_pattern_agree_dec : forall a p, lc_tm a -> tm_pattern_agree a p \/
                                        ~(tm_pattern_agree a p).
Proof. intros. pose (P := match_dec p H). inversion P as [P1 | P2].
       left. eapply MatchSubst_match; eauto.
       right. intro. apply P2. eapply tm_pattern_agree_bullet_bullet; auto.
Qed.

Lemma tm_pattern_agree_app_contr : forall a p rho b, tm_pattern_agree a p ->
               tm_pattern_agree a (a_App p (Rho rho) b) -> False.
Proof. intros a p rho b H. induction H; intro H1; inversion H1; subst; eauto.
Qed.

Lemma tm_pattern_agree_capp_contr : forall a p, tm_pattern_agree a p ->
               tm_pattern_agree a (a_CApp p g_Triv) -> False.
Proof. intros a p H. induction H; intro H1; inversion H1; eauto.
Qed.

Corollary MatchSubst_app_nexists : forall a p b b',
          MatchSubst (a_App a (Rho Irrel) a_Bullet) p b b' ->
          ~(tm_pattern_agree a p).
Proof. intros. apply MatchSubst_match in H. intro. inversion H.
       subst. eapply tm_pattern_agree_app_contr; eauto.
Qed.

Corollary MatchSubst_capp_nexists : forall a p b b',
          MatchSubst (a_CApp a g_Triv) p b b' ->
          ~(tm_pattern_agree a p).
Proof. intros. apply MatchSubst_match in H. intro. inversion H.
       subst. eapply tm_pattern_agree_capp_contr; eauto.
Qed.

Lemma tm_pattern_agree_rename_inv_1 : forall a p p' b b' D,
      tm_pattern_agree a p -> Rename p b p' b' D -> tm_pattern_agree a p'.
Proof. intros. generalize dependent p'. generalize dependent D.
       generalize dependent b'.
       induction H; intros b' D p' H1; inversion H1; subst; eauto.
Qed.

Lemma tm_pattern_agree_rename_inv_2 : forall a p p' b b' D,
      tm_pattern_agree a p -> Rename p' b' p b D -> tm_pattern_agree a p'.
Proof. intros. generalize dependent p'. generalize dependent D.
       generalize dependent b.
       induction H; intros b D p' H1; inversion H1; subst; eauto.
Qed.

Inductive Pi_CPi_head_form : tm -> Prop :=
  | head_Pi : forall rho A B, Pi_CPi_head_form (a_Pi rho A B)
  | head_CPi : forall phi B, Pi_CPi_head_form (a_CPi phi B).
Hint Constructors Pi_CPi_head_form.

Inductive Abs_CAbs_head_form : tm -> Prop :=
  | head_Abs : forall rho a, Abs_CAbs_head_form (a_UAbs rho a)
  | head_CAbs : forall a, Abs_CAbs_head_form (a_UCAbs a).
Hint Constructors Abs_CAbs_head_form.

Inductive App_CApp_head_form : tm -> Prop :=
  | head_App : forall nu a b, App_CApp_head_form (a_App a nu b)
  | head_CApp : forall a, App_CApp_head_form (a_CApp a g_Triv).
Hint Constructors App_CApp_head_form.

Inductive Const_App_CApp_head_form : tm -> Prop :=
   | head_Fam : forall F, Const_App_CApp_head_form (a_Fam F)
   | head_App_CApp : forall a, App_CApp_head_form a -> Const_App_CApp_head_form a.
Hint Constructors Const_App_CApp_head_form.

Lemma tm_pattern_agree_tm_const_app : forall a p, tm_pattern_agree a p ->
       Const_App_CApp_head_form a.
Proof. intros. induction H; eauto.
Qed.

(* If a agrees with p, then a can be substituted for p in b *)

Lemma MatchSubst_exists : forall a p, tm_pattern_agree a p -> forall b,
                          lc_tm b -> exists b', MatchSubst a p b b'.
Proof. intros a p H. induction H; intros.
        - exists b; auto.
        - pose (P := IHtm_pattern_agree b H1). inversion P as [b1 Q].
          exists (tm_subst_tm_tm a2 x b1). eauto.
        - pose (P := IHtm_pattern_agree b H0). inversion P as [b1 Q].
          exists b1; eauto.
        - pose (P := IHtm_pattern_agree b H0). inversion P as [b1 Q].
          exists b1; eauto.
Qed.

Lemma matchsubst_fun_ind : forall a p b b', tm_pattern_agree a p -> lc_tm b ->
      matchsubst a p b = b' -> MatchSubst a p b b'.
Proof. intros. generalize dependent b. generalize dependent b'.
       induction H; intros; eauto.
        - simpl in H1. rewrite <- H1. auto.
        - destruct R. simpl in H2. rewrite <- H2. eauto.
          simpl in H2. rewrite <- H2. eauto.
Qed.


Definition chain_substitution := fold_right (fun y => tm_subst_tm_tm (snd y) (fst y)).

Fixpoint tm_pattern_correspond (a p : tm) : list (atom * tm) := match (a,p) with
  | (a_Fam F, a_Fam F') => nil
  | (a_App a1 (Role Nom) a2, a_App p1 (Role Nom) (a_Var_f x)) =>
         (x, a2) :: tm_pattern_correspond a1 p1
  | (a_App a1 (Role Rep) a2, a_App p1 (Role Rep) (a_Var_f x)) =>
         (x, a2) :: tm_pattern_correspond a1 p1
  | (a_App a1 (Rho Irrel) a_Bullet, a_App p1 (Rho Irrel) a_Bullet) =>
         tm_pattern_correspond a1 p1
  | (a_CApp a1 g_Triv, a_CApp p1 g_Triv) => tm_pattern_correspond a1 p1
  | (_,_) => nil
  end.

Lemma chain_sub_fam : forall l F,
                      chain_substitution (a_Fam F) l = a_Fam F.
Proof. intros. induction l. simpl; auto. destruct a; simpl. rewrite IHl.
       auto.
Qed.
(*
Lemma chain_sub_app : forall l nu a1 a2,
           chain_substitution l (a_App a1 nu a2) =
           a_App (chain_substitution l a1) nu (chain_substitution l a2).
Proof. intros. induction l. simpl; auto. destruct a; simpl. rewrite IHl.
       auto.
Qed.

Lemma chain_sub_var : forall l x, exists y, 
                      chain_substitution (map a_Var_f l) (a_Var_f x) = a_Var_f y.
Proof. intros. induction l. simpl. exists x; auto. destruct a.
       simpl. inversion IHl as [y P]. rewrite P. destruct (a == y).
       subst. exists t; simpl. destruct (y == y). auto. contradiction.
       exists y. simpl. destruct (y == a). symmetry in e. contradiction.
       auto.
Qed.

Lemma chain_sub_bullet : forall l, chain_substitution l a_Bullet = a_Bullet.
Proof. intros. induction l; try destruct a; simpl; try rewrite IHl; eauto.
Qed.

Lemma chain_sub_capp : forall l a, chain_substitution l (a_CApp a g_Triv) =
                       a_CApp (chain_substitution l a) g_Triv.
Proof. intros. induction l. simpl; auto. destruct a0; simpl. rewrite IHl; auto.
Qed.

Lemma Path_pat_rename_consist : forall a p l, Path_pat_consist a p ->
              Path_pat_consist a (chain_substitution (map a_Var_f l) p).
Proof. intros. induction H.
        - rewrite chain_sub_fam. eauto.
        - rewrite chain_sub_app. pose (P := chain_sub_var l x).
          inversion P as [y Q]. rewrite Q. eauto.
        - rewrite chain_sub_app. rewrite chain_sub_bullet. eauto.
        - rewrite chain_sub_capp; eauto.
Qed.


Lemma MatchSubst_permutation : forall a p b,
              chain_substitution (permutation a p) b = matchsubst a p b.
Proof. intros. generalize dependent p. generalize dependent b.
       induction a; intros; eauto.
       all: try destruct g; try destruct nu; eauto.
       all: try destruct R; try destruct rho; eauto.
        - destruct p; eauto. destruct nu; eauto. destruct R; eauto.
          destruct p2; eauto. simpl. rewrite IHa1. auto.
        - destruct p; eauto. destruct nu; eauto. destruct R; eauto.
          destruct p2; eauto. simpl. rewrite IHa1. auto.
        - destruct a2; eauto. destruct p; eauto. destruct nu; eauto.
          destruct rho; eauto. destruct p2; eauto.
        - destruct p; eauto. destruct g; eauto.
        - destruct p; eauto.
Qed.

Inductive ICApp : tm -> tm -> Prop :=
   | ICApp_refl : forall a, ICApp a a
   | ICApp_IApp : forall a1 a2, ICApp a1 a2 -> ICApp a1 (a_App a2 (Rho Irrel) a_Bullet)
   | ICApp_CApp : forall a1 a2, ICApp a1 a2 -> ICApp a1 (a_CApp a2 g_Triv).

Lemma nonempty_perm : forall a p x l, x :: l = permutation a p ->
      exists a1 a2 p1 y, (ICApp (a_App a1 (Role Nom) a2) a /\ 
              ICApp (a_App p1 (Role Nom) (a_Var_f y)) p /\ x = (y, a2)
              /\ l = permutation a1 p1) \/
              (ICApp (a_App a1 (Role Rep) a2) a /\ 
              ICApp (a_App p1 (Role Rep) (a_Var_f y)) p /\ x = (y, a2)
              /\ l = permutation a1 p1).
Proof. intros a. induction a; intros p y l H; try (inversion H; fail).
       destruct nu; try (inversion H; fail).
       destruct R; try (inversion H; fail).
       destruct p; try (inversion H; fail).
       destruct nu; try (inversion H; fail).
       destruct R; try (inversion H; fail).
       destruct p2; try (inversion H; fail).
       inversion H. exists a1, a2, p1, x. left; repeat split.
       eapply ICApp_refl. eapply ICApp_refl.
       destruct p; try (inversion H; fail).
       destruct nu; try (inversion H; fail).
       destruct R; try (inversion H; fail).
       destruct p2; try (inversion H; fail).
       inversion H. exists a1, a2, p1, x. right; repeat split.
       eapply ICApp_refl. eapply ICApp_refl.
       destruct rho; try (inversion H; fail).
       destruct a2; try (inversion H; fail).
       destruct p; try (inversion H; fail).
       destruct nu; try (inversion H; fail).
       destruct rho; try (inversion H; fail).
       destruct p2; try (inversion H; fail).
       simpl in H. pose (P := IHa1 p1 y l ltac:(auto)).
       inversion P as [a2 [a3 [p2 [y0 [Q1 | Q2]]]]]. 
       exists a2, a3, p2, y0. inversion Q1 as [S1 [S2 [S3 S4]]].
       left; repeat split.
       eapply ICApp_IApp; auto.
       eapply ICApp_IApp; auto. auto. auto.
       exists a2, a3, p2, y0. inversion Q2 as [T1 [T2 [T3 T4]]]. 
       right; repeat split.
       eapply ICApp_IApp; auto.
       eapply ICApp_IApp; auto. auto. auto.
       destruct g; try (inversion H; fail).
       destruct p; try (inversion H; fail).
       destruct g; try (inversion H; fail).
       simpl in H. pose (P := IHa p y l ltac:(auto)).
       inversion P as [a2 [a3 [p2 [y0 [Q1 | Q2]]]]]. 
       exists a2, a3, p2, y0. inversion Q1 as [S1 [S2 [S3 S4]]].
       left; repeat split.
       eapply ICApp_CApp; auto.
       eapply ICApp_CApp; auto. auto. auto.
       exists a2, a3, p2, y0. inversion Q2 as [T1 [T2 [T3 T4]]]. 
       right; repeat split.
       eapply ICApp_CApp; auto.
       eapply ICApp_CApp; auto. auto. auto.
       destruct p; try (inversion H; fail).
Qed.

Lemma fv_ICApp : forall a1 a2 x, ICApp a1 a2 -> x `in` fv_tm_tm_tm a1 <->
                  x `in` fv_tm_tm_tm a2.
Proof. intros. generalize dependent x.
       induction H; intro.
         - split; auto.
         - pose (P := IHICApp x). inversion P as [P1 P2].
           split; intro; simpl in *; fsetdec.
         - pose (P := IHICApp x). inversion P as [P1 P2].
           split; intro; simpl in *; fsetdec.
Qed.

Lemma fv_perm_1 : forall a p l x a', l = permutation a p -> In (x,a') l ->
                    x `in` fv_tm_tm_tm p.
Proof. intros. generalize dependent a. generalize dependent p.
       dependent induction l; intros. inversion H0.
       inversion H0. subst. apply nonempty_perm in H.
       inversion H as [a1 [a2 [p1 [y [Q1 | Q2]]]]].
       inversion Q1 as [S1 [S2 [S3 S4]]].
       eapply (fv_ICApp x) in S2. inversion S3; subst. simpl in S2.
       fsetdec. inversion Q2 as [T1 [T2 [T3 T4]]].
       eapply (fv_ICApp x) in T2. inversion T3; subst. simpl in T2.
       fsetdec. apply nonempty_perm in H.
       inversion H as [a1 [a2 [p1 [y [Q1 | Q2]]]]].
       inversion Q1 as [S1 [S2 [S3 S4]]].
       eapply (fv_ICApp x) in S2. apply S2. simpl. apply union_iff.
       left. eapply IHl; eauto.
       inversion Q2 as [T1 [T2 [T3 T4]]].
       eapply (fv_ICApp x) in T2. apply T2. simpl. apply union_iff.
       left. eapply IHl; eauto.
Qed.

Lemma fv_perm_2 : forall a p l x a', l = permutation a p -> In (x,a') l ->
                  forall y, y `in` fv_tm_tm_tm a' -> y `in` fv_tm_tm_tm a.
Proof. intros. generalize dependent a. generalize dependent p.
       dependent induction l; intros. inversion H0.
       inversion H0. subst. apply nonempty_perm in H.
       inversion H as [a1 [a2 [p1 [z [Q1 | Q2]]]]].
       inversion Q1 as [S1 [S2 [S3 S4]]].
       eapply (fv_ICApp y) in S1. inversion S3; subst. simpl in S1.
       fsetdec. inversion Q2 as [T1 [T2 [T3 T4]]].
       eapply (fv_ICApp y) in T1. inversion T3; subst. simpl in T1.
       fsetdec. apply nonempty_perm in H.
       inversion H as [a1 [a2 [p1 [z [Q1 | Q2]]]]].
       inversion Q1 as [S1 [S2 [S3 S4]]].
       eapply (fv_ICApp y) in S1. apply S1. simpl. apply union_iff.
       left. eapply IHl; eauto.
       inversion Q2 as [T1 [T2 [T3 T4]]].
       eapply (fv_ICApp y) in T1. apply T1. simpl. apply union_iff.
       left. eapply IHl; eauto.
Qed.

Fixpoint rang (L : list (atom * tm)) : atoms :=
   match L with
   | nil => empty
   | (x, a) :: l => fv_tm_tm_tm a \u rang l
   end.

Lemma dom_Perm : forall A (L : list (atom * A)) L', Permutation L L' ->
                                                        dom L [=] dom L'.
Proof. intros. induction H; eauto. fsetdec. destruct x; simpl. fsetdec.
       destruct x, y. simpl. fsetdec. eapply transitivity; eauto.
Qed.

Lemma rang_Perm : forall L L', Permutation L L' -> rang L [=] rang L'.
Proof. intros. induction H; eauto. fsetdec. destruct x; simpl. fsetdec.
       destruct x, y. simpl. fsetdec. eapply transitivity; eauto.
Qed.

Lemma uniq_Perm : forall A (L : list (atom * A)) L', Permutation L L' ->
                                                      uniq L -> uniq L'.
Proof. intros. induction H; eauto. destruct x. apply uniq_cons_iff in H0.
       inversion H0. eapply uniq_cons_3; eauto. apply dom_Perm in H. fsetdec.
       destruct x, y. solve_uniq.
Qed.

Lemma Chain_sub_Permutation : forall L L' b,
        uniq L -> (forall x, x `in` dom L -> x `notin` rang L) ->
        Permutation L L' -> chain_substitution L b = chain_substitution L' b.
Proof. intros.
       dependent induction H1; intros.
         - auto.
         - simpl. destruct x. erewrite IHPermutation; eauto 1.
           solve_uniq. intros. simpl in H0. pose (P := H0 x ltac:(auto)).
           fsetdec.
         - destruct x, y. simpl. rewrite tm_subst_tm_tm_tm_subst_tm_tm.
           rewrite (tm_subst_tm_tm_fresh_eq t). auto. simpl in H0.
           pose (P := H0 a0 ltac:(auto)). fsetdec. simpl in H0.
           pose (P := H0 a ltac:(auto)). fsetdec.
           solve_uniq.
         - apply transitivity with (y := chain_substitution l' b).
           eapply IHPermutation1; eauto. eapply IHPermutation2.
           eapply uniq_Perm; eauto. pose (P := H1_). pose (Q := H1_).
           apply dom_Perm in P. apply rang_Perm in Q. intros.
           pose (S := H0 x). fsetdec.
Qed.

Lemma perm_pat_subst : forall a p x y a' l l1 l2, l = permutation a p ->
      uniq l -> y `notin` dom l -> l = l1 ++ (x, a') :: l2 ->
      permutation a (tm_subst_tm_tm (a_Var_f y) x p) = l1 ++ (y, a') :: l2.
Proof. intros. generalize dependent a. generalize dependent p.
       generalize dependent l1. generalize dependent l2.
       dependent induction l; intros. destruct l1; inversion H2.
       destruct l1; simpl in *. inversion H2; subst.
       apply nonempty_perm in H. inversion H as [a1 [a2 [p1 [z [P1 | P2]]]]].
       inversion P1 as [Q1 [Q2 [Q3 Q4]]]. inversion Q3; subst.
       solve_uniq. fsetdec.

Lemma chain_sub_subst : forall a p b x y,
    uniq (permutation a p) -> (forall z, z `in` p -> z `notin` fv_tm_tm_tm a) ->
    x `in` fv_tm_tm_tm p -> y `notin` fv_tm_tm_tm a ->
    chain_substitution (permutation a (tm_subst_tm_tm (a_Var_f y) x p))
    tm_subst_tm_tm (a_Var_f y) x b) = chain_substitution (permutation a p) b.
Proof. intros. rewrite MatchSubst_permutation. rewrite MatchSubst_permutation.

Lemma rename_chain_sub : forall a l p b,
 chain_substitution (permutation a (chain_substitution (map a_Var_f l) p))
 (chain_substitution (map a_Var_f l) b) = chain_substitution (permutation a p) b.
Proof. intros. generalize dependent p; generalize dependent b.
       induction l; intros. simpl. auto.
       destruct a0. rewrite map_cons.
       rewrite (Chain_sub_Permutation (L := [(a0, a_Var_f t)] ++ map a_Var_f l)
       (L' := map a_Var_f l ++ ([(a0, a_Var_f t)]))).
       rewrite chain_sub_append.
       rewrite (Chain_sub_Permutation (L := [(a0, a_Var_f t)] ++ map a_Var_f l)
       (L' := map a_Var_f l ++ ([(a0, a_Var_f t)]))).
       rewrite chain_sub_append. simpl. rewrite IHl.

Definition Nice a p := Path_pat_consist a p /\
              (forall x, x `in` fv_tm_tm_tm p -> x `notin` fv_tm_tm_tm a) /\
               uniq (permutation a p).

Fixpoint matchsubst2 a p b : tm := match (a,p) with
  | (a_Fam F, a_Fam F') => if F == F' then b else a_Bullet
  | (a_App a1 (Role Nom) a2, a_App p1 (Role Nom) (a_Var_f x)) =>
         tm_subst_tm_tm a2 x (matchsubst a1 p1 b)
  | (a_App a1 (Role Rep) a2, a_App p1 (Role Rep) (a_Var_f x)) =>
         tm_subst_tm_tm a2 x (matchsubst a1 p1 b)
  | (a_App a1 (Rho Irrel) a_Bullet, a_App p1 (Rho Irrel) a_Bullet) =>
         matchsubst a1 p1 b
  | (a_CApp a1 g_Triv, a_CApp p1 g_Triv) => matchsubst a1 p1 b
  | (_,_) => a_Bullet
  end.

Lemma matchsubst_subst : forall a p b x y, x `notin` fv_tm_tm_tm a ->
      y `notin` fv_tm_tm_tm a -> matchsubst2 a p b =
    matchsubst2 a (tm_subst_tm_tm (a_Var_f y) x p) (tm_subst_tm_tm (a_Var_f y) x b).
Proof. intros. generalize dependent p. generalize dependent b.
       induction a; intros; eauto.
         - destruct nu; eauto. destruct R; eauto.
           destruct p; eauto. simpl. destruct (x0 == x); auto.
           destruct nu; eauto. destruct R; eauto. destruct p2; eauto.
           simpl. destruct (x0 == x); auto.

Fixpoint matchsubst2 a p b : tm := match (a,p) with
  | (a_Fam F, a_Fam F') => if F == F' then b else a_Bullet
  | (a_App a1 (Role Nom) a2, a_App p1 (Role Nom) (a_Var_f x)) =>
         matchsubst2 a1 p1 (tm_subst_tm_tm a2 x b)
  | (a_App a1 (Role Rep) a2, a_App p1 (Role Rep) (a_Var_f x)) =>
         matchsubst2 a1 p1 (tm_subst_tm_tm a2 x b)
  | (a_App a1 (Rho Irrel) a_Bullet, a_App p1 (Rho Irrel) a_Bullet) =>
         matchsubst a1 p1 b
  | (a_CApp a1 g_Triv, a_CApp p1 g_Triv) => matchsubst a1 p1 b
  | (_,_) => a_Bullet
  end.

Lemma matchsubst_matchsubst2 : forall a p b,
      (forall x, x `in` fv_tm_tm_tm a -> x `notin` fv_tm_tm_tm p) ->
       matchsubst a p b = matchsubst2 a p b.
Proof. intros. generalize dependent p. generalize dependent b.
       induction a; intros; eauto. destruct p; eauto.
       destruct p2; eauto. destruct nu; eauto.
       destruct nu0; eauto. destruct R, R0; eauto; simpl.

*)
Lemma MatchSubst_lc_1 : forall a p b b', MatchSubst a p b b' →  lc_tm a.
Proof.
  induction 1; auto.
Qed.

Lemma MatchSubst_lc_2 : forall a p b b', MatchSubst a p b b' →  lc_tm b.
Proof.
  induction 1; auto.
Qed.

Lemma MatchSubst_lc_3 : forall a p b b', MatchSubst a p b b' →  lc_tm b'.
Proof.
  induction 1;
    eauto using tm_subst_tm_tm_lc_tm, co_subst_co_tm_lc_tm.
Qed.
(*
Lemma ax_const_rs_nil : forall F F0 a A R Rs S, Sig S ->
                 binds F (Ax (a_Fam F0) a A R Rs) S -> F = F0 /\ Rs = nil.
Proof. intros. induction H. inversion H0. inversion H0.
       inversion H3. eauto. inversion H0. inversion H5; subst.
       inversion H2; subst. inversion H2; auto. eauto.
Qed.

Lemma match_subst_roleing : forall W a R p b b', Roleing W a R ->
                   MatchSubst a p b b' -> Roleing W b' R.
Proof. Admitted.

Lemma match_path : forall F p a A R Rs a0 b, binds F (Ax p a A R Rs) toplevel ->
                          MatchSubst a0 p a b -> Path a0 F nil.
Proof. intros. induction H0. pose (H' := H).
       eapply ax_const_rs_nil in H'. inversion H'; subst.
       eauto. apply Sig_toplevel. econstructor. auto.
       Admitted.
*)

Lemma ApplyArgs_lc_3 : forall a b c, ApplyArgs a b c → lc_tm c.
Proof.
  induction 1; eauto.
Qed.

Lemma tm_subpattern_agree_const_same : forall a p, tm_subpattern_agree a p ->
 head_const a = head_const p.
Proof. intros. induction H; simpl; eauto.
       apply tm_pattern_agree_const_same; auto.
Qed.

Fixpoint pattern_length (a : tm) : nat := match a with
   a_Fam F => 0
 | a_App a nu b => pattern_length a + 1
 | a_CApp a g_Triv => pattern_length a + 1
 | _ => 0
 end.

Lemma tm_pattern_agree_length_same : forall a p, tm_pattern_agree a p ->
      pattern_length a = pattern_length p.
Proof. intros. induction H; simpl; eauto.
Qed.

Lemma tm_subpattern_agree_length_leq : forall a p, tm_subpattern_agree a p ->
      pattern_length a <= pattern_length p.
Proof. intros. induction H; simpl; try omega.
       eapply tm_pattern_agree_length_same in H; omega.
Qed.

Lemma tm_subpattern_agree_abs_cabs_contr : forall a p,
      tm_subpattern_agree a p -> Abs_CAbs_head_form a -> False.
Proof. intros. dependent induction H; eauto. inversion H0; subst; inversion H.
Qed.

Lemma tm_subpattern_agree_pi_cpi_contr : forall a p,
      tm_subpattern_agree a p -> Pi_CPi_head_form a -> False.
Proof. intros. dependent induction H; eauto. inversion H0; subst; inversion H.
Qed.

Lemma tm_subpattern_agree_pattern_contr : forall R a F b1 b2 p,
                tm_subpattern_agree (a_Pattern R a F b1 b2) p -> False.
Proof. intros. dependent induction H; eauto. inversion H.
Qed.

Lemma tm_subpattern_agree_app_contr : forall rho a b p, tm_pattern_agree a p ->
                  tm_subpattern_agree (a_App a (Rho rho) b) p -> False.
Proof. intros. apply tm_pattern_agree_length_same in H.
       apply tm_subpattern_agree_length_leq in H0. simpl in H0. omega.
Qed.

Lemma tm_subpattern_agree_capp_contr : forall a p, tm_pattern_agree a p ->
                  tm_subpattern_agree (a_CApp a g_Triv) p -> False.
Proof. intros. apply tm_pattern_agree_length_same in H.
       apply tm_subpattern_agree_length_leq in H0. simpl in H0. omega.
Qed.

Lemma tm_subpattern_agree_sub_app : forall a rho b p,
              tm_subpattern_agree (a_App a (Rho rho) b) p ->
              tm_subpattern_agree a p.
Proof. intros. dependent induction H; eauto. inversion H; subst. eauto.
Qed.

Lemma tm_subpattern_agree_sub_capp : forall a p,
              tm_subpattern_agree (a_CApp a g_Triv) p ->
              tm_subpattern_agree a p.
Proof. intros. dependent induction H; eauto. inversion H; subst. eauto.
Qed.

Lemma tm_subpattern_agree_rel_contr : forall a b p, tm_subpattern_agree
      (a_App a (Rho Rel) b) p -> False.
Proof. intros. dependent induction H; eauto. inversion H.
Qed.

Lemma tm_subpattern_agree_irrel_bullet : forall a b p, tm_subpattern_agree
      (a_App a (Rho Irrel) b) p -> b = a_Bullet.
Proof. intros. dependent induction H; eauto. inversion H. auto.
Qed.

Ltac pattern_head := match goal with
      | [ P1 : binds ?F (Ax ?p _ _ _ _) toplevel,
          P2 : Rename ?p _ ?p' _ _,
          P3 : MatchSubst ?a ?p' _ _ |- _ ] =>
            pose (Q := tm_pattern_agree_rename_inv_2 (MatchSubst_match P3) P2);
            pose (Q1 := tm_pattern_agree_const_same Q);
            pose (Q2 := axiom_pattern_head P1);
            assert (U : head_const a = a_Fam F);
           [ rewrite Q1; rewrite Q2; auto |
             simpl in U; clear Q2; clear Q1; clear Q ]
       end.

Ltac pattern_head_tm_agree := match goal with
      | [ P1 : binds ?F (Ax ?p _ _ _ _) toplevel,
          P2 : tm_pattern_agree ?a ?p |- _ ] =>
          pose (Q := axiom_pattern_head P1);
          pose (Q1 := tm_pattern_agree_const_same P2);
          assert (U1 : head_const a = a_Fam F);
          [ rewrite Q1; auto | clear Q1; clear Q ]
      | [ P1 : binds ?F (Ax ?p _ _ _ _) toplevel,
          P2 : tm_subpattern_agree ?a ?p |- _ ] =>
          pose (Q := axiom_pattern_head P1);
          pose (Q1 := tm_subpattern_agree_const_same P2);
          assert (U1 : head_const a = a_Fam F);
          [ rewrite Q1; auto | clear Q1; clear Q ]
      end.

Ltac axioms_head_same := match goal with
     | [ P11 : binds ?F (Ax ?p1 ?b1 ?A1 ?R1 ?Rs1) toplevel,
         P12 : binds ?F (Ax ?p2 ?b2 ?A2 ?R2 ?Rs2) toplevel |- _ ] =>
         assert (P13 : Ax p1 b1 A1 R1 Rs1 = Ax p2 b2 A2 R2 Rs2);
         [ eapply binds_unique; eauto using uniq_toplevel |
                            inversion P13; subst; clear P13]
     | [ P11 : binds ?F (Ax ?p1 ?b1 ?A1 ?R1 ?Rs1) toplevel,
         P12 : binds ?F (Cs ?A2 ?Rs2) toplevel |- _ ] =>
         assert (P13 : Ax p1 b1 A1 R1 Rs1 = Cs A2 Rs2);
         [ eapply binds_unique; eauto using uniq_toplevel | inversion P13]
     end.

Lemma pattern_like_tm_par_abs_cabs_contr : forall a a1 W R,
      Par W a a1 R -> Abs_CAbs_head_form a1 ->
     (exists F p b A R1 Rs, binds F (Ax p b A R1 Rs) toplevel /\
      tm_subpattern_agree a p /\ ~(tm_pattern_agree a p)) -> False.
Proof. intros. dependent induction H; eauto.
         - inversion H1 as [F [p [b [A [R1 [Rs [H2 [H3 H4]]]]]]]].
           eapply tm_subpattern_agree_abs_cabs_contr; eauto.
         - eapply IHPar1; eauto. inversion H2 as
           [F [p [b1 [A [R1 [Rs [H3 [H4 H5]]]]]]]].
           exists F, p, b1, A, R1, Rs; repeat split; auto.
           eapply tm_subpattern_agree_sub_app; eauto.
           intro. eapply tm_subpattern_agree_app_contr; eauto.
         - inversion H1.
         - eapply IHPar; eauto. inversion H1 as
           [F [p [b1 [A [R1 [Rs [H3 [H4 H5]]]]]]]].
           exists F, p, b1, A, R1, Rs; repeat split; auto.
           eapply tm_subpattern_agree_sub_capp; eauto.
           intro. eapply tm_subpattern_agree_capp_contr; eauto.
         - inversion H0.
         - inversion H2 as [F [p [b1 [A [R1 [Rs [H3 [H4 H5]]]]]]]].
           eapply tm_subpattern_agree_abs_cabs_contr; eauto.
         - inversion H2.
         - inversion H2 as [F [p [b1 [A [R1 [Rs [H3 [H4 H5]]]]]]]].
           eapply tm_subpattern_agree_abs_cabs_contr; eauto.
         - inversion H4.
         - inversion H5 as [F0 [p0 [b1 [A0 [R0 [Rs0 [H6 [H7 H8]]]]]]]].
           pattern_head. pattern_head_tm_agree. rewrite U in U1.
           inversion U1; subst. axioms_head_same.
           assert (tm_pattern_agree a p0).
           eapply tm_pattern_agree_rename_inv_2; eauto.
           eapply MatchSubst_match; eauto. contradiction.
         - inversion H2.
         - inversion H4.
         - inversion H5 as [F0 [p [b [A [R1 [Rs [H6 [H7 H8]]]]]]]].
           eapply tm_subpattern_agree_pattern_contr; eauto.
Qed.


Lemma par_pattern_like_tm : forall a a' W R, Par W a a' R ->
                     (exists F p b A R1 Rs, binds F (Ax p b A R1 Rs) toplevel /\
                      tm_subpattern_agree a p /\ ~(tm_pattern_agree a p)) ->
                      a' = a.
Proof. intros. induction H; eauto.
        - assert False. inversion H0 as [F [p [b1 [A [R1 [Rs [H2 [H3 H4]]]]]]]].
          eapply pattern_like_tm_par_abs_cabs_contr. apply H. eauto.
          exists F, p, b1, A, R1, Rs; split; auto. split.
          eapply tm_subpattern_agree_sub_app; eauto. intro.
          eapply tm_subpattern_agree_app_contr; eauto. contradiction.
        - inversion H0 as [F [p [b1 [A [R1 [Rs [H2 [H3 H4]]]]]]]].
          destruct rho. apply tm_subpattern_agree_rel_contr in H3. contradiction.
          assert (b = a_Bullet). eapply tm_subpattern_agree_irrel_bullet; eauto.
          subst. inversion H1; subst. f_equal. eapply IHPar1; eauto.
          exists F, p, b1, A, R1, Rs; split; auto. split.
          eapply tm_subpattern_agree_sub_app; eauto. intro.
          eapply tm_subpattern_agree_app_contr; eauto. inversion H8.
        - assert False. eapply pattern_like_tm_par_abs_cabs_contr; eauto.
          inversion H0 as [F [p [b1 [A [R1 [Rs [H2 [H3 H4]]]]]]]].
          exists F, p, b1, A, R1, Rs; split; auto. split.
          eapply tm_subpattern_agree_sub_capp; eauto.
          intro. eapply tm_subpattern_agree_capp_contr; eauto. contradiction.
        - inversion H0 as [F [p [b1 [A [R1 [Rs [H2 [H3 H4]]]]]]]].
          f_equal. eapply IHPar. exists F, p, b1, A, R1, Rs; split; auto.
          split. eapply tm_subpattern_agree_sub_capp; eauto.
          intro. eapply tm_subpattern_agree_capp_contr; eauto.
        - inversion H0 as [F [p [b1 [A [R1 [Rs [H2 [H3 H4]]]]]]]].
          assert False. eapply tm_subpattern_agree_abs_cabs_contr; eauto.
          contradiction.
        - inversion H0 as [F [p [b1 [A1 [R1 [Rs [H3 [H4 H5]]]]]]]].
          assert False. eapply tm_subpattern_agree_pi_cpi_contr; eauto.
          contradiction.
        - inversion H0 as [F [p [b1 [A [R1 [Rs [H2 [H3 H4]]]]]]]].
          assert False. eapply tm_subpattern_agree_abs_cabs_contr; eauto.
          contradiction.
        - inversion H0 as [F [p [b1 [A1 [R2 [Rs [H5 [H6 H7]]]]]]]].
          assert False. eapply tm_subpattern_agree_pi_cpi_contr; eauto.
          contradiction.
        - inversion H0 as [F0 [p0 [b1 [A0 [R0 [Rs0 [H6 [H7 H8]]]]]]]].
          pattern_head. pattern_head_tm_agree. rewrite U in U1.
          inversion U1; subst. axioms_head_same.
          assert (tm_pattern_agree a p0).
          eapply tm_pattern_agree_rename_inv_2; eauto.
          eapply MatchSubst_match; eauto. contradiction.
        - inversion H0 as [F0 [p [b [A [R1 [Rs [H6 [H7 H8]]]]]]]]. assert False.
          eapply tm_subpattern_agree_pattern_contr; eauto. contradiction.
        - inversion H0 as [F0 [p [b' [A [R1 [Rs [H6 [H7 H8]]]]]]]]. assert False.
          eapply tm_subpattern_agree_pattern_contr; eauto. contradiction.
        - inversion H0 as [F0 [p [b' [A [R1 [Rs [H6 [H7 H8]]]]]]]]. assert False.
          eapply tm_subpattern_agree_pattern_contr; eauto. contradiction.
Qed.


Fixpoint applyArgs (a : tm) (b : tm) : tm := match a with
   | a_Fam F => b
   | a_App a' nu b' => a_App (applyArgs a' b) nu b'
   | a_CApp a' g_Triv => a_CApp (applyArgs a' b) g_Triv
   | _ => a_Bullet
   end.
(*
Inductive CasePath_like_tm : tm -> Prop :=
  | CasePath_like_fam : forall F, CasePath_like_tm (a_Fam F)
  | CasePath_like_app : forall a nu b, CasePath_like_tm a -> lc_tm b ->
                               CasePath_like_tm (a_App a nu b)
  | CasePath_like_capp : forall a, CasePath_like_tm a ->
                               CasePath_like_tm (a_CApp a g_Triv).
Hint Constructors CasePath_like_tm.*)

Lemma ApplyArgs_applyArgs : forall a b b', ApplyArgs a b b' ->
                             applyArgs a b = b'.
Proof. intros. induction H; simpl; subst; eauto.
Qed.

Lemma applyArgs_ApplyArgs : forall R a F b b', CasePath R a F -> lc_tm b ->
                          applyArgs a b = b' -> ApplyArgs a b b'.
Proof. intros. generalize dependent b'. apply CasePath_ValuePath in H.
       induction H; intros; simpl in *; subst; eauto.
Qed.


(* Properties of CasePath and Value *)

Lemma ValuePath_head : forall a F, ValuePath a F -> head_const a = a_Fam F.
Proof. intros. induction H; eauto.
Qed.

Lemma CasePath_head : forall F a R, CasePath R a F -> head_const a = a_Fam F.
Proof. intros. apply CasePath_ValuePath in H. apply ValuePath_head; auto.
Qed.

Ltac pattern_head_same := match goal with
      | [ P1 : binds ?F (Ax ?p _ _ _ _) toplevel,
          P2 : Rename ?p _ ?p' _ _,
          P3 : MatchSubst ?a ?p' _ _,
          P4 : binds ?F' (Ax _ _ _ _ _) toplevel,
          P5 : CasePath _ ?a' ?F' |- _ ] => pattern_head;
            pose (Q := CasePath_head P5); simpl in Q;
            assert (U1 : a_Fam F = a_Fam F');
            [ eapply transitivity; symmetry; eauto |
                 inversion U1; subst; clear U1; clear Q; axioms_head_same ]
      | [ P1 : binds ?F (Ax ?p _ _ _ _) toplevel,
          P2 : Rename ?p _ ?p' _ _,
          P3 : MatchSubst ?a ?p' _ _,
          P4 : binds ?F' (Ax _ _ _ _ _) toplevel,
          P5 : ValuePath ?a' ?F' |- _ ] => pattern_head;
            pose (Q := ValuePath_head P5); simpl in Q;
            assert (U1 : a_Fam F = a_Fam F');
            [ eapply transitivity; symmetry; eauto |
                 inversion U1; subst; clear U1; clear Q; axioms_head_same ]
       | [ P1 : binds ?F (Ax ?p _ _ _ _) toplevel,
          P2 : Rename ?p _ ?p' _ _,
          P3 : MatchSubst ?a ?p' _ _,
          P4 : binds ?F' (Cs _ _) toplevel,
          P5 : ValuePath ?a' ?F' |- _ ] => pattern_head;
            pose (Q := ValuePath_head P5); simpl in Q;
            assert (U1 : a_Fam F = a_Fam F');
            [ eapply transitivity; symmetry; eauto |
                 inversion U1; subst; clear U1; clear Q; axioms_head_same ]
       end.

Lemma uniq_CasePath : forall F1 F2 a R, CasePath R a F1 -> CasePath R a F2 ->
                       F1 = F2.
Proof. intros. apply CasePath_head in H. apply CasePath_head in H0.
       rewrite H0 in H. inversion H. auto.
Qed.

Lemma ValuePath_cs_par_ValuePath : forall a F A Rs W a' R, ValuePath a F ->
                 binds F (Cs A Rs) toplevel -> Par W a a' R -> ValuePath a' F.
Proof. intros. generalize dependent a'. induction H; intros; eauto.
        - inversion H1; subst; eauto. pattern_head. inversion U; subst.
          axioms_head_same.
        - axioms_head_same.
        - inversion H2; subst. auto. assert (ValuePath (a_UAbs rho a'0) F).
          apply IHValuePath; auto. subst. inversion H3.
          econstructor. eapply Par_lc2; eauto. eauto. pattern_head_same.
        - inversion H1; subst; auto. assert (ValuePath (a_UCAbs a'0) F).
          eauto. inversion H2. pattern_head_same.
Qed.

Lemma ValuePath_ax_par_ValuePath_1 : forall a F p b A R1 Rs W a' R,
      ValuePath a F -> binds F (Ax p b A R1 Rs) toplevel ->
      ~(SubRole R1 R) -> Par W a a' R -> ValuePath a' F /\  ~(SubRole R1 R).
Proof. intros. generalize dependent a'. generalize dependent p.
       induction H; intros; eauto.
         - axioms_head_same.
         - axioms_head_same. inversion H2; subst.
           split; eauto. pattern_head. inversion U; subst. axioms_head_same.
           contradiction.
         - inversion H3; subst. 
           + split; eauto.
           + assert (ValuePath (a_UAbs rho a'0) F).
             eapply IHValuePath; eauto. inversion H4.
           + pose (P := IHValuePath p H2 a'0 H10). inversion P.
             split; eauto. econstructor. eapply Par_lc2; eauto. auto.
           + pattern_head_same. contradiction.
          - inversion H2; subst.
           + split; eauto.
           + assert (ValuePath (a_UCAbs a'0) F).
             eapply IHValuePath; eauto. inversion H3.
           + pose (P := IHValuePath p H0 a'0 H5).
             inversion P. split; auto.
           + pattern_head_same. contradiction.
Qed.


Lemma tm_subpattern_agree_base : forall F p, Pattern p ->
      head_const p = a_Fam F -> tm_subpattern_agree (a_Fam F) p.
Proof. intros. induction H; eauto. simpl in H0. inversion H0; eauto.
Qed.


Inductive tm_tm_agree : tm -> tm -> Prop :=
  | tm_tm_agree_const : forall F, tm_tm_agree (a_Fam F) (a_Fam F)
  | tm_tm_agree_app_relR : forall a1 a2 R b1 b2, tm_tm_agree a1 a2 -> lc_tm b1 ->
       lc_tm b2 -> tm_tm_agree (a_App a1 (Role R) b1) (a_App a2 (Role R) b2)
  | tm_tm_agree_app_rel : forall a1 a2 b1 b2, tm_tm_agree a1 a2 -> lc_tm b1 ->
       lc_tm b2 -> tm_tm_agree (a_App a1 (Rho Rel) b1) (a_App a2 (Rho Rel) b2)
  | tm_tm_agree_app_irrel : forall a1 a2, tm_tm_agree a1 a2 ->
     tm_tm_agree (a_App a1 (Rho Irrel) a_Bullet) (a_App a2 (Rho Irrel) a_Bullet)
  | tm_tm_agree_capp : forall a1 a2, tm_tm_agree a1 a2 ->
                      tm_tm_agree (a_CApp a1 g_Triv) (a_CApp a2 g_Triv).
Hint Constructors tm_tm_agree.

Lemma tm_tm_agree_sym : forall a1 a2, tm_tm_agree a1 a2 -> tm_tm_agree a2 a1.
Proof. intros. induction H; eauto.
Qed.

Lemma tm_pattern_agree_cong : forall a1 a2 p, tm_pattern_agree a1 p ->
              tm_tm_agree a1 a2 -> tm_pattern_agree a2 p.
Proof. intros. generalize dependent p. induction H0; intros; eauto.
         - inversion H2; subst. eauto.
         - inversion H2.
         - inversion H; subst. eauto.
         - inversion H; subst. eauto.
Qed.

Lemma subtm_pattern_agree_cong : forall a1 a2 p, subtm_pattern_agree a1 p ->
              tm_tm_agree a1 a2 -> subtm_pattern_agree a2 p.
Proof. intros. generalize dependent a2. induction H; intros; eauto.
        - econstructor. eapply tm_pattern_agree_cong; eauto.
        - destruct nu. inversion H1; subst. eauto.
          destruct rho. inversion H1; subst; eauto.
          inversion H1; subst; eauto.
        - inversion H0; subst. eauto.
Qed.

Lemma tm_tm_agree_refl : forall a F W R, ValuePath a F -> roleing W a R ->
                                tm_tm_agree a a.
Proof. intros. induction H; auto.
       destruct nu. inversion H0; subst. econstructor; eauto.
       destruct rho. inversion H0; eauto. inversion H0; subst. eauto.
       inversion H0; eauto.
Qed.

Lemma ValuePath_ax_par_ValuePath_2 : forall a F p b A R1 Rs W a' R,
      ValuePath a F -> binds F (Ax p b A R1 Rs) toplevel ->
      ~(subtm_pattern_agree a p) -> Par W a a' R -> ValuePath a' F /\
      ~(subtm_pattern_agree a' p) /\ tm_tm_agree a a'.
Proof. intros. generalize dependent a'. generalize dependent p.
       induction H; intros; eauto.
         - axioms_head_same.
         - inversion H2; subst. eauto. pattern_head. inversion U; subst.
           axioms_head_same.
           inversion H6; subst. inversion H5; subst.
           assert False. apply H1. eauto. contradiction.
         - inversion H3; subst.
           + repeat split; simpl in *; eauto. eapply tm_tm_agree_refl; eauto.
           + assert (ValuePath (a_UAbs rho a'0) F).
             eapply IHValuePath; eauto. inversion H4.
           + pose (P := IHValuePath p H1 ltac:(eauto) a'0 H10).
             inversion P as [P1 [P2 P3]].
             split; eauto. econstructor. eapply Par_lc2; eauto. auto.
             assert (Q : tm_tm_agree (a_App a'0 (Rho rho) b'0) (a_App a (Rho rho) b')).
             { apply tm_tm_agree_sym in P3. destruct rho. econstructor. eauto.
             eapply Par_lc2; eauto. auto. pose (H5 := H3). pose (H6 := H3).
             eapply Par_roleing_tm_fst in H5. eapply Par_roleing_tm_snd in H6.
             inversion H5; subst. inversion H6; subst. eauto. } split.
             intro. apply H2. eapply subtm_pattern_agree_cong; eauto.
             apply tm_tm_agree_sym; auto.
           + pattern_head_same.
             pose (Q1 := tm_pattern_agree_rename_inv_2 (MatchSubst_match H7) H6).
             assert False. eapply H2; eauto. contradiction.
          - inversion H2; subst.
           + repeat split; simpl in *; eauto. eapply tm_tm_agree_refl; eauto.
           + assert (ValuePath (a_UCAbs a'0) F).
             eapply IHValuePath; eauto. inversion H3.
           + pose (P := IHValuePath p H0 ltac:(eauto) a'0 H5).
             inversion P as [P1 [P2 P3]].
             repeat split. econstructor. eapply IHValuePath; eauto. intro.
             apply H1. pose (Q := tm_tm_agree_sym P3).
             eapply subtm_pattern_agree_cong; eauto. eauto.
           + pattern_head_same.
             pose (Q1 := tm_pattern_agree_rename_inv_2 (MatchSubst_match H6) H5).
             assert False. eapply H1; eauto. contradiction.
Qed.

Lemma Par_CasePath : forall F a R W a', CasePath R a F -> Par W a a' R ->
                                        CasePath R a' F.
Proof. intros. generalize dependent a'. induction H; intros.
       - pose (P := ValuePath_cs_par_ValuePath H H0 H1). eauto.
       - pose (P := ValuePath_ax_par_ValuePath_1 H H0 H1 H2).
         inversion P. eauto.
       - pose (P := ValuePath_ax_par_ValuePath_2 H H0 H1 H2).
         inversion P as [P1 [P2 P3]]. eauto.
Qed.

Ltac invert_par :=
     try match goal with
      | [ Hx : CasePath _ _ _,
          Hy : Par _ _ _ _ |- _ ] => apply CasePath_ValuePath in Hx;
               inversion Hy; subst;
                    match goal with
                 | [ Hz : MatchSubst _ _ _ _,
                     Hw : Rename _ _ _ _ _ |- _ ] =>
                       pose (Q := tm_pattern_agree_rename_inv_2
                              (MatchSubst_match Hz) Hw); inversion Q
                 | [ Hu : ValuePath _ _ |- _ ] => inversion Hu
                     end; fail
           end.

Lemma CasePath_Par : forall F a R W a', Value R a' -> CasePath R a F -> Par W a' a R -> CasePath R a' F.
Proof. intros. induction H; invert_par.
       pose (P := Par_CasePath H H1). apply CasePath_head in H0.
       apply CasePath_head in P. rewrite P in H0. inversion H0; subst; auto.
Qed.

Lemma Value_par_Value : forall R v W v', Value R v -> Par W v v' R -> Value R v'.
Proof. intros. generalize dependent W. generalize dependent v'.
       induction H; intros.
        - inversion H0; subst. auto. inversion H3.
        - inversion H1; subst. auto.
          apply Par_lc2 in H1. econstructor.
          inversion H1; auto. auto. inversion H5.
        - inversion H1; subst. auto.
          apply Par_lc2 in H1. econstructor.
          inversion H1; auto. auto. inversion H5.
        - inversion H1; subst. auto. inversion H5.
        - inversion H0; subst. auto.
          apply Par_lc2 in H0. econstructor. auto. inversion H4.
        - inversion H1; subst. eauto. eapply Value_UAbsIrrel with (L := L \u L0).
          intros. eapply H0. auto. eapply H7; eauto. inversion H5.
        - inversion H1; subst. auto. inversion H5.
        - inversion H0; subst. auto. econstructor.
          eapply Par_lc2; eauto. inversion H4.
        - pose (P := Par_CasePath H H0). eauto.
Qed.

Lemma multipar_CasePath :  forall F a R W a', CasePath R a F ->
                       multipar W a a' R -> CasePath R a' F.
Proof. intros. induction H0; auto. apply IHmultipar. eapply Par_CasePath; eauto.
Qed.

Lemma multipar_CasePath_join_head : forall F1 F2 W a1 a2 c R,
      multipar W a1 c R -> multipar W a2 c R ->
      CasePath R a1 F1 -> CasePath R a2 F2 -> F1 = F2.
Proof. intros. eapply multipar_CasePath in H; eauto.
       eapply multipar_CasePath in H0; eauto. eapply uniq_CasePath; eauto.
Qed.

Lemma app_roleing_nom : forall W a rho b R, roleing W (a_App a (Rho rho) b) R ->
                               roleing W b Nom.
Proof. intros. dependent induction H; eauto. eapply role_a_Bullet.
       eapply rctx_uniq; eauto.
Qed.

Lemma CasePath_ax_par_contr : forall R a F F' p b A R1 Rs p' b' D a',
       CasePath R a F -> binds F' (Ax p b A R1 Rs) toplevel ->
       Rename p b p' b' D -> MatchSubst a p' b' a' -> SubRole R1 R -> False.
Proof. intros. pattern_head.
       pose (Q := CasePath_head H).
       assert (a_Fam F = a_Fam F'). eapply transitivity. symmetry. eauto. auto.
       inversion H4; subst.
       inversion H; subst.
         + axioms_head_same.
         + axioms_head_same. contradiction.
         + axioms_head_same.
           pose (Q1 := tm_pattern_agree_rename_inv_2 (MatchSubst_match H2) H1).
           apply H7; eauto.
Qed.

Lemma apply_args_par : forall a b c a' b' c' W R1 R2 F, ApplyArgs a b c ->
                       CasePath R1 a F -> Par W a a' R1 -> Par W b b' R2 ->
                       ApplyArgs a' b' c' -> Par W c c' R2.
Proof. intros. generalize dependent a'. generalize dependent b'.
       generalize dependent c'. induction H; intros.
         - inversion H1; subst. inversion H3; subst. auto.
           pattern_head. inversion U; subst. pose (P2 := CasePath_head H0).
           simpl in P2; inversion P2; subst. assert False.
           eapply CasePath_ax_par_contr; eauto. contradiction.
         - inversion H3; subst.
             + inversion H4; subst. admit.
               (* eapply IHApplyArgs; eauto. eapply CasePath_app; eauto.
               inversion H5; eauto. econstructor. eapply app_roleing_nom; eauto.*)
             + eapply CasePath_app in H0. pose (P := Par_CasePath H0 H11).
               apply CasePath_ValuePath in P. inversion P.
             + inversion H4; subst. econstructor. eapply IHApplyArgs; eauto.
               eapply CasePath_app; eauto. auto.
             + assert False. eapply CasePath_ax_par_contr; eauto. contradiction.
         - inversion H1; subst.
             + inversion H3; subst. admit. (* econstructor.
               eapply IHApplyArgs; eauto. eapply CasePath_capp; eauto.
               inversion H4; eauto. *)
             + eapply CasePath_capp in H0. pose (P := Par_CasePath H0 H6).
               apply CasePath_ValuePath in P. inversion P.
             + inversion H3; subst. econstructor. eapply IHApplyArgs; eauto.
               eapply CasePath_capp; eauto.
             + assert False. eapply CasePath_ax_par_contr; eauto. contradiction.
Admitted.