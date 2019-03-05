Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

Require Export FcEtt.tactics.
Require Export FcEtt.imports.
Require Export FcEtt.ett_inf.
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.
Require Import FcEtt.toplevel.
Require Import FcEtt.ett_roleing.
Require Import FcEtt.ext_wf.

(* Lemmas about the various Path judgements and MatchSubst. 

TODO: it's not clear to me what belongs here and what belongs in ett_match 

 *)


(* ------ substitution lemmas ------- *)

Lemma ValuePath_subst : forall F a b x, ValuePath a F -> lc_tm b ->
                   ValuePath (tm_subst_tm_tm b x a) F.
Proof. intros. induction H; simpl; eauto. econstructor; eauto with lngen lc.
Qed.

Lemma ValuePath_subst_co : forall F a b c, ValuePath a F -> lc_co b ->
                   ValuePath (co_subst_co_tm b c a) F.
Proof. intros. induction H; simpl; eauto.
       econstructor; eauto with lngen lc.
Qed.

Lemma tm_pattern_agree_subst_tm : forall a p b x, lc_tm b -> tm_pattern_agree a p ->
                         tm_pattern_agree (tm_subst_tm_tm b x a) p.
Proof. intros.
       induction H0; simpl; eauto. econstructor.
       eapply tm_subst_tm_tm_lc_tm; eauto. auto. econstructor.
       eapply tm_subst_tm_tm_lc_tm; eauto. auto.
Qed.

Lemma tm_pattern_agree_subst_co : forall a p g c, lc_co g -> tm_pattern_agree a p ->
                         tm_pattern_agree (co_subst_co_tm g c a) p.
Proof. intros.
       induction H0; simpl; eauto. econstructor.
       eapply co_subst_co_tm_lc_tm; eauto. auto. econstructor.
       eapply co_subst_co_tm_lc_tm; eauto. auto.
Qed.

Lemma tm_subpattern_agree_subst_tm : forall a p b x, lc_tm b ->
      tm_subpattern_agree a p -> tm_subpattern_agree (tm_subst_tm_tm b x a) p.
Proof. intros. induction H0; eauto. econstructor.
       eapply tm_pattern_agree_subst_tm; eauto.
Qed.

Lemma tm_subpattern_agree_subst_co : forall a p g c, lc_co g ->
      tm_subpattern_agree a p -> tm_subpattern_agree (co_subst_co_tm g c a) p.
Proof. intros. induction H0; eauto. econstructor.
       eapply tm_pattern_agree_subst_co; eauto.
Qed.

Lemma subtm_pattern_agree_subst_tm : forall a p b x, lc_tm b ->
      subtm_pattern_agree a p -> subtm_pattern_agree (tm_subst_tm_tm b x a) p.
Proof. intros. induction H0; simpl. econstructor.
       eapply tm_pattern_agree_subst_tm; eauto.
       eauto with lngen lc. eauto with lngen lc.
Qed.

Lemma subtm_pattern_agree_subst_co : forall a p g c, lc_co g ->
      subtm_pattern_agree a p -> subtm_pattern_agree (co_subst_co_tm g c a) p.
Proof. intros. induction H0; simpl. econstructor.
       eapply tm_pattern_agree_subst_co; eauto.
       eauto with lngen lc. eauto with lngen lc.
Qed.




Lemma RolePath_ValuePath : forall a Rs, RolePath a Rs -> exists F, ValuePath a F.
Proof. intros. induction H; try destruct IHRolePath; eauto.
Qed.

Lemma CasePath_ValuePath : forall R a F, CasePath R a F -> ValuePath a F.
Proof. intros. induction H; eauto.
Qed.

Lemma CasePath_app : forall R a nu a' F, CasePath R (a_App a nu a') F ->
                            CasePath R a F.
Proof. intros. dependent induction H; inversion H; subst; eauto.
Qed.

Lemma CasePath_capp : forall R a F, CasePath R (a_CApp a g_Triv) F ->
                            CasePath R a F.
Proof. intros. dependent induction H; inversion H; subst; eauto.
Qed.


Lemma role_dec : forall (R1 : role) R2, R1 = R2 \/ ~(R1 = R2).
Proof. intros. destruct R1, R2; auto. right. intro. inversion H.
       right. intro. inversion H.
Qed.

Lemma match_bullet : forall a p b, MatchSubst a p a_Bullet b -> b = a_Bullet.
Proof. intros. dependent induction H; auto.
       pose (P := IHMatchSubst ltac:(auto)). rewrite P. auto.
Qed.

Instance eqdec_eq_F : EqDec_eq F. move=>//; by decide equality. Qed.

Lemma match_dec : forall a p, lc_tm a -> MatchSubst a p a_Bullet a_Bullet \/ ~(MatchSubst a p a_Bullet a_Bullet).
Proof. intros. generalize dependent a.
       induction p; intros; try (right; intro P; inversion P; fail).
        - destruct nu. destruct a; try (right; intro P; inversion P; fail).
           + destruct nu; try (right; intro P; inversion P; fail).
             destruct p2; try (right; intro P; inversion P; fail).
             pose (P := role_dec R0 R). inversion P; subst.
              * inversion H; subst. pose (Q := IHp1 a1 H2). inversion Q.
                  ** assert (Q' : a_Bullet = (tm_subst_tm_tm a2 x a_Bullet)).
                    {auto. }
                    left. apply MatchSubst_AppRelR with
                    (R := R)(a := a2)(x := x) in H0. rewrite <- Q' in H0. auto.
                    auto.
                  ** right. intro Q1. inversion Q1; subst. rewrite H10 in H11.
                     pose (Q2 := H11). apply match_bullet in Q2. subst.
                     contradiction.
              * right; intro P1; inversion P1; contradiction.
           + destruct rho. right; intro P1; inversion P1.
             destruct p2; try (right; intro P; inversion P; fail).
             destruct a; try (right; intro P; inversion P; fail).
             destruct nu; try (right; intro P; inversion P; fail).
             destruct rho; try (right; intro P1; inversion P1; fail).
             inversion H; subst. pose (Q := IHp1 a1 H2). inversion Q.
             left; eauto. right. intro P. inversion P. contradiction.
        - destruct g; try (right; intro P; inversion P; fail).
          destruct a; try (right; intro P; inversion P; fail).
          destruct g; try (right; intro P; inversion P; fail).
          inversion H; subst. pose (Q := IHp a H2). inversion Q.
          left; eauto. right. intro P. inversion P. contradiction.
        - destruct a; try (right; intro P; inversion P; fail).
          get F as f1.
          get F excl ![f1]! as f2.
          case eq1: f1 => [|t1]; try solve [right; inversion 1].
          case eq2: f2 => [|t2]; try solve [right; inversion 1].
          subst.
          destruct (t1 == t2); subst.
          by left; eauto.
          by right; inversion 1; contradiction.
Qed.


Fixpoint var_patt (p : tm) : atoms := 
   match p with
      a_App p (Role R) (a_Var_f x) => (singleton x) \u (var_patt p)
    | a_App p (Rho Irrel) Bullet => var_patt p
    | a_CApp p g_Triv => var_patt p
    | _  => {}
   end.


Lemma AppsPath_subst_tm : forall R Apps F a b x, AppsPath R a F Apps -> lc_tm b ->
                   AppsPath R (tm_subst_tm_tm b x a) F Apps.
Proof. intros. induction H; simpl; eauto.
       econstructor; eauto with lngen lc.
       econstructor; eauto with lngen lc.
Qed.

Lemma AppsPath_subst_co : forall R Apps F a b c, AppsPath R a F Apps -> lc_co b ->
                   AppsPath R (co_subst_co_tm b c a) F Apps.
Proof. intros. induction H; simpl; eauto.
       econstructor; eauto with lngen lc.
       econstructor; eauto with lngen lc.
Qed.

Lemma AppsPath_ValuePath_const : forall a F n R,
  AppsPath R a F n -> ValuePath a F /\ 
                     ((exists A Rs T,  binds T (Cs A Rs) toplevel /\ F = T) \/
                      (exists p a A R1 Rs T, binds T (Ax p a A R1 Rs) toplevel /\ F = T  /\
                                       ¬ SubRole R1 R) \/
                      (F = f_Star)).
Proof.
  intros.
  dependent induction H.
  - split; eauto 8.
  - split; eauto 11.
  - split; eauto.
  - destruct IHAppsPath. auto.
  - destruct IHAppsPath. auto.
  - destruct IHAppsPath. auto.
Qed.


Lemma AppsPath_CasePath : forall a F n R,
  AppsPath R a F n -> CasePath R a F.
Proof.
  intros.
  edestruct AppsPath_ValuePath_const; eauto 1.
  destruct H1; [|destruct H1];
  autofwd; subst;
  try with eq do invs end;
  eauto.
Qed.
