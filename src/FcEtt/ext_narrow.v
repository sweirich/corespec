
Require Export FcEtt.ett_ott.
Require Export FcEtt.ett_ind.

Lemma narrow_mutual :
   (forall G0 b B R (H : Typing G0 b B R),
      forall G a A R', Typing G a A R' ->
         forall F x R'', G0 = (F ++ (x ~ (Tm A R')) ++ G) -> SubRole R'' R' ->
                      Typing (F ++ (x ~ (Tm A R'')) ++ G) b B R) /\
    (forall G0 phi (H : PropWff G0 phi),
        forall G a A R', Typing G a A R' ->
         forall F x R'', G0 = (F ++ (x ~ (Tm A R')) ++ G) -> SubRole R'' R' ->
                        PropWff (F ++ (x ~ (Tm A R'')) ++ G) phi) /\
    (forall G0 D p1 p2 (H : Iso G0 D p1 p2),
        forall G a A R', Typing G a A R' ->
         forall F x R'', G0 = (F ++ (x ~ (Tm A R')) ++ G) -> SubRole R'' R' ->
                Iso (F ++ (x ~ (Tm A R'')) ++ G) D p1 p2) /\
    (forall G0 D A B T R'' (H : DefEq G0 D A B T R''),
       forall G a A0 R', Typing G a A0 R' ->
         forall F x R0, G0 = (F ++ (x ~ (Tm A0 R')) ++ G) -> SubRole R0 R' ->
                 DefEq (F ++ (x ~ (Tm A0 R0)) ++ G) D A B T R'') /\
    (forall G0 (H : Ctx G0),
        forall G a A R', Typing G a A R' ->
         forall F x R'', G0 = (F ++ (x ~ (Tm A R')) ++ G) -> SubRole R'' R' ->
                        Ctx (F ++ (x ~ (Tm A R'')) ++ G)).
Proof. eapply typing_wff_iso_defeq_mutual;
    intros; subst; simpl.
     - eapply E_SubRole with (R1 := R1). auto. eapply H; eauto.
     - eapply E_Star. eapply H; eauto.
     - apply binds_app_1 in b. destruct b. eapply E_Var. eapply H; eauto.
       apply binds_app_2. auto. apply binds_app_1 in H1. destruct H1.
       apply binds_one_iff in H1. destruct H1. inversion H3. subst.
       econstructor. eauto. eapply E_Var. eapply H; eauto. apply binds_app_3.
       apply binds_cons_2; auto. eapply E_Var. eapply H; eauto.
       apply binds_app_3. apply binds_cons_3. auto.
     - eapply E_Pi with (L := L). intros. rewrite <- app_assoc. eapply H; eauto.
       eapply H0; eauto.
     - eapply E_Abs with (L := L). intros. rewrite <- app_assoc. eapply H; eauto.
       eapply H0; eauto. intros; auto.
     - eapply E_App. eapply H; eauto. eapply H0; eauto.
     - eapply E_IApp. eapply H; eauto. eapply H0; eauto.
     - eapply E_Conv. eapply H; eauto.
       assert (dom (F ++ (x, Tm A0 R'') :: G0) [=] dom (F ++ (x, Tm A0 R') :: G0)).
       admit. rewrite H3. eapply H0; eauto. eapply H1; eauto.
     - eapply E_CPi with (L := L). intros. rewrite <- app_assoc. eapply H; eauto.
       eapply H0; eauto.
     - eapply E_CAbs with (L := L). intros. rewrite <- app_assoc. eapply H; eauto.
       eapply H0; eauto.
     - eapply E_CApp. eapply H; eauto.
       assert (P : dom (F ++ (x, Tm A0 R'') :: G0) = dom (F ++ (x, Tm A0 R'0) :: G0)).
       admit. rewrite P. eapply H0; eauto.
     - eapply E_Fam. eapply H; eauto. eauto. eauto.
     - eapply E_Pat. eapply H; eauto.
       assert (P : dom (F ++ (x, Tm A R'') :: G0) = dom (F ++ (x, Tm A R') :: G0)).
       admit. rewrite P. eapply H0; eauto. eapply H1; eauto.
     - eapply E_Bullet. eapply H; eauto.
     - econstructor. eapply H; eauto. eapply H0; eauto. eapply H1; eauto.
     - econstructor. eapply H; eauto. eapply H0; eauto.
     - econstructor. eapply H; eauto. eapply H0; eauto. eapply H1; eauto.
     - econstructor. eapply H; eauto.
     - apply binds_app_1 in b0. destruct b0. eapply E_Assn. eapply H; eauto.
       apply binds_app_2. eauto. auto. apply binds_app_1 in H1. destruct H1.
       apply binds_one_iff in H1. destruct H1. inversion H3.
       eapply E_Assn. eapply H; eauto. apply binds_app_3. apply binds_cons_3.
       eauto. auto.
     - eapply E_Refl. eapply H; eauto.
     - eapply E_Sym. eapply H; eauto.
     - eapply E_Trans. eapply H; eauto. eapply H0; eauto.
     - eapply E_Sub. eapply H; eauto. auto.
     - eapply E_Beta. eapply H; eauto. eapply H0; eauto. auto.
     - eapply E_PiCong with (L := L). eapply H; eauto. intros.
       rewrite <- app_assoc. eapply H0; eauto. eapply H1; eauto.
       eapply H2; eauto. eapply H3; eauto.
     - eapply E_AbsCong with (L := L). intros. rewrite <- app_assoc.
       eapply H; eauto. eapply H0; eauto. intros; auto. intros; auto.
     - eapply E_AppCong. eapply H; eauto. eapply H0; eauto.
     - eapply E_IAppCong. eapply H; eauto. eapply H0; eauto.
     - eapply E_PiFst. eapply H; eauto.
     - eapply E_PiSnd. eapply H; eauto. eapply H0; eauto.
     - eapply E_CPiCong with (L := L). eapply H; eauto.
       intros. rewrite <- app_assoc. eapply H0; eauto.
       eapply H1; eauto. eapply H2; eauto. eapply H3; eauto.
     - eapply E_CAbsCong with (L := L). intros. rewrite <- app_assoc.
       eapply H; eauto. eapply H0; eauto.
     - eapply E_CAppCong. eapply H; eauto.
       assert (P : dom (F ++ (x, Tm A0 R0) :: G0) = dom (F ++ (x, Tm A0 R'0) :: G0)).
       admit. rewrite P. eapply H0; eauto.
     - eapply E_CPiSnd. eapply H; eauto.
       assert (P : dom (F ++ (x, Tm A0 R1) :: G0) = dom (F ++ (x, Tm A0 R'0) :: G0)).
       admit. rewrite P. eapply H0; eauto.
       assert (P : dom (F ++ (x, Tm A0 R1) :: G0) = dom (F ++ (x, Tm A0 R'0) :: G0)).
       admit. rewrite P. eapply H1; eauto.
     - eapply E_Cast. eapply H; eauto. eapply H0; eauto.
     - eapply E_EqConv. eapply H; eauto.
       assert (P : dom (F ++ (x, Tm A0 R0) :: G0) = dom (F ++ (x, Tm A0 R') :: G0)).
       admit. rewrite P. eapply H0; eauto. auto.
     - eapply E_IsoSnd. eapply H; eauto.
     - eapply E_CastCong. eapply H; eauto.
       assert (P : dom (F ++ (x, Tm A0 R0) :: G0) = dom (F ++ (x, Tm A0 R') :: G0)).
       admit. rewrite P. eapply H0; eauto. eapply H1; eauto.
     - destruct F. inversion H0. inversion H0.
     - admit.
     - admit.
Admitted.