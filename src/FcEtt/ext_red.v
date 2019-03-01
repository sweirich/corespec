Require Import FcEtt.imports.
Require Import FcEtt.tactics.
Require Import FcEtt.notations.
Require Import FcEtt.utils.

Require Import FcEtt.ett_ott.

Require Import FcEtt.ett_inf.
Require Import FcEtt.ett_ind.
Require Import FcEtt.ext_wf.
Require Export FcEtt.ext_invert.
Require Export FcEtt.ext_weak.
Require Export FcEtt.ext_subst.
Require Import FcEtt.ett_roleing.

Require Import FcEtt.param.
Require Import FcEtt.ett_path.
Require Import FcEtt.ett_match.
(* Require Import FcEtt.pattern. *)
Require Import FcEtt.ett_rename.

Require Export FcEtt.ext_red_one.

Require Import FcEtt.chain_subst.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.

(* FIXME: temporary *)
Generalizable All Variables.

Definition degrade : pattern_arg -> pattern_arg :=
  fun p => match p with 
  | p_Tm (Role R) a => p_Tm (Rho Rel) a
  | _ => p
  end.


(* --------------------------------------------------------- *)


(* --------------------------------------------------------- *)

Lemma apply_pattern_args_tail_Tm : forall rest a b nu,
   apply_pattern_args a (rest ++ [p_Tm nu b]) = 
   a_App (apply_pattern_args a rest) nu b.
Proof. 
  induction rest; intros; simpl; auto.
  destruct a; try destruct nu; try destruct rho; simpl;
  rewrite IHrest; auto.
Qed. 

Lemma apply_pattern_args_tail_Co : forall rest a b,
 apply_pattern_args a (rest ++ [p_Co b]) = 
   a_CApp (apply_pattern_args a rest) b.
Proof. 
  induction rest. simpl. auto.
  intros a0 b.
  rewrite <- app_comm_cons.
  destruct a; try destruct nu; try destruct rho; simpl; rewrite IHrest; auto.
Qed.

Fixpoint args_roles ( l : list pattern_arg) : list role :=
   match l with 
        | nil => nil
        | ( (p_Tm (Role R) _) :: xs ) => R :: args_roles xs 
        | ( (p_Tm (Rho Rel) _)  :: xs ) => Nom :: args_roles xs
        | ( (p_Tm (Rho Irrel) _)  :: xs ) => args_roles xs
        | ( (p_Co _         ) :: xs)  => args_roles xs  
        end.

Lemma args_roles_app : forall l1 l2, 
    args_roles (l1 ++ l2) = args_roles l1 ++ args_roles l2.
Proof. 
  induction l1; intros; eauto. 
  destruct a; try destruct nu; try destruct rho; simpl; rewrite IHl1; eauto.
Qed.
  
Lemma ApplyArgs_pattern_args : forall a b1 b1' F,
 ApplyArgs a b1 b1' 
 -> ValuePath a F
 -> exists args, a = apply_pattern_args (a_Fam F) args 
       /\ b1' = apply_pattern_args b1 (List.map degrade args).
Proof.
  induction 1.
  + move=> VP. exists nil.  
    inversion VP; subst.
    repeat split; eauto.
    repeat split; eauto.
  + move=> VP. inversion VP; subst.
    move: (IHApplyArgs ltac:(auto)) => [rest [h0 h1]].
    rewrite h0. rewrite h1.
    exists (rest ++ [p_Tm (Role R) a']).
    rewrite map_app. simpl.
    rewrite! apply_pattern_args_tail_Tm.
    repeat split; auto.
  + move=> VP. inversion VP; subst.
    move: (IHApplyArgs ltac:(auto)) => [rest [h0 h1]].
    rewrite h0. rewrite h1.
    exists (rest ++ [p_Tm (Rho rho) a']).
    rewrite map_app. simpl.
    rewrite! apply_pattern_args_tail_Tm.
    auto.
  + move=> VP. inversion VP; subst.
    move: (IHApplyArgs ltac:(auto)) => [rest [h0 h1]].
    rewrite h0. rewrite h1.
    exists (rest ++ [p_Co g_Triv]).
    rewrite map_app. simpl.
    rewrite! apply_pattern_args_tail_Co. auto.
Qed.

Lemma MatchSubst_ValuePath : 
  `{ MatchSubst a p1 b1 b' →
     binds F (Ax p b PiB R1 Rs) toplevel →
     Rename p b p1 b1 s D →
     ValuePath a F}.
Proof. intros. eapply tm_pattern_agree_ValuePath.
       eapply tm_pattern_agree_rename_inv_2.
       eapply MatchSubst_match. all:eauto. econstructor.
       eapply tm_pattern_agree_refl. eapply axiom_pattern. eauto.
Qed. (* MatchSubst_ValuePath *)

Lemma RolePath_no_Beta :
 forall  a R1 Rs, RolePath a (R1 :: Rs) -> forall R, not (exists a', Beta a a' R).
Proof. intros. intro. inversion H0 as [a' h1]. eapply no_Value_Beta; try apply h1.
       move: (RolePath_inversion H) => h.
       move: (RolePath_ValuePath H) => [F0 VP]. 
       destruct h as [[F [A [h2 h3]]] | [F [p [b [A [R2 [ h2 h3]]]]]]];
         move: (ValuePath_head VP) => eq.
       + rewrite eq in h3;  inversion h3; subst. 
         eapply Value_Path; eapply CasePath_AbsConst; eauto 2.
       + move: (RolePath_subtm_pattern_agree_contr H h2) => h4.
         rewrite h3 in eq. inversion eq. subst.
         eapply Value_Path.
         eapply CasePath_UnMatch; eauto 3.
Qed.

Definition arg_app (p : pattern_arg) : App := 
    match p with 
      | p_Tm nu _ => A_Tm nu
      | p_Co _    => A_Co
    end.

Fixpoint map_arg_app (p : list pattern_arg) : Apps :=
  match p with 
  | nil => A_nil
  | cons arg args => A_cons (arg_app arg) (map_arg_app args)
  end.


(* 
   open_telescope G n PiB args targs A 

   holds when 
      - the args line up with the applicators n
      - each arg/targ typechecks according to G
      - the targs include the implicit type arguments
      - each targ matches the Pis in B and, after instantiation,
        produces a final type A
 *)

Inductive open_telescope : context -> Apps -> tm -> pattern_args -> pattern_args -> tm -> Prop :=
  | open_base : forall G A,
      Typing G A a_Star ->
      open_telescope G A_nil A nil nil A
  | open_Role : forall G apps a A R B B0 args targs C,
      Typing G a A ->
      open_telescope G apps B0 args targs C ->
      DefEq G (dom G) B0 (open_tm_wrt_tm B a) a_Star Rep ->
      open_telescope G (A_cons (A_Tm (Role R)) apps) (a_Pi Rel A B) (p_Tm (Role R) a :: args) (p_Tm (Role R) a :: targs) C
  | open_Rel : forall G apps a A B B0 args targs C,
      Typing G a A ->
      open_telescope G apps B0 args targs C ->
      DefEq G (dom G) B0 (open_tm_wrt_tm B a) a_Star Rep -> 
      open_telescope G (A_cons (A_Tm (Rho Rel)) apps) (a_Pi Rel A B) (p_Tm (Rho Rel) a :: args) (p_Tm (Rho Rel) a :: args) C
  | open_Irrel : forall G apps a A B B0 args targs C,
      Typing G a A ->
      open_telescope G apps B0 args targs C ->
      DefEq G (dom G) B0 (open_tm_wrt_tm B a) a_Star Rep ->
      open_telescope G (A_cons (A_Tm (Rho Irrel)) apps) (a_Pi Irrel A B) (p_Tm (Rho Irrel) a_Bullet :: args)
                                        (p_Tm (Rho Irrel) a :: targs)  C
  | open_Co : forall G apps a b A R B B0 args targs C,
      DefEq G (dom G)  a b A R ->
      open_telescope G apps B0 args targs C ->
      DefEq G (dom G) B0 (open_tm_wrt_co B g_Triv) a_Star Rep ->
      open_telescope G (A_cons A_Co apps) (a_CPi (Eq a b A R) B) (p_Co g_Triv :: args)  (p_Co g_Triv :: targs) C
.

Hint Constructors open_telescope.

Lemma invert_Typing_pattern_args2 : forall args hd,
  forall G A, Typing G (apply_pattern_args hd args) A -> 
  exists PiB targs, open_telescope G (map_arg_app args) PiB args targs A
   /\ G ⊨ hd : PiB.
Proof.   
  induction args; intros hd G A H.
  + reg H. simpl. eauto. 
  + destruct a. 
    ++ simpl in H.
       destruct (IHargs _ G A H) as [PiB [targs h0]]. split_hyp.
       destruct nu; try destruct rho; autoinv.
       - do 2 eexists; split; last by eauto 1.
         eapply open_Role; eauto 1. 
       - do 2 eexists; split; last by eauto 1.
         eapply open_Rel; eauto 1.
       - do 2 eexists; split; last by eauto 1.
         subst.
         eapply open_Irrel; eauto 1.
    ++ simpl in H.
       destruct (IHargs _ G A H) as [PiB [targs h0]]. split_hyp.
       autoinv. subst. eexists; eexists; split; eauto 1.
       eapply open_Co; eauto 1. 
Qed. 

Lemma Typing_a_Fam_unique : forall F G A B, 
      Typing G (a_Fam F) A -> Typing G (a_Fam F) B -> DefEq G (dom G) A B a_Star Rep.
Proof.
  intros.
  autoinv.
  all: match goal with 
      | [ H : binds _ _ _ , H1 : binds _ _ _ |- _ ] => 
        move: (binds_unique _ _ _ _ _ H3 H1 uniq_toplevel) => e ;
        inversion e                                                               
      end.
  + subst.
    eapply E_Trans; eauto 1.
    eapply E_Sym; eauto 1.
  + subst.
    eapply E_Trans; eauto 1.
    eapply E_Sym; eauto 1.
Qed.


Inductive arg_targ : pattern_arg -> pattern_arg -> Prop :=
  | AT_Role  : forall R a, 
      arg_targ (p_Tm (Role R) a) (p_Tm (Role R) a)
  | AT_Irrel :forall a, 
      arg_targ (p_Tm (Rho Irrel) a_Bullet) (p_Tm (Rho Irrel) a) 
  | AT_Rel   : forall a,
      arg_targ (p_Tm (Rho Rel) a) (p_Tm (Rho Rel) a)
  | AT_Co    : arg_targ (p_Co g_Triv) (p_Co g_Triv) 
.


Lemma ValuePath_apply_pattern_args : forall args hd F,
  ValuePath (apply_pattern_args hd args) F ->
  ValuePath hd F.
Proof.
  induction args; intros; simpl in *.
  auto.
  destruct a.
  specialize (IHargs _ _  H).
  inversion IHargs.
  auto.
  specialize (IHargs _ _  H).
  inversion IHargs.
  auto.
Qed.


Lemma tm_subst_tm_tm_apply_pattern_args : forall args a0 x a,
   tm_subst_tm_tm a0 x (apply_pattern_args a args) = 
   apply_pattern_args (tm_subst_tm_tm a0 x a) 
                      (List.map (tm_subst_tm_pattern_arg a0 x) args).
Proof. 
  induction args; intros; simpl.
  auto.
  destruct a; simpl.
  rewrite IHargs; auto.
  rewrite IHargs; auto.
Qed.

Definition arg_agree : pattern_arg -> pattern_arg -> Prop :=
  fun arg pat => 
    match (arg,pat) with 
    | (p_Tm nu1 a, p_Tm nu2 p) => nu1 = nu2 /\ tm_pattern_agree a p 
    | (p_Co _, p_Co _) => True
    | (_,_) => False
    end.


Lemma fv_tm_tm_tm_apply_pattern_args : forall pargs a, 
        fv_tm_tm_tm (apply_pattern_args a pargs) [=] 
        fv_tm_tm_tm a \u fv_tm_tm_pattern_args pargs.
Proof. 
  induction pargs; intros; simpl in *.
  fsetdec.
  destruct a.
  rewrite IHpargs. simpl. fsetdec.
  rewrite IHpargs. simpl. fsetdec.
Qed.
Lemma fv_co_co_tm_apply_pattern_args : forall pargs a, 
        fv_co_co_tm (apply_pattern_args a pargs) [=] 
        fv_co_co_tm a \u fv_co_co_pattern_args pargs.
Proof. 
  induction pargs; intros; simpl in *.
  fsetdec.
  destruct a.
  rewrite IHpargs. simpl. fsetdec.
  rewrite IHpargs. simpl. fsetdec.
Qed.

Lemma fv_tm_tm_pattern_args_app : forall pargs1 pargs2,
  fv_tm_tm_pattern_args (pargs1 ++ pargs2) [=] 
  fv_tm_tm_pattern_args pargs1 \u fv_tm_tm_pattern_args pargs2.
Proof. induction pargs1; intros; simpl; try rewrite IHpargs1; fsetdec.
Qed.

Instance Proper_domFresh {A} : Proper (Logic.eq ==> AtomSetImpl.Equal ==> iff) (@domFresh A).
Proof. 
  move=> x y Eq1 z w Eq2.
  subst.
  induction y; unfold domFresh. split; eauto.
  split; unfold domFresh in *. 
  intro h; inversion h; destruct a; econstructor; eauto.
  rewrite <- Eq2. auto. rewrite <- IHy. auto.
  intro h; inversion h; destruct a; econstructor; eauto.
  rewrite Eq2. auto. rewrite IHy. auto.
Qed.


Lemma Beta_fv_preservation : forall x a b R, 
    Beta a b R -> 
    x `notin` fv_tm_tm_tm a ->
    x `notin` fv_tm_tm_tm b.
Proof.
  intros.
  induction H.
  + simpl in *.
    move => h. 
    eapply fv_tm_tm_tm_open_tm_wrt_tm_upper in h.
    fsetdec.
  + simpl in *.    
    move => h.
    eapply fv_tm_tm_tm_open_tm_wrt_co_upper in h.
    fsetdec.
  + move: (Rename_MatchSubst_fv H1 H2) => h3.
    move: (axiom_body_fv_in_pattern H) => h.
    intro. move: (AtomSetProperties.in_subset H4 h3) => h1.
    apply union_iff in h1. inversion h1. apply diff_iff in H5.
    inversion H5. apply H7. eapply AtomSetProperties.in_subset; eauto.
    apply H0. auto.
  + simpl in *.
    move: H2 H0.
    generalize a.
    induction 1.
    - intros. fsetdec.
    - simpl in *.
      fsetdec.
    - simpl in *.
      fsetdec.
    - simpl in *.
      fsetdec.
  + simpl in *. fsetdec.
Qed.

(*

This is the main lemma about the preservation of 
pattern matching. 

Invariants about the IH:

 We will call this lemma (in BranchTyping_start) with 
    args1 = nil       targs1 == appropriate for args 
    args2 = args      targs2 == nil
    pargs1 = nil      G1 = nil
    pargs2 = pargs 

In the base case, we will have the opposite
   pargs1 = pargs           pargs2 = nil
   args1  = args            targs2 = nil

   tm_pattern_agree (args1 ++ args2) (pargs1 ++ pargs2)

   arg_agree args1 targs1
   arg_agree args2 targs2

   scrut = hd @ args1  @ args2
   pat   = hd @ pargs1 @ pargs2

     |= pargs1 : G1
  

*)

(* For roles, we need to know that the non-nominal prefix of args 
   matches the Roles for F. 
 *)


Lemma BranchTyping_lemma : forall n G1 G R A scrut hd pargs1 B0 B1 C,
    BranchTyping (G1 ++ G) n R scrut A hd pargs1 B0 B1 C ->
    domFresh G (fv_tm_tm_pattern_args pargs1) ->
    forall args1 args2 , 
    map_arg_app args2 = n ->
    forall Rs, RolePath (apply_pattern_args hd args1) (args_roles args2 ++ Rs) -> 
    scrut = apply_pattern_args (apply_pattern_args hd args1) args2  ->
    forall targs1 sub, 
    sub = zip (List.map fst G1) (rev targs1) ->
    wf_sub G sub ->
    length G1 = length (rev targs1) ->
    (List.map (fun a => cps_pattern_arg a sub) pargs1 = args1) ->
    forall B0' targs2,
    open_telescope G n B0' args2 targs2 A ->
    DefEq G (dom G) B0' (cps_tm B0 sub) a_Star Rep ->
    Typing G (apply_pattern_args hd args1) B0' ->
    forall b1' b1,
    b1' = apply_pattern_args b1 (List.map degrade args2) ->
    Typing G b1 (cps_tm B1 sub) ->
    Typing G C a_Star ->
    Typing G (a_CApp b1' g_Triv) C.
Proof.
  intros n. induction n.
  all: intros.
  all: with BranchTyping do ltac:(fun h => inversion h; subst; clear h). 
  all: destruct args2; with (map_arg_app _ = _) do 
           ltac:(fun h=> simpl in h; inversion h).
  {
    simpl in *.
    with open_telescope do ltac:(fun h => inversion h).
    subst.
    set (s := zip (List.map fst G1) (rev targs1)) in *.
    with (Typing _ _ (cps_tm (a_CPi _ _) _)) 
       do ltac:(fun h => rewrite cps_a_CPi in h; simpl in h).
    with (Typing G (open_tm_wrt_co _ _) a_Star) do ltac:(fun h => 
       move:(Typing_context_fv h)=> ?). split_hyp.
    with (Typing G b1) do ltac:(fun h => 
       replace (cps_tm C1 s) with C1 in h).
        Focus 2.  move: (fv_tm_tm_tm_open_tm_wrt_co_lower C1 g_Triv) => ?. 
             move: (fv_co_co_tm_open_tm_wrt_co_lower C1 g_Triv) => ?. 
             rewrite cps_tm_fresh_eq.
             eapply wf_sub_domFresh with (G:=G); auto.
             eapply wf_sub_domFresh with (G:=G); auto.
             auto.
     eapply E_CApp; eauto 1.
        {
        with (Typing G (apply_pattern_args _ _)) do ltac:(fun h => 
          move:(Typing_context_fv h) => ?; split_hyp). 
        with (fv_tm_tm_tm (apply_pattern_args _ _) [<=] _) do ltac:(fun h =>
          rewrite -> fv_tm_tm_tm_apply_pattern_args in h).
        with (fv_co_co_tm (apply_pattern_args _ _) [<=] _) do ltac:(fun h =>
          rewrite -> fv_co_co_tm_apply_pattern_args in h).
        simpl in *.
          rewrite! cps_tm_apply_pattern_args.
          rewrite (cps_tm_fresh_eq hd).
          eapply wf_sub_domFresh with (G:=G); auto.
          eapply wf_sub_domFresh with (G:=G); auto.
          
          have eq: 
            wf_sub G s ->
            fv_tm_tm_pattern_args (List.map (cps_pattern_arg^~ s) pargs1) [<=] dom G ->
            fv_co_co_pattern_args (List.map (cps_pattern_arg^~ s) pargs1) [<=] dom G ->
            (List.map (cps_pattern_arg^~ s) (List.map (cps_pattern_arg^~ s) pargs1) = 
                      (List.map (cps_pattern_arg^~ s) pargs1)).
          { 
            generalize s. generalize pargs1. 
            induction pargs0; intros; simpl; auto.
            simpl in *.
            rewrite IHpargs0; eauto.
            f_equal.
            destruct a; simpl in *.           
            rewrite (cps_tm_fresh_eq (cps_tm a s0));
            try eapply wf_sub_domFresh with (G:=G); auto.
            rewrite (cps_co_fresh_eq (cps_co g s0));
            try eapply wf_sub_domFresh with (G:=G); auto.
          }
          rewrite eq. eauto 1. fsetdec. fsetdec. 
          eapply E_Refl.
          autoreg. 
          eapply E_Conv; eauto 1.
        } 
  }
 
  all: set (sub := zip (List.map fst G1) (rev targs1)).
  all: set (args1 := List.map (fun a => cps_pattern_arg a sub) pargs1).

  all: destruct p; try destruct nu; simpl in *; try discriminate.
  all: try match goal with [H : A_Tm _ = _ |- _ ] => inversion H; subst end.
  all: try match goal with [H : A_Co _ = _ |- _ ] => inversion H; subst end. 

  all: with (open_telescope) do ltac:(fun h => inversion h; subst).
  all: match goal with 
   [ H : open_telescope ?G ?r _ _ (?p1 :: _) ?A |- _ ] =>
     set (targs1' :=  (targs1 ++ [p1])) in *
  end.

  all: try 
    with (Typing G a) do ltac:(fun h =>  move: (Typing_context_fv h) => ?; split_hyp).
  all: try 
    with (Typing G a0) do ltac:(fun h =>  move: (Typing_context_fv h) => ?; split_hyp).
  all: try
    with (DefEq _ _ a) do ltac:(fun h => move: (DefEq_context_fv h) => ?; split_hyp).
  all: try have ?: lc_tm a by eapply Typing_lc1; eauto.
  all: try have ?: lc_tm a0 by eapply Typing_lc1; eauto.
  (* already have lc_co g *)
  all: try with (Typing _ _ (cps_tm _ _)) do  ltac:(fun h => rewrite cps_a_Pi in h).
  all: try with (DefEq _ _ _ (cps_tm _ _)) do  ltac:(fun h => rewrite cps_a_Pi in h).
  all: autofresh. 
  all: have ?: x `notin` dom sub by (unhide Fr; rewrite dom_zip_map_fst; auto).
  all: have ?: x `notin` dom G   by (unhide Fr; fsetdec_fast).
  all: try match goal with 
      [ targs1' := ?targs1 ++ [?p (Role ?R) ?a] : _ |- _  ]=> 
      set (G1' := (x, Tm A0) :: G1) in *;
      set (sub' := (x, p_Tm (Role R) a) :: (zip (List.map fst G1) (rev targs1)));
      set (args1' := args1 ++ [p_Tm (Role R) a]);
      set (pargs1' := pargs1 ++ [p_Tm (Role R) (a_Var_f x)])
     end. 

  all: try match goal with 
      [ targs1' := ?targs1 ++ [?p (Rho ?rho) ?a] : _ |- _  ]=> 
      set (G1' := (x, Tm A0) :: G1) in *;
      set (sub' := (x, p_Tm (Rho rho) a) :: (zip (List.map fst G1) (rev targs1)));
      match rho with 
         | Rel => 
            set (args1' := args1 ++ [p_Tm (Rho rho) a]);
            set (pargs1' := pargs1 ++ [p_Tm (Rho rho) (a_Var_f x)])
         | Irrel =>
            set (args1' := args1 ++ [p_Tm (Rho rho) a_Bullet]);
            set (pargs1' := pargs1 ++ [p_Tm (Rho rho) a_Bullet])
      end
     end.

  all: try match goal with 
      [ targs1' := ?targs1 ++ [p_Co ?g] : _ |- _  ]=> 
      set (G1' := (x, Co phi) :: G1) in *;
      set (sub' := (x, p_Co g_Triv) :: (zip (List.map fst G1) (rev targs1)));
      set (args1' := args1 ++ [p_Co g]);
      set (pargs1' := pargs1 ++ [p_Co g_Triv])
     end.
  all: have ?: length G1' = length (rev targs1') by
      (unfold G1'; unfold targs1'; rewrite rev_unit; simpl; auto).

   all: try
      have df :  
        domFresh G (fv_tm_tm_pattern_args pargs1') by
          (unfold pargs1';
           rewrite fv_tm_tm_pattern_args_app;
           rewrite domFresh_union;
           split; auto;
           simpl;
           rewrite union_empty_r;
           eauto using domFresh_empty, domFresh_singleton2).  

  all: have es: sub' = zip (List.map fst G1') (rev targs1') by
      (unfold sub'; unfold G1'; unfold targs1';
      rewrite rev_unit; reflexivity). 
  all: have ?: wf_sub G sub' by (unfold sub'; econstructor; eauto 2; fsetdec).


  Opaque cps_tm.
  all : try 
    have SA: cps_tm (a_Var_f x) sub' = a by
    ( unfold sub'; simpl;
      erewrite wf_cps_subst_var; auto;
      econstructor; eauto 1;
      fsetdec ).
  all: try 
    have SA: cps_tm (a_Var_f x) sub' = a0 by
     ( unfold sub'; simpl;
      erewrite wf_cps_subst_var; auto;
      econstructor; eauto 1;
      fsetdec ).

  all: try 
   have SA: cps_co (g_Var_f x) sub' = g_Triv by
    (  unfold sub';
       erewrite wf_cps_co_subst_var; auto;
       econstructor; eauto 1;
       fsetdec ).

  all: with BranchTyping do ltac:(fun h =>
        specialize (IHn G1' G _ _ _ _ _ _ _ _ h); clear h).  

  all: specialize (IHn df args1' args2 eq_refl Rs). 
  all: try rewrite apply_pattern_args_tail_Tm in IHn.
  all: try rewrite apply_pattern_args_tail_Co in IHn.

  all: specialize (IHn ltac:(eauto)).
  all: specialize (IHn eq_refl).
  all: specialize (IHn targs1' sub' es ltac:(auto) ltac:(auto)).

  all: with (Typing G (apply_pattern_args _ _)) do ltac:(fun h => 
         move:(Typing_context_fv h) => ?; split_hyp). 
  all: with (fv_tm_tm_tm (apply_pattern_args _ _) [<=] _) do ltac:(fun h =>
         rewrite -> fv_tm_tm_tm_apply_pattern_args in h).
  all: with (fv_co_co_tm (apply_pattern_args _ _) [<=] _) do ltac:(fun h =>
         rewrite -> fv_co_co_tm_apply_pattern_args in h).

  all: 
   have ?: List.map (cps_pattern_arg^~ sub') pargs1' = args1'
  by (unfold args1'; unfold args1; rewrite map_app;
      f_equal;
      [ unfold sub'; unfold sub;
        erewrite cps_pattern_fresh; eauto 
      | simpl; f_equal; f_equal;
        try eapply (@wf_cps_subst_var _ _ G); 
        try eapply cps_a_Bullet;
        try erewrite cps_g_Triv; eauto]).

  all: specialize (IHn ltac:(auto)).
  all: with (open_telescope) do 
         ltac:(fun h => specialize (IHn _ _ h); clear h).

  Transparent cps_tm. 
  all: try 
     with (DefEq _ _ (a_Pi _ _ _)) do 
       ltac:(fun h => move: (DefEq_context_fv h) => ?) end;  split_hyp.
  all: try
     with (DefEq _ _ (a_CPi _ _)) do 
       ltac:(fun h => move: (DefEq_context_fv h) => ?) end;  split_hyp.

  all: try
    have htmp: 
     DefEq G (dom G) B1 (cps_tm (open_tm_wrt_tm B (a_Var_f x)) sub') a_Star Rep by
    (
      eapply E_Trans with (a1 := open_tm_wrt_tm B0 a); eauto 1;
      unfold sub';
      rewrite cps_open_tm_wrt_tm; first eauto;
      rewrite SA;
      simpl;
      rewrite tm_subst_tm_tm_fresh_eq; 
      [ simpl in *;
        eapply subset_notin with (S2 := dom G); auto
      | eauto
      ]
    ).
    
+ eapply IHn with (b1 := a_App b1 (Rho Rel) a); auto.
    ++ eapply E_Conv with (A := open_tm_wrt_tm B0 a); 
         eauto 1. 2: eapply E_Sym; eauto 1.
      eapply E_TApp; eauto 1.
      { autoreg. auto. }

    ++ rewrite cps_open_tm_wrt_tm.
       eapply wf_sub_lc_sub; eauto.
       rewrite SA.
       unfold sub'. simpl.
       rewrite tm_subst_tm_tm_fresh_eq.
    {  with (Typing _ _ (a_Pi _ _ _)) do 
             ltac:(fun h => move: (Typing_context_fv h) => ?).
        split_hyp.
        simpl in *.
        eapply subset_notin with (S2 := dom G). auto.
        fsetdec.
    }    
    eapply E_App with (A:=  (cps_tm A0 (zip (List.map fst G1) (rev targs1)))).
    eauto 1.
    eapply E_Conv; eauto 1.
    eapply E_PiFst; eauto 1.
    { autoreg. autoinv. auto. }

+ eapply IHn with (b1 := a_App b1 (Rho Rel) a); auto.
  ++ eapply E_Conv with (A := open_tm_wrt_tm B0 a); 
       eauto 1. 2: eapply E_Sym; eauto 1.
      eapply E_App; eauto 1.
      { autoreg. auto. }
  ++ rewrite cps_open_tm_wrt_tm.
       eapply wf_sub_lc_sub; eauto.
       rewrite SA.
       unfold sub'. simpl.
       rewrite tm_subst_tm_tm_fresh_eq.
    {  with (Typing _ _ (a_Pi _ _ _)) do 
             ltac:(fun h => move: (Typing_context_fv h) => ?).
        split_hyp.
        simpl in *.
        eapply subset_notin with (S2 := dom G). auto.
        fsetdec.
    }    
    eapply E_App with (A:=  (cps_tm A0 (zip (List.map fst G1) (rev targs1)))).
    eauto 1.
    eapply E_Conv; eauto 1.
    eapply E_PiFst; eauto 1.
    { autoreg. autoinv. auto. }
+ eapply IHn with (b1 := a_App b1 (Rho Irrel) a_Bullet); auto.
   ++ eapply E_Trans with (a1 := open_tm_wrt_tm B0 a0); eauto 1;
      unfold sub';
      rewrite cps_open_tm_wrt_tm; first eauto;
      rewrite SA;
      simpl;
      rewrite tm_subst_tm_tm_fresh_eq.
      simpl in *;
        eapply subset_notin with (S2 := dom G); auto.
      move: H9 => peq. 
      eapply E_PiSnd; eauto 1.
      eapply E_Refl; eauto 1.
   ++ eapply E_Conv with (A := open_tm_wrt_tm B0 a0); 
        eauto 1. 2: eapply E_Sym; eauto 1.
      eapply E_IApp; eauto 1.
      { autoreg. auto. }
   ++ rewrite cps_open_tm_wrt_tm.
       eapply wf_sub_lc_sub; eauto.
       rewrite SA.
       unfold sub'. simpl.
       rewrite tm_subst_tm_tm_fresh_eq.
    {  with (Typing _ _ (a_Pi _ _ _)) do 
             ltac:(fun h => move: (Typing_context_fv h) => ?).
        split_hyp.
        simpl in *.
        eapply subset_notin with (S2 := dom G). auto.
        fsetdec.
    }    
    eapply E_IApp with (A:=  (cps_tm A0 (zip (List.map fst G1) (rev targs1)))).
    eauto 1.
    eapply E_Conv; eauto 1.
    eapply E_PiFst; eauto 1.
    { autoreg. autoinv. auto. } 

+ eapply IHn with (b1 := a_CApp b1 g_Triv); auto.
  ++  eapply E_Trans with (a1 := open_tm_wrt_co B0 g_Triv); eauto 1;
      unfold sub'.
      rewrite cps_open_tm_wrt_co; first eauto.
      rewrite SA.
      simpl.
      rewrite co_subst_co_tm_fresh_eq.
      { 
        rewrite cps_a_CPi in H24.
        rewrite cps_a_CPi in H25.
        simpl in *.
        eapply subset_notin with (S2 := empty). auto.
        rewrite -> union_subset in H25. split_hyp. auto.
      }
      move: H9 => peq.
      fold sub. fold sub in peq.
      destruct phi as [a' b' A0' R'].
      rewrite cps_a_CPi in peq. simpl in peq.
      have e1: DefEq G (dom G) a b A0 R. auto.
      move: (E_CPiFst _ _ _ _ _ _ _ _ _ _ _ _ _ peq) => iso.
      move: (E_Cast _ _ _ _ _ _ _ _ _ _ e1 iso) => e2.
      eapply E_CPiSnd; eauto 1.
  ++ eapply E_Conv; eauto 1. 2: eapply E_Sym; eauto 1.
     eapply E_CApp; eauto 1.
      { autoreg. auto. }
  ++ rewrite cps_open_tm_wrt_co.
       eapply wf_sub_lc_sub; eauto.
       rewrite SA.
       unfold sub'. simpl.
       rewrite co_subst_co_tm_fresh_eq.
       {  with (Typing _ _ (cps_tm (a_CPi _ _) _)) do 
             ltac:(fun h => move: (Typing_context_fv h) => ?).
          split_hyp.
          rewrite cps_a_CPi in H30.
          rewrite cps_a_CPi in H31.
          eapply subset_notin with (S2 := empty). auto.
          simpl in *.
          rewrite -> union_subset in H31. split_hyp. auto.
       }  
       move: H12 => h.
       move: H9 => h0.
       destruct phi.
       rewrite cps_a_CPi in h.
       rewrite cps_a_CPi in h0.
       simpl in *.
       eapply E_CApp; eauto 1.
       eapply E_Cast with (a:=a)(b:=b).  eauto 1.
       eapply E_CPiFst. eauto 1.
Qed.


(* Specialized version of main lemma that is "easier" to use. *)
Lemma BranchTyping_start : forall  G n R A scrut hd B0 B1 C,
    BranchTyping G n R scrut A hd nil B0 B1 C ->
    forall args, map_arg_app args = n ->
    forall Rs, RolePath hd (args_roles args ++ Rs) ->
    scrut = apply_pattern_args hd args  ->
    forall B0' targs,
    open_telescope G n B0' args targs A ->
    DefEq G (dom G) B0' B0 a_Star Rep ->
    Typing G hd B0' ->
    forall b1' b1,
    b1' = apply_pattern_args b1 (List.map degrade args) ->
    Typing G b1 B1  ->
    Typing G C a_Star ->
    Typing G (a_CApp b1' g_Triv) C.
Proof.
  intros.
  eapply BranchTyping_lemma with (G1 := nil)(args1 := nil)
                                 (pargs1:=nil)(targs1:=nil); eauto 1. 
  simpl. generalize G. induction G0; unfold domFresh; auto.
  econstructor. destruct a. auto. auto.
Qed.

Lemma rev_injective : forall A (xs ys : list A), rev xs = rev ys -> xs = ys.
Proof.
  induction xs. intros. destruct ys; simpl in H; inversion H; auto.
  move: (app_cons_not_nil (rev ys) nil a) => h0. contradiction.
  intros. 
  destruct ys; simpl in H; inversion H; auto.
  move: (app_cons_not_nil (rev xs) nil a) => h0. rewrite H1 in h0. contradiction.
  apply app_inj_tail in H.
  destruct H.
  f_equal; auto.
Qed.


Lemma shuffle : forall A (args : list A) a rargs,
(a :: rargs = rev args) -> args = rev rargs ++ [a].
Proof.
  intros. 
  rewrite <- (rev_involutive rargs) in H.
  rewrite <- rev_unit in H.
  apply rev_injective in H.
  auto.
Qed.

Lemma map_arg_app_snoc : forall args App,
    map_arg_app (args ++ [App]) = A_snoc (map_arg_app args) (arg_app App).
Proof.
  induction args.
  simpl. eauto.
  intros. simpl. rewrite IHargs. eauto.
Qed.
  
Lemma AppsPath_arg_app' : forall rargs args, rargs = rev args -> forall n R F,
  AppsPath R (apply_pattern_args (a_Fam F) args) F n -> 
  map_arg_app args = n.
Proof.
  induction rargs.
  - intros. destruct args; simpl in H; inversion  H. 
    simpl in *. inversion H0; auto.
    apply app_cons_not_nil in H. contradiction.
  - intros args H n R F AP.
    apply shuffle in H.
    rewrite H in AP.
    destruct a; try destruct nu.
    all: try rewrite apply_pattern_args_tail_Tm in AP.    
    all: try rewrite apply_pattern_args_tail_Co in AP.    
    all: inversion AP; subst.
    all: rewrite map_arg_app_snoc; f_equal;
      eapply IHrargs; eauto. 
    all: rewrite rev_involutive; auto.
Qed.

Lemma AppsPath_arg_app : forall args n R F,
  AppsPath R (apply_pattern_args (a_Fam F) args) F n -> 
  map_arg_app args = n.
Proof.
  intros args. intros.
  eapply (@AppsPath_arg_app' (rev args) args eq_refl).
  eauto.
Qed.

Lemma RolePath_args : forall F Rs, 
    RolePath (a_Fam F) Rs ->
    forall args Rs', RolePath (apply_pattern_args (a_Fam F) (rev args)) Rs' ->
    Rs = (args_roles (rev args)) ++ Rs'.
Proof.
  intros F Rs RP.
  induction args; intros Rs' RP'.
  - simpl in *. 
    inversion RP; inversion RP'; subst.
    all: move: (binds_unique _ _ _ _ _ H0 H3 uniq_toplevel) => EQ; inversion EQ.
    all: auto.
  - simpl in *.
    destruct a; try destruct nu; try destruct rho.
    all: try rewrite apply_pattern_args_tail_Tm in RP'.
    all: try rewrite apply_pattern_args_tail_Co in RP'.
    all: inversion RP'; subst; simpl. clear RP'.
    all: with RolePath do ltac:(fun h => move: (IHargs _ h) => eq).
    all: subst; simpl.
    all: rewrite args_roles_app; simpl.
    all: rewrite <- app_assoc; simpl; auto.
Qed.

Lemma RolePath_AppRole : 
    forall args Rs, AppRoles (map_arg_app args) Rs -> 
    forall hd,  RolePath hd Rs ->
    Rs = args_roles args.
Proof.
  intros args Rs H. dependent induction H; eauto.
  + intros. destruct args; inversion x. simpl. auto. 
  + intros. destruct args; inversion x. subst. 
    destruct p; try destruct nu; inversion H2; subst.
    simpl. erewrite IHAppRoles; eauto.
  + intros. destruct args; inversion x. subst. 
    destruct p; try destruct nu; inversion H2; subst.
    simpl. erewrite IHAppRoles; eauto.
  + intros. destruct args; inversion x. subst. 
    destruct p; try destruct nu; inversion H2; subst.
    simpl. erewrite IHAppRoles; eauto.
  + intros. destruct args; inversion x. subst. 
    destruct p; try destruct nu; inversion H2; subst.
    simpl. erewrite IHAppRoles; eauto.
Unshelve. all: eauto.
Qed.

Lemma BranchTyping_preservation : forall G n R a A F B0 B1 C,
    BranchTyping G n R a A (a_Fam F) nil B0 B1 C ->
    CasePath R a F ->
    AppsPath R a F n ->
    SatApp F n ->
    Typing G a A ->
    Typing G (a_Fam F) B0 ->
    forall b1, Typing G b1 B1 ->
    forall b1', ApplyArgs a b1 b1' ->
    Typing G C a_Star ->
    Typing G  (a_CApp b1' g_Triv) C.
Proof.
  intros G n R a A F B0 B1 C BT CP AP SA Ta Tp b1 Tb1 b1' AA TC.
  have VP:  ValuePath a F.   
  eapply ett_path.CasePath_ValuePath; eauto.
  edestruct ApplyArgs_pattern_args as [args [h0 h1]]; eauto 1.
  subst a.
  move: (invert_Typing_pattern_args2 _ _  Ta) => [PiB [targs [h2 h4]]].
  
  have eq: map_arg_app args = n.  eapply AppsPath_arg_app; eauto.
  rewrite eq in h2.

  have RP: RolePath (a_Fam F) (args_roles args).
  { inversion SA. subst.
    ++ replace (args_roles args) with Rs. 
       eauto. eapply RolePath_AppRole; eauto.
    ++ replace (args_roles args) with Rs. 
       eauto. eapply RolePath_AppRole; eauto.
       rewrite eq. auto.
  }     
  eapply BranchTyping_start with (Rs := nil); eauto 1.
  rewrite app_nil_r; eauto.
  eapply Typing_a_Fam_unique; eauto 1.
Qed.

(* --------------------------------------------------------- *)

(*
(* Need to also say that vars P # C *)
Definition patternFresh p s :=
  AtomSetImpl.inter (of_list (vars_Pattern p)) s [<=] empty.
*)

(*
Definition sub := list (atom * tm). *)

(* MatchTyping describes the relationship between the pattern 
   and the scrutinee during type checking

   If we have

     MatchTyping Gp p B G a A sub 

   then 

     Gp |= p : B
     G  |= a : A

   and

     cps_tm (zip (fst Gp) sub) p = a 
     cps_tm (zip (fst Gp) sub) B = A

   and

     wf_sub (zip (fst Gp) sub)
   
*)
Inductive MatchTyping : 
  context -> tm -> tm -> context -> tm -> tm -> list pattern_arg -> list atom -> Prop := 
  | MatchTyping_Const : forall G F PiB B,
    Typing G (a_Fam F) PiB ->
    DefEq G (dom G) PiB B a_Star Rep ->
    MatchTyping nil (a_Fam F) PiB G (a_Fam F) B nil nil
  | MatchTyping_AppRelR : 
    forall G Gp R p x A1 B1 a1 a2 A2 B2 A sub D,
    MatchTyping Gp p (a_Pi Rel A1 B1) G a1 (a_Pi Rel A2 B2) sub D ->
    Typing G a2 A2 ->
    DefEq G (dom G) A (open_tm_wrt_tm B2 a2) a_Star Rep ->
    x `notin` dom Gp ->
    x `notin` dom G  ->
    MatchTyping (x ~ Tm A1 ++ Gp)
                (a_App p  (Role R) (a_Var_f x)) (open_tm_wrt_tm B1 (a_Var_f x))
                G  (a_App a1 (Role R) a2)          A
                ((p_Tm (Role R) a2) :: sub) D 
  | MatchTyping_AppIrrel : 
    forall Gp G p x A1 B1 a1 a2 a2' A2 B2 A sub D,
    MatchTyping Gp p (a_Pi Irrel A1 B1) G a1 (a_Pi Irrel A2 B2) sub D ->
    Typing G a2' A2 ->
    DefEq G (dom G) A (open_tm_wrt_tm B2 a2') a_Star Rep ->
    x `notin` dom Gp ->
    x `notin` dom G ->
    MatchTyping (x ~ Tm A1 ++ Gp)
                (a_App p  (Rho Irrel) a_Bullet) (open_tm_wrt_tm B1 (a_Var_f x))
                G (a_App a1 (Rho Irrel) a2)       A
                ((p_Tm (Rho Irrel) a2') :: sub)  (x :: D)
  | MatchTyping_CApp : 
    
   `{MatchTyping Gp p (a_CPi (Eq a0 b0 A0 R0) B1) G a1 
                      (a_CPi (Eq a2 b2 A2 R2) B2) sub D  ->
    DefEq G (dom G) A (open_tm_wrt_co B2 g_Triv) a_Star Rep ->
(*    DefEq G (dom G) a0 b0 A0 R0 -> *)
    DefEq G (dom G) a2 b2 A2 R2 -> 
    c `notin` dom Gp ->
    c `notin` dom G  ->

    MatchTyping (c ~ Co (Eq a0 b0 A0 R0) ++ Gp) (a_CApp p  g_Triv) 
                (open_tm_wrt_co B1 (g_Var_f c))
                G (a_CApp a1 g_Triv) A
                (p_Co g_Triv :: sub) D}
.

Lemma MatchTyping_fv_tm_tm_pattern_args_sub : 
  `{ MatchTyping Gp p B G a A sub D -> fv_tm_tm_pattern_args sub [<=] dom G }.
Proof.
  induction 1; simpl; auto.
  - fsetdec.
  - move: (Typing_context_fv H0) => h. split_hyp. fsetdec.
  - move: (Typing_context_fv H0) => h. split_hyp. fsetdec.
  - fsetdec.
Qed.

Lemma MatchTyping_uniq : 
  `{ MatchTyping Gp p B G a A sub D -> uniq (Gp ++ G) } .
Proof.
  induction 1; simpl; auto.
  eapply Ctx_uniq; eauto. 
Qed.


Lemma map_fst_zip : forall A B (a : list A) (b: list B), length a = length b -> (List.map fst (zip a b)) = a.
Proof.
  intros A B a. induction a.
  all: intros b H.
  all: destruct b; inversion H; simpl in *.
  auto.
  f_equal. auto.
Qed. 

Lemma map_snd_zip : forall A B (a : list A) (b: list B), length a = length b -> (List.map snd (zip a b)) = b.
Proof.
  intros A B a. induction a.
  all: intros b H.
  all: destruct b; inversion H; simpl in *.
  auto.
  f_equal. auto.
Qed. 

Lemma MatchTyping_wf_sub : 
  `{ MatchTyping Gp p B G a A sub D -> 
     length Gp = length sub /\
     wf_sub G (zip (List.map fst Gp) sub) }.
Proof. 
  induction 1; simpl; auto.
  all: destruct IHMatchTyping. 
  all: split; auto.
  all: have SD: dom (zip (List.map fst Gp) sub) [=] (dom Gp) by
         (rewrite dom_zip_map_fst; auto; reflexivity).
  all: econstructor; eauto 2.
  all: try eapply Typing_lc1; eauto.
  all: try rewrite SD; auto.
  move: (Typing_context_fv H0) => h. split_hyp. fsetdec.
  move: (Typing_context_fv H0) => h. split_hyp. fsetdec.
Qed.  

Lemma PatternPath_MatchTyping : forall a p, 
   tm_pattern_agree a p ->
   `{ PatternContexts Ωp Gp Dp F PiB p B ->
      Typing G (a_Fam F) PiB ->
      ValuePath a F ->
      G ⊨ a : A →
      Ctx Gp ->
      uniq (Gp ++ G) ->
      exists sub, MatchTyping Gp p B G a A sub Dp}.
Proof.
  induction 1; intros.
  all: with PatternContexts do ltac:(fun h => inversion h).
  all: subst.
  - exists nil. econstructor; eauto 2.
    eapply Typing_a_Fam_unique; eauto 1.
  - with ValuePath do ltac: (fun h => inversion h; subst). 
    move: (invert_a_App_Role H4) => [A1 [B1 [F0 [Rs h]]]]. split_hyp.
    with Ctx do ltac:(fun h => inversion h; subst). 
    with uniq do ltac:(fun h => inversion h; subst).
    edestruct IHtm_pattern_agree as [s h0]; eauto 2. 
    eexists. econstructor; eauto 1.

  - with ValuePath do ltac: (fun h => inversion h; subst). 
    move: (invert_a_App_Irrel H4) => [A1 [B1 [b0 h]]]. split_hyp.
    with Ctx do ltac:(fun h => inversion h; subst).
    have wf: Ctx G0. auto.
    with uniq do ltac:(fun h => inversion h; subst).
    edestruct IHtm_pattern_agree as [s h0]; eauto 1. 
    eexists. econstructor; eauto 1.

  - with ValuePath do ltac: (fun h => inversion h; subst). 
    move: (invert_a_CApp H3) => [a2 [b2 [A2 [A3 [R1 [B0 h]]]]]]. split_hyp.
    with Ctx do ltac:(fun h => inversion h; subst).
    have wf: Ctx G0. auto.
    with uniq do ltac:(fun h => inversion h; subst).
    edestruct IHtm_pattern_agree as [s h0]; eauto 1.
    destruct phi.
    eexists. econstructor; eauto 1.
Qed.


Lemma MatchTyping_correctness2 : 
  `{ MatchTyping Gp p B G a A s D ->
     G ∥ dom G ⊨ cps_tm B (zip (List.map fst Gp) s) ∼ A : a_Star / Rep }.
Proof.
  induction 1.
  all: intros; simpl in *; auto.
  all: move: (MatchTyping_wf_sub H) => [h0 h1].
  all: set (s := zip (List.map fst Gp) sub) in *.
  all: have SD: dom s [=] dom Gp by
         (unfold s; eapply dom_zip_map_fst; eauto).
  all: have LC: lc_sub s by eauto.

  all: try erewrite (cps_a_Pi) in IHMatchTyping.
  all: try rewrite cps_a_CPi in IHMatchTyping.
  + have EA: DefEq G (dom G) (cps_tm A1 s) A2 a_Star Rep.
    { eapply E_PiFst; eauto 1. }

    erewrite (cps_tm_cons (Rho Rel)).  
 
    rewrite cps_open_tm_wrt_tm.
    { unfold lc_sub. econstructor; eauto. econstructor; eauto. eapply Typing_lc1; eauto. }    
    erewrite wf_cps_subst_var. Focus 2. 
      econstructor; eauto.
      eapply Typing_lc1; eauto.
      fsetdec.
      move: (Typing_context_fv H0) => h. split_hyp.
      fsetdec. 
    

    eapply E_Trans; eauto 1. 2: eapply E_Sym; eauto 1.
    
    have EQ2: cps_tm B1 ((x, p_Tm (Rho Rel) a2) :: s) = 
              cps_tm B1 s.
    { rewrite <- cps_tm_cons.
      rewrite tm_subst_tm_tm_fresh_eq; auto.
      move: (DefEq_context_fv IHMatchTyping) => h. split_hyp.
      simpl in *.
      fsetdec.
    }

    rewrite EQ2. 
    eapply E_PiSnd; eauto 1.
    eapply E_Refl; eauto 1.
    eapply E_Conv; eauto 1. eapply E_Sym; eauto 1.
    autoreg. auto.
  +  have EA: DefEq G (dom G) (cps_tm A1 s) A2 a_Star Rep.
    { eapply E_PiFst; eauto 1. }

    erewrite (cps_tm_cons (Rho Irrel)).  
 
    rewrite cps_open_tm_wrt_tm.
    { unfold lc_sub. econstructor; eauto. econstructor; eauto. 
      eapply Typing_lc1; eauto. }    
    erewrite wf_cps_subst_var. Focus 2.
      econstructor; eauto.
      eapply Typing_lc1; eauto.
      fsetdec.
      move: (Typing_context_fv H0) => h. split_hyp.
      fsetdec. 
    

    eapply E_Trans; eauto 1. 2: eapply E_Sym; eauto 1.
    
    have EQ2: cps_tm B1 ((x, p_Tm (Rho Irrel) a2') :: s) = 
              cps_tm B1 s.
    { rewrite <- cps_tm_cons.
      rewrite tm_subst_tm_tm_fresh_eq; auto.
      move: (DefEq_context_fv IHMatchTyping) => h. split_hyp.
      simpl in *.
      fsetdec.
    } 

    rewrite EQ2. 
    eapply E_PiSnd; eauto 1.
    eapply E_Refl; eauto 1.
    eapply E_Conv; eauto 1. eapply E_Sym; eauto 1.
    autoreg. auto.
  + 
    
   have Eq: Iso G (dom G) (Eq a2 b2 A2 R2)(cps_constraint (Eq a0 b0 A0 R0) s).
   { simpl in *.
     eapply E_CPiFst; eauto 1. 
     eapply E_Sym. eauto 1.
   }

    erewrite cps_co_cons with (g:=g_Triv). 
 
    rewrite cps_open_tm_wrt_co.
    { unfold lc_sub. econstructor; eauto. }
    erewrite wf_cps_co_subst_var with (G:=G)(x:=c). Focus 2.
      econstructor; eauto.
      fsetdec.

    eapply E_Trans; eauto 1. 2: eapply E_Sym; eauto 1.
    
    have EQ2: cps_tm B1 ((c, p_Co g_Triv ) :: s) = 
              cps_tm B1 s.
    { rewrite <- cps_co_cons.
      rewrite co_subst_co_tm_fresh_eq; auto.
      move: (DefEq_context_fv IHMatchTyping) => h. split_hyp.
      simpl in *.
      clear - H5. fsetdec.
    } 

    rewrite EQ2. 
    simpl in Eq.
    eapply E_CPiSnd. eauto 1.
    eapply E_Cast. 2 : eauto 1. 
    eauto 1.
    eauto 1.
Qed.

    (* 

   MatchSubst a p b b'
   is defined outside-in on the pattern p 
       in conjunction with the path a
   at each step, if p has type B then 
       a has type (chain_substiution_args B targs)
       where sub are the type arguments 
       corresponding to the earlier arguments
  
*)



Lemma Ctx_app : forall G1,  Ctx G1 -> forall G2, uniq(G1 ++ G2) -> Ctx G2 -> Ctx (G1 ++ G2).
Proof. 
  induction G1; intros; auto. 
  simpl_env in *. 
  inversion H0. subst.
  inversion H; subst.
  + econstructor; eauto 3.
    specialize (Typing_weakening H8 G2 G1 nil) => WK.
    rewrite! app_nil_r in WK.
    apply WK; eauto 3.
  + econstructor; eauto 3.
    specialize (PropWff_weakening H8 G2 G1 nil) => WK.
    rewrite! app_nil_r in WK.
    apply WK; eauto 3.
Qed.

Lemma MatchSubstTyping :  `{
  forall a p b b' (ms : MatchSubst a p b b'),
  forall Gp G A B sub D, 
    MatchTyping Gp p B G a A sub D ->
    (∀ x : atom, In x D -> x `notin` fv_tm_tm_tm b) ->
  forall C Gp2, 
    uniq (Gp2 ++ G) ->
    (Gp2 ++ Gp ⊨ b : C) ->
    (cps_context Gp2 (zip (List.map fst Gp) sub) ++ G ⊨ b' : 
          cps_tm C (zip (List.map fst Gp) sub)) 
    /\ fv_tm_tm_tm b' [<=] fv_tm_tm_tm b \u dom G
}.
Proof. 
  induction 1; intros.
  all: with MatchTyping do ltac:(fun h => inversion h; subst; clear h).
  - simpl in *. 
    have EQ: cps_context Gp2 ∅ = Gp2.
    { generalize Gp2. induction Gp0. simpl. auto.
      simpl. destruct a. rewrite IHGp0. f_equal.
      f_equal. apply cps_sort_nil. }
    rewrite EQ.
    with (Typing _ b _) do ltac:(fun h => 
        specialize (Typing_weakening h G Gp2 nil eq_refl)) end.
    move=> WK. rewrite app_nil_r in WK. 
    split. 
    apply WK.
    rewrite app_nil_r in H3.
    eapply Ctx_app; eauto using Typing_Ctx.
    fsetdec.

  -  with MatchTyping do ltac:(fun h =>
         specialize (IHms Gp0 G _ _ sub0 D h ltac:(auto) C); 
         move: (MatchTyping_wf_sub h) => [ln wfs];
         move: (MatchTyping_correctness2 h) => de
    ) end.
    rewrite cps_a_Pi in de.
    with (Typing _ b1) do ltac:(fun h2 => move:h2=>Tb1) end. 
    rewrite app_assoc in Tb1.
    have U: uniq ((Gp2 ++ x ~ Tm A1) ++ G). 
      { 
        apply Typing_Ctx in Tb1. apply Ctx_uniq in Tb1.
        simpl_env in *.
        solve_uniq.
      } 

    specialize (IHms _ U Tb1). 
    unfold cps_context in *.
    rewrite EnvImpl.map_app in IHms.
    unfold one in IHms.
    simpl in IHms.
    set (s := (zip (List.map fst Gp0) sub0)).
    have TA: Typing G a (cps_tm A1 s). {

      eapply E_Conv; eauto 1.
      eapply E_Sym.
      eapply E_PiFst.
      eauto.
      autoreg.
      autoinv.
      auto.
      }
    move: IHms => [Tb2 fvb2].
    destruct tm_substitution_mutual as [L _].
    specialize (L _ _ _ Tb2).
    specialize (L _ _ _ TA).
    specialize (L (cps_context Gp2 s) x).
    lapply L. clear L. move=>L. 2:   simpl_env; f_equal.

    have EQ3: utils.map = EnvImpl.map. auto. rewrite EQ3 in L.
    have EQ4:
       EnvImpl.map (tm_subst_tm_sort a x) (cps_context Gp2 s) = 
       EnvImpl.map (cps_sort^~ (x ~ (p_Tm (Rho Rel) a) ++ s)) Gp2.
    { 
      generalize Gp2.
      induction Gp1.
      simpl. auto.
      simpl. destruct a0. rewrite IHGp1.
      f_equal. f_equal. eapply cps_sort_cons.
    }
    rewrite EQ4 in L.
    have EQ5:
      tm_subst_tm_tm a x (cps_tm C s) = 
      cps_tm C (x ~ (p_Tm (Rho Rel) a) ++ s).
    {
      eapply cps_tm_cons.
    } 
    rewrite EQ5 in L.
    split.
    eapply L.
    rewrite fv_tm_tm_tm_tm_subst_tm_tm_upper.
    move: (Typing_context_fv H13) => [? _].
    fsetdec.
  - with MatchTyping do ltac:(fun h =>
         specialize (IHms Gp0 G _ _ sub0 D0 h);
         move: (MatchTyping_wf_sub h) => [ln wfs];
         move: (MatchTyping_correctness2 h) => de 
    ) end.
    have ?: (∀ x : atom, In x D0 ⟹ x ∉ fv_tm_tm_tm b1).
    { intros y In. eapply H1. simpl; eauto. }
    specialize (IHms ltac:(auto) C).

    rewrite cps_a_Pi in de.
    with (Typing _ b1) do ltac:(fun h2 => move: h2=>Tb1) end.
    rewrite app_assoc in Tb1.
    have U: uniq ((Gp2 ++ x ~ Tm A1) ++ G). 
      { 
        apply Typing_Ctx in Tb1. apply Ctx_uniq in Tb1.
        simpl_env in *.
        solve_uniq.
      } 

    specialize (IHms _ U Tb1). 
    unfold cps_context in *.
    rewrite EnvImpl.map_app in IHms.
    unfold one in IHms.
    simpl in IHms.
    set (s := (zip (List.map fst Gp0) sub0)).
    have TA: Typing G a2' (cps_tm A1 s). {

      eapply E_Conv; eauto 1.
      eapply E_Sym.
      eapply E_PiFst.
      eauto.
      autoreg.
      autoinv.
      auto.
      }

    move: IHms => [Tb2 fvb2].
    destruct tm_substitution_mutual as [L _].
    specialize (L _ _ _ Tb2).
    specialize (L _ _ _ TA).
    specialize (L (cps_context Gp2 s) x).
    lapply L. clear L. move=>L. 2: {
      simpl_env.
      f_equal.
    }    
    have EQ3: utils.map = EnvImpl.map. auto. rewrite EQ3 in L.
    have EQ4:
       EnvImpl.map (tm_subst_tm_sort a2' x) (cps_context Gp2 s) = 
       EnvImpl.map (cps_sort^~ (x ~ (p_Tm (Rho Irrel) a2') ++ s)) Gp2.
    { 
      generalize Gp2.
      induction Gp1.
      simpl. auto.
      simpl. destruct a0. rewrite IHGp1.
      f_equal. f_equal. eapply cps_sort_cons.
    }
    rewrite EQ4 in L.
    have EQ5:
      tm_subst_tm_tm a2' x (cps_tm C s) = 
      cps_tm C (x ~ (p_Tm (Rho Irrel) a2') ++ s).
    {
      eapply cps_tm_cons.
    } 
    rewrite EQ5 in L.
    rewrite tm_subst_tm_tm_fresh_eq in L.
    intro. apply (H1 x); simpl; auto. fsetdec.
    split.
    eapply L.
    fsetdec.
  - with MatchTyping do ltac:(fun h =>
         specialize (IHms Gp0 G _ _ sub0 D h ltac:(auto) C); 
         move: (MatchTyping_wf_sub h) => [ln wfs];
         move: (MatchTyping_correctness2 h) => de
    ) end.
    rewrite cps_a_CPi in de.
    with (Typing _ b1) do ltac:(fun h2 => move:h2=>Tb1). 
    rewrite app_assoc in Tb1.
    have U: uniq ((Gp2 ++ c ~ Co (Eq a0 b0 A0 R0)) ++ G). 
      {
        apply Typing_Ctx in Tb1. apply Ctx_uniq in Tb1.
        simpl_env in *.
        solve_uniq.
      } 

    specialize (IHms _ U Tb1). 
    unfold cps_context in *.
    rewrite EnvImpl.map_app in IHms.
    unfold one in IHms.
    simpl in IHms.
    set (s := (zip (List.map fst Gp0) sub0)).
    move: IHms => [Tb2 fb2].
    split; auto.

    simpl in Tb2.
    fold s in Tb2. simpl in de. fold s in de.
    destruct co_substitution_mutual as [L _].
    specialize (L _ _ _ Tb2 G (dom G) (cps_tm a0 s) (cps_tm b0 s) (cps_tm A0 s) R0).
    simpl_env in L.
    specialize (L (EnvImpl.map (cps_sort^~ s) Gp2) c g_Triv eq_refl).
    have ?: G ∥ dom G ⊨ cps_tm a0 s ∼ cps_tm b0 s : cps_tm A0 s / R0.
    { 
      eapply E_Cast. eapply H7.
      eapply sym_iso.
      eapply E_CPiFst. eauto 1.
    } 

    specialize (L ltac:(auto)).
    have EQ3: utils.map = EnvImpl.map. auto. rewrite EQ3 in L.
    have EQ4:
       EnvImpl.map (co_subst_co_sort g_Triv c) (cps_context Gp2 s) = 
       EnvImpl.map (cps_sort^~ (c ~ (p_Co g_Triv) ++ s)) Gp2.
    { 
      generalize Gp2.
      induction Gp1.
      simpl. auto.
      simpl. destruct a. rewrite IHGp1.
      f_equal. f_equal. eapply cps_sort_cons_co.
    }
    rewrite EQ4 in L.
    have EQ5:
      co_subst_co_tm g_Triv c (cps_tm C s) = 
      cps_tm C (c ~ (p_Co g_Triv) ++ s).
    {
      simpl. auto.
    } 
    rewrite EQ5 in L.
    rewrite co_subst_co_tm_fresh_eq in L. 
    show_fresh. fsetdec.
    eapply L. 
    auto.
Qed.


Lemma MatchSubstTyping_start :  `{
  forall a p b b' (ms : MatchSubst a p b b'),
  forall Gp G A B sub Dp, MatchTyping Gp p B G a A sub Dp ->
  G ⊨ A : a_Star -> 
  (Gp ⊨ b : B) ->
  (forall x, In x Dp -> x `notin` fv_tm_tm_tm b) ->
  (G ⊨ b' : A) 
}.
Proof.
  intros.
  move: (MatchSubstTyping ms H) => h0.
  have f : (∀ x : atom, In x Dp ⟹ x ∉ fv_tm_tm_tm b).
  { eapply H2. }
  specialize (h0 f B nil ltac:(eapply Ctx_uniq; eapply Typing_Ctx; eauto)
                       ltac:(auto) ).   
  simpl in h0.
  eapply E_Conv; eauto 1. eapply h0.
  eapply MatchTyping_correctness2; eauto 1.
Qed.

(* TODO: move this to ett_match *)
Hint Resolve tm_pattern_agree_cong tm_pattern_agree_tm_tm_agree : nominal.
Hint Resolve Rename_tm_pattern_agree : nominal.

(* We can freshen the axiom WRT to any context *)
Lemma Axiom_Freshening : forall s (Γ:list(atom*s)), 
  `{ MatchSubst a p1 b1 b' ->
  Rename p b p1 b1 D1 D ->
  PatternContexts Ωp Γp Dp F PiB p B ->
  Γp ⊨ b : B ->
  (forall x, In x Dp -> x `notin` fv_tm_tm_tm b) -> 
  exists p2 b2 B' Dp' Ωp' Γp', 
  MatchSubst a p2 b2 b' /\
  Rename p b p2 b2 (dom Γ \u D1) D /\
  PatternContexts Ωp' Γp' Dp' F PiB p2 B' /\
  Γp' ⊨ b2 : B' /\
  disjoint Γp' Γ /\
  (forall x, In x Dp' -> x `notin` fv_tm_tm_tm b2)}. 
Proof.
  intros.

  move: (MatchSubst_match H) => a_agree_p1.
  (* Rename the pattern, avoiding dom G *)
  have Lcb: lc_tm b. eapply Typing_lc1. eauto.  
  have Pp: Pattern p. eapply patctx_pattern. eauto.

  destruct (rename p b (dom Γ \u (fv_tm_tm_tm a) \u (fv_tm_tm_tm p))) 
    as [[p3 b3] D3] eqn:EQN.
  move: (rename_Rename ((dom Γ \u (fv_tm_tm_tm a) \u (fv_tm_tm_tm p)))  Pp Lcb) => RN.
  rewrite EQN in RN. simpl in RN. clear EQN.

  have a_agree_p: tm_pattern_agree a p.
  eapply tm_pattern_agree_rename_inv_2; eauto. 

  move: (Rename_chain_subst RN) => eq.
  move: (Rename_chain_subst H0) => eq2.
  rewrite <- matchsubst_chain_subst in eq; eauto with nominal.
  rewrite <- matchsubst_chain_subst in eq2; eauto with nominal.
  repeat eexists.

Admitted. (* Freshening lemma for axioms *)


Theorem MatchSubst_preservation2 : `{
  MatchSubst a p1 b1 b' →
  Rename p b p1 b1 ((fv_tm_tm_tm a) ∪ (fv_tm_tm_tm p)) D →
  binds F (Ax p b PiB R1 Rs) toplevel →
  Γ ⊨ a : A →
  Γ ⊨ b' : A}.
Proof.
  intros until 0.
  move=> ms rn bds tpg_a.

  (* Deriving basic facts *)
  (* move: (Rename_Pattern rn) => [pat_p pat_p1]. *)
  move: (toplevel_inversion bds) => [Ωp] [Γp] [Dp] [B] [patctx_p] 
     [tpg_b] [roleing [rnge [tyB fr]]].
  move: (MatchSubst_match ms) => a_agree_p1.
  (* move: (Rename_spec rn) => [fv_p1 fv_b1]. *)
  (* move: (Rename_PatCtx_Typing_exist rn patctx_p tpg_b) => [Ωp1] [Γp1] [B1] [patctx_p1] tpg_b1. *)
  move: (Typing_regularity tpg_a) => tpg_A.


  edestruct (@Axiom_Freshening _ Γ) as 
      [p2 [b2 [B' [Dp' [Ωp' [Γp' h]]]]]]; eauto 1.
  split_hyp.
(*
  have Dp' : atoms. admit.
  have Ωp' : role_context. admit.
  have Γp' : context. admit.
  have ms2: MatchSubst a p2 b2 b'. admit.
  have PC2: PatternContexts Ωp' Γp' Dp' F PiB p2 B'. admit.
  have Tb2:  Γp' ⊨ b2 : B'. admit. 
  have u: uniq (Γp' ++ Γ). admit.
  have ff: AtomSetImpl.For_all (λ x : atom, x ∉ fv_tm_tm_tm b2) Dp'. admit.
*)
  clear ms rn patctx_p a_agree_p1.

  (* new stuff *)
  edestruct PatternPath_MatchTyping 
    with (a:=a)(G := Γ)(Gp := Γp')(p := p2) as [sub0 h0]; eauto 2.
  eapply MatchSubst_match; eauto.
  have TF: Typing nil (a_Fam F) PiB. eapply E_Fam; eauto 1. 
  move: (Typing_weakening TF  Γ nil nil eq_refl) => w.

  simpl_env in w. eapply w; eauto.
  eapply MatchSubst_ValuePath; eauto.
  eapply uniq_app_4. 
  eapply Ctx_uniq; eauto.
  eapply Ctx_uniq; eauto.
  auto.
  eapply MatchSubstTyping_start; eauto.
  Unshelve. all: eauto.
Qed.



(* -------------------------------------------------------- *)


Lemma Beta_preservation : `(Beta a b R →  forall G A, Typing G a A -> Typing G b A).
Proof.
  induction 1; intros G A0 TH.
  - have CT: Ctx G by eauto.
    have RA: Typing G A0 a_Star by eauto using Typing_regularity.
    destruct rho.
    + destruct (invert_a_App_Rel TH) as (A & B & TB & DE & h).
      destruct (invert_a_UAbs TB) as (A1 & B1 & DE2 & [L TB1] & TA1 ).
      eapply E_Conv with (A := (open_tm_wrt_tm B1 b)); eauto 2.
      pick fresh x.
      move: (TB1 x ltac:(auto)) =>  [T1 [T2 RC]].
      rewrite (tm_subst_tm_tm_intro x v); eauto 2.
      rewrite (tm_subst_tm_tm_intro x B1); eauto.

      eapply Typing_tm_subst with (A:=A1); eauto 5.
      eapply E_Sym.
      eapply E_Trans with (a1:= open_tm_wrt_tm B b); eauto 2.
      eapply E_PiSnd; eauto 1.
      eauto.

    + destruct (invert_a_App_Irrel TH) as (A & B & b0 & Tb & Tb2 & EQ & DE ).
      subst.
      destruct (invert_a_UAbs Tb) as (A1 & B1 & DE2 & [L TB1] & TA1 ).
      eapply E_Conv with (A := (open_tm_wrt_tm B1 b0)); eauto 2.
      pick fresh x.
      move: (TB1 x ltac:(auto)) =>  [T1 [T2 RC]].
      inversion RC. subst.
      rewrite (tm_subst_tm_tm_intro x v); eauto 2.
      rewrite (tm_subst_tm_tm_intro x B1); eauto 2.
      rewrite (tm_subst_tm_tm_fresh_eq _ _ _ H1).
      rewrite - (tm_subst_tm_tm_fresh_eq _ b0 x H1).
      eapply Typing_tm_subst with (A:=A1); eauto 2.
      eapply E_Conv with (A:=A); eauto using E_PiFst, param_sub1.
      eapply E_Sym.
      eapply E_Trans with (a1 := open_tm_wrt_tm B b0). auto.
      eapply E_PiSnd; eauto using E_Refl, param_covariant.
   - have CT: Ctx G by eauto.
     have RA: Typing G A0 a_Star by eauto using Typing_regularity.
     destruct (invert_a_CApp TH) as (eq & a1 & b1 & A1 & R1 & B1 & h0 & h1 & h2 ).
     destruct (invert_a_UCAbs h0) as (a2 & b2 & A2 & R3 & B2 & h4 & h5 & [L h6] ).
     pick fresh c.
     move: (h6 c ltac:(auto)) => [T1 T2].
     have? : DefEq G (dom G) a2 b2 A2 R3. 
     apply E_CPiFst in h5. apply E_Cast in h5. auto.
     eapply E_Sub; eauto using param_sub1.
     eapply E_Conv with (A:= (open_tm_wrt_co B2 g_Triv)); eauto 2.
     rewrite (co_subst_co_tm_intro c a'); eauto.
     rewrite (co_subst_co_tm_intro c B2); eauto.
     eapply Typing_co_subst; eauto.
     eapply E_Sym.
     eapply E_Trans with (a1 := open_tm_wrt_co B1 g_Triv). auto.
     eapply E_CPiSnd; eauto 2.
   - (* Axiom *)
     eapply MatchSubst_preservation2; eauto.
   - (* Pattern True *)
     move: (invert_a_Pattern TH) => [A [A1 [B0 [C h]]]].
     split_hyp.
     eapply E_Conv with (A := C); eauto 1.
     eapply BranchTyping_preservation; eauto 1.
     eauto using AppsPath_CasePath.
     autoreg. auto.
     autoreg. auto.
   - dependent induction TH; eauto.
Qed.


Lemma E_Beta2 :  ∀ (G : context) (D : available_props) (a1 a2 B : tm) R,
       Typing G a1 B → Beta a1 a2 R → DefEq G D a1 a2 B R.
Proof.
  intros; eapply E_Beta; eauto.
  eapply Beta_preservation; eauto.
Qed.

Lemma PatternContexts_dom :
  `{ PatternContexts W G D F A p B -> fv_tm_tm_tm p [<=] dom G  }.
Proof. 
  induction 1; simpl; try rewrite IHPatternContexts; try fsetdec.
Qed.  

Lemma Par_fv_preservation: forall W x a b R, Par W a b R ->
                                        x `notin` fv_tm_tm_tm a ->
                                        x `notin` fv_tm_tm_tm b.
Proof.
  intros.
  induction H; eauto 2; simpl.
  all: simpl in H0.
  all: try solve [move => h0; apply AtomSetFacts.union_iff in h0; case: h0 => h0; eauto; apply IHreduction_in_one; auto].
  - simpl in *.
    have: x `notin` fv_tm_tm_tm (open_tm_wrt_tm a' b') => h0.
    apply fv_tm_tm_tm_open_tm_wrt_tm_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    ok.
    ok.
    auto.
  - auto.
  - have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a' g_Triv) => h0.
    apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    fsetdec.
    auto.
  - auto.
  - pick fresh x0.
    assert (Fl : x0 `notin` L). auto.
    assert (Fa : x `notin` fv_tm_tm_tm (open_tm_wrt_tm a (a_Var_f x0))).
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper. auto.
    move: (H1 x0 Fl Fa) => h0.
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto.
  - pick fresh x0.
    have na': x `notin` fv_tm_tm_tm A'. eauto.
    have nb: x `notin` fv_tm_tm_tm (open_tm_wrt_tm B (a_Var_f x0)).
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_upper. eauto.
    have nob': x `notin` fv_tm_tm_tm (open_tm_wrt_tm B' (a_Var_f x0)). eauto.
    have nb': x `notin` fv_tm_tm_tm B'.
    rewrite fv_tm_tm_tm_open_tm_wrt_tm_lower. eauto.
    eauto.
  - pick_fresh c0.
    have: x `notin` fv_tm_tm_tm (open_tm_wrt_co a (g_Var_f c0)) => h0.
    apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    simpl in h0.
    fsetdec.
    have K:= H1 c0 ltac:(auto) h0.
    move => h1.
    apply K. auto.
    apply fv_tm_tm_tm_open_tm_wrt_co_lower; auto.
  - pick fresh c0 for L.
    have: x `notin` fv_tm_tm_tm (open_tm_wrt_co B (g_Var_f c0)) => h0.
    apply fv_tm_tm_tm_open_tm_wrt_co_upper in h0.
    apply AtomSetFacts.union_iff in h0.
    case:h0; eauto => h0.
    simpl in h0.
    fsetdec.
    have h2: x `notin` fv_tm_tm_tm (open_tm_wrt_co B' (g_Var_f c0)). eauto.
    move: (fv_tm_tm_tm_open_tm_wrt_co_lower B' (g_Var_f c0)) => h3.
    have h4: x `notin` fv_tm_tm_tm a'. fsetdec.
    move => h1.
    apply AtomSetFacts.union_iff in h1.
    case: h1 => h1; eauto.
    apply AtomSetFacts.union_iff in h1.
    case: h1 => h1; eauto.
    fsetdec.
  - apply toplevel_inversion in H.
    autofwd.
    inversion H. subst.
    show_fresh.
    simpl in *.
    fsetdec. 
  - apply toplevel_inversion in H. 
    autofwd.

    edestruct (@Axiom_Freshening role [(x , Nom)]) as 
      [p2 [b2 [B' [Dp' [Ωp' [Γp' h]]]]]]. eauto 1. eauto 1.
    eauto 1. eauto 1. eauto 1.
    split_hyp.
    move:(Rename_MatchSubst_fv H14 H13) => h.
    simpl in *.
    move=> xin.
    apply h in xin.
    destruct (AtomSetImpl.union_1 xin).
    admit. (* !!!! Rename_MatchSubst_fv seems too weak. *)
    fsetdec.
  - admit.  (* Rename / Axiom, same as above *)
  - eauto.
  - have: x `notin` fv_tm_tm_tm a'. fsetdec.
    have: x `notin` fv_tm_tm_tm b1'. fsetdec.
    move: H4.
    generalize a' b1' b.
    induction 1; simpl; try fsetdec.
  - eauto.
Admitted. (* Par_fv_preservation, nice but unused *)


Lemma reduction_in_Par : forall a a' R, reduction_in_one a a' R ->
                                   forall W, roleing W a R -> Par W a a' R.
Proof.
  induction 1; intros.
  all: try solve [inversion H1; subst; eauto].
  all: try solve [inversion H0; subst; eauto].
  - inversion H1.
    pick fresh x and apply Par_Abs.
    eapply H0; eauto 2.
  - inversion H2; subst.
    eauto.
  - inversion H; subst.
    + inversion H0; subst.
      eapply Par_Beta; eauto.
    + inversion H0; subst.
      eapply Par_CBeta; eauto.
    + move: H3 H2. 
     (* eapply Par_Axiom; eauto. eapply rctx_uniq in H0. auto. *)
     all: admit.
    + inversion H0; subst. eapply Par_PatternTrue; eauto.
    + inversion H0; subst. eapply Par_PatternFalse; eauto. 
Admitted. (* reduction in Par, nice but unused *)


Lemma reduction_in_one_fv_preservation: forall x a b R, 
    reduction_in_one a b R -> 
    x `notin` fv_tm_tm_tm a ->
    x `notin` fv_tm_tm_tm b.
Proof.
  induction 1; intros.
  + autofresh.
    simpl in *.
    unhide Fr.
    rewrite -> fv_tm_tm_tm_open_tm_wrt_tm_upper in H0. 
    simpl in H0.
    move: (H0 ltac:(fsetdec)) => h1.
    move => h. apply h1.
    apply fv_tm_tm_tm_open_tm_wrt_tm_lower.
    auto.
  + simpl in *. fsetdec.
  + simpl in *. fsetdec.
  + simpl in *. fsetdec.
  + eapply Beta_fv_preservation. eauto. eauto.
Qed.

Lemma reduction_rhocheck : forall a a' rho x R, 
    reduction_in_one a a' R -> RhoCheck rho x a -> RhoCheck rho x a'.
Proof.
  intros. inversion H0.
  -  eauto using reduction_in_one_lc.
  -  eauto using reduction_in_one_fv_preservation.
Qed.

Lemma RolePath_preservation :
forall a a' R, reduction_in_one a a' R -> forall R1 Rs, 
   RolePath a  (R1 :: Rs) -> RolePath a'  (R1 :: Rs).
Proof.
  intros a a' R H.
  induction H; intros.
  - inversion H1.
  - inversion H1; subst; eauto.
  - inversion H0; subst; eauto.
  - inversion H2.
  - assert False.  move: (RolePath_no_Beta H0) => h0.
    eapply h0. eauto.
    contradiction.
Qed.

Lemma BranchTyping_congruence : 
  `{ BranchTyping G Apps5 Nom a A0 t ps A1 B C ->
    forall G D a', Typing G B a_Star ->
    DefEq G D a a' A0 Nom ->
    exists B', BranchTyping G Apps5 Nom a' A0 t ps A1 B' C /\
        DefEq G D B B' a_Star Rep}.
Proof.
  induction 1; intros. 
  - subst.
    autoinv.
    move: (PropWff_regularity H6) => [t1 t2].
    move: (DefEq_regularity H5) => t3.
    move: (PropWff_regularity t3) => [_ t5].
    exists (a_CPi (Eq a' (apply_pattern_args b pattern_args5) A Nom) C1).
    split.
    eapply BranchTyping_Base; eauto. eapply DefEq_lc2; eauto.
    pick fresh c and apply E_CPiCong2; eauto 1.
    eapply E_PropCong; eauto 1.
    eapply E_Refl; eauto 1.
    move: (H4 c ltac:(auto)) => h0. hide Fr.
    eapply E_Refl; eauto 1.
  - autoinv.
    autofresh.
    have h0: DefEq (nil ++ [(x0, Tm A)] ++ G0) D a a' A1 Nom.
    { eapply DefEq_weakening with (F:=nil)(G:=G0).
      eauto 1. auto. simpl. eapply Typing_Ctx; eauto. }
    simpl in h0.
    move: (H0 _ _ _ H3 h0) => [B' [h1 h2]].
    eexists.
    split.
    eapply (@BranchTyping_PiRole_exists x0); auto.
    rewrite <- (open_tm_wrt_tm_close_tm_wrt_tm B' x0) in h1.
    eapply h1.  rewrite fv_tm_tm_tm_close_tm_wrt_tm. unhide Fr. fsetdec.
    eapply (@E_PiCong3 x0); eauto 2.
    unhide Fr. rewrite fv_tm_tm_tm_close_tm_wrt_tm. fsetdec.
    rewrite open_tm_wrt_tm_close_tm_wrt_tm.
    eapply h2.
  - autoinv. autofresh.
    have h0: DefEq (nil ++ [(x0, Tm A)] ++ G0) D a a' A1 Nom.
    { eapply DefEq_weakening with (F:=nil)(G:=G0).
      eauto 1. auto. simpl. eapply Typing_Ctx; eauto. }
    simpl in h0.
    move: (H0 _ _ _ H3 h0) => [B' [h1 h2]].
    eexists.
    split.
    eapply (@BranchTyping_PiRel_exists x0); auto.
    rewrite <- (open_tm_wrt_tm_close_tm_wrt_tm B' x0) in h1.
    eapply h1.  rewrite fv_tm_tm_tm_close_tm_wrt_tm. unhide Fr. fsetdec.
    eapply (@E_PiCong3 x0); eauto 2.
    unhide Fr. rewrite fv_tm_tm_tm_close_tm_wrt_tm. fsetdec.
    rewrite open_tm_wrt_tm_close_tm_wrt_tm.
    eapply h2.
  - autoinv. autofresh.
    have h0: DefEq (nil ++ [(x0, Tm A)] ++ G0) D a a' A1 Nom.
    { eapply DefEq_weakening with (F:=nil)(G:=G0).
      eauto 1. auto. simpl. eapply Typing_Ctx; eauto. }
    simpl in h0.
    move: (H0 _ _ _ H3 h0) => [B' [h1 h2]].
    eexists.
    split.
    eapply (@BranchTyping_PiIrrel_exists x0); auto.
    rewrite <- (open_tm_wrt_tm_close_tm_wrt_tm B' x0) in h1.
    eapply h1.  rewrite fv_tm_tm_tm_close_tm_wrt_tm. unhide Fr. fsetdec.
    eapply (@E_PiCong3 x0); eauto 2.
    unhide Fr. rewrite fv_tm_tm_tm_close_tm_wrt_tm. fsetdec.
    rewrite open_tm_wrt_tm_close_tm_wrt_tm.
    eapply h2.
  - autoinv. autofresh.
    have h0: DefEq (nil ++ [(x0, Co phi)] ++ G0) D a a' A Nom.
    { eapply DefEq_weakening with (F:=nil)(G:=G0).
      eauto 1. auto. simpl. eapply Typing_Ctx; eauto. }
    simpl in h0.
    move: (H0 _ _ _ H3 h0) => [B' [h1 h2]].
    eexists.
    split.
    eapply (@BranchTyping_CPi_exists x0); auto.
    rewrite <- (open_tm_wrt_co_close_tm_wrt_co B' x0) in h1.
    eapply h1.  unhide Fr.  
    rewrite fv_co_co_tm_close_tm_wrt_co.
    fsetdec.
    destruct phi.
    eapply (@E_CPiCong3 x0); eauto 2.
    unhide Fr. 
    autorewrite with lngen.
    fsetdec.
    eapply refl_iso; eauto 1.
    rewrite open_tm_wrt_co_close_tm_wrt_co.
    eapply h2.
Qed.


Lemma reduction_preservation : forall a a' R, reduction_in_one a a' R -> forall G A D, 
      Typing G a A -> Typing G a' A /\ DefEq G D a a' A R.
Proof.
  move=> a a' R r.
  induction r.
  all: move=> G A D tpga.
  - move: (Typing_regularity tpga) => h0.
    autoinv. 
    split.
    + eapply E_Conv with (A := (a_Pi Irrel x x0)); auto.
    pick fresh y and apply E_Abs; auto.
    apply_first_hyp; auto.
    apply H2. auto. 
    eapply reduction_rhocheck; eauto. 
    eapply H2. auto.
    + 
    eapply E_EqConv with (A := (a_Pi Irrel x x0)); auto.
    pick fresh y and apply E_AbsCong2; auto;
    move: (H0 y ltac:(auto)) => ih;
    move: (H2 y ltac:(auto)) => [ty1 [ty2 rc]];
    move: (ih _ _ D ty1) => [ty3 de]; 
    hide Fr.                             
    eapply de.
    auto.
    eapply reduction_rhocheck; eauto.
  - move: (Typing_regularity tpga) => h0.
    destruct nu; autoinv.
    move: (IHr _ _ D H0) => [h1 h2].
    split.
    + eapply E_Conv with (A := (open_tm_wrt_tm x0 b)); auto.
      move: (RolePath_preservation r H3) => ?.
      eapply E_TApp; eauto 1.
    + eapply E_EqConv with (A := (open_tm_wrt_tm x0 b)); auto.
      eapply E_TAppCong; eauto 1.
      eapply E_Refl; eauto.
      eapply RolePath_preservation; eauto 1.
      eapply E_TApp; eauto 1.
      eapply RolePath_preservation; eauto 1.
    + move: (IHr _ _ D H0) => [h1 h2].
      split.
      eapply E_Conv with (A := (open_tm_wrt_tm x0 b)); auto.
      eauto.
      eapply E_EqConv with (A := (open_tm_wrt_tm x0 b)); auto.
      eapply E_AppCong; eauto 2.
    + move: (IHr _ _ D H0) => [h1 h2]. subst.
      split.
      eapply E_Conv with (A := (open_tm_wrt_tm x0 x1)); auto.
      eauto.
      eapply E_EqConv with (A := (open_tm_wrt_tm x0 x1)); auto.
      eapply E_IAppCong; eauto 2.
      
  - move: (Typing_regularity tpga) => h0. 
    autoinv; subst.
    move: (IHr _ _ D H0) => [h1 h2].
    split.
    + eapply E_Conv with (A:= (open_tm_wrt_co x3 g_Triv)); auto.
      eapply E_CApp; eauto. 
    + eapply E_EqConv with (A:= (open_tm_wrt_co x3 g_Triv)); auto.
      eapply E_CAppCong; eauto 2.
  -  move: (Typing_regularity tpga) => h0. 
     move: (invert_a_Pattern tpga) => h1.
     move: h1 => [A0 [A1 [B [C h]]]]. split_hyp.
     move: (IHr _ _ D H1) => [h1 h2].
     split.
     + have h3: Typing G B a_Star. { autoreg. auto. }
       move: (BranchTyping_congruence H4 h3 h2 ) => [B' [h4 h5]].
       eapply E_Conv with (A := C); auto.
       clear H4.
       eapply E_Case with (B := B'); eauto 1. 
       eapply E_Conv with (A := B)(B := B'). auto.
       eapply DefEq_weaken_available. eauto.
       autoreg; auto.
     + have h3: Typing G B a_Star. { autoreg. auto. }
       move: (BranchTyping_congruence H4 h3 h2 ) => [B' [h4 h5]].
       eapply E_EqConv with (A := C); auto.
       eapply E_PatCong with (B := B)(B':=B'); eauto 1.
       eapply E_EqConv with (A := B); auto.
       eapply E_Refl; eauto.
  - split.
    eapply Beta_preservation; eauto.
    eapply E_Beta2; eauto.
Qed.

