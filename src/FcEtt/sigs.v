Require Import FcEtt.imports.

Require Export FcEtt.ett_ott.
Require Export FcEtt.utils.



(**************** Ext_Wf ****************)

Module Type ext_wf_sig.

Axiom ctx_wff_mutual :
  (forall G0 r a A, Typing G0 r a A -> Ctx G0) /\
  (forall G0 r phi,   PropWff G0 r phi -> Ctx G0) /\
  (forall G0 D r p1 p2, Iso G0 D r p1 p2 -> Ctx G0) /\
  (forall G0 D r A B T,   DefEq G0 D r A B T -> Ctx G0) /\
  (forall G0, Ctx G0 -> True).

Axiom lc_mutual :
  (forall G0 r a A, Typing G0 r a A -> lc_tm a /\ lc_tm A) /\
  (forall G0 r phi,   PropWff G0 r phi -> lc_constraint phi) /\
  (forall G0 D r p1 p2, Iso G0 D r p1 p2 -> lc_constraint p1 /\ lc_constraint p2) /\
  (forall G0 D r A B T,   DefEq G0 D r A B T -> lc_tm A /\ lc_tm B /\ lc_tm T) /\
  (forall G0, Ctx G0 -> forall x s , binds x s G0 -> lc_sort s).

Axiom Typing_lc  : forall G0 r a A, Typing G0 r a A -> lc_tm a /\ lc_tm A.
Axiom PropWff_lc : forall G0 r phi,   PropWff G0 r phi -> lc_constraint phi.
Axiom Iso_lc : forall G0 D r p1 p2, Iso G0 D r p1 p2 -> lc_constraint p1 /\ lc_constraint p2.
Axiom DefEq_lc : forall G0 D r A B T,   DefEq G0 D r A B T -> lc_tm A /\ lc_tm B /\ lc_tm T.

Axiom Typing_lc1 : forall G0 r a A, Typing G0 r a A -> lc_tm a.
Axiom Typing_lc2 : forall G0 r a A, Typing G0 r a A -> lc_tm A.

Axiom Iso_lc1 : forall G0 D r p1 p2, Iso G0 D r p1 p2 -> lc_constraint p1.
Axiom Iso_lc2 : forall G0 D r p1 p2, Iso G0 D r p1 p2 -> lc_constraint p2.

Axiom DefEq_lc1 : forall G0 D r A B T,   DefEq G0 D r A B T -> lc_tm A.
Axiom DefEq_lc2 : forall G0 D r A B T,   DefEq G0 D r A B T -> lc_tm B.
Axiom DefEq_lc3 : forall G0 D r A B T,   DefEq G0 D r A B T -> lc_tm T.

Axiom Ctx_lc : forall G0, Ctx G0 -> forall x s , binds x s G0 -> lc_sort s.

Axiom Ctx_uniq : forall G, Ctx G -> uniq G.

Axiom Toplevel_lc : forall c s, binds c s toplevel -> lc_sig_sort s.

(* Axiom Path_lc : forall T a, Path T a -> lc_tm a.

Axiom DataTy_lc : forall A, DataTy A a_Star -> lc_tm A. *)

Axiom Value_lc : forall A, Value A -> lc_tm A.

Axiom CoercedValue_lc : forall A, CoercedValue A -> lc_tm A.

Axiom SubRho_trans : forall r2 r1 r3, SubRho r1 r2 -> SubRho r2 r3 -> SubRho r1 r3.

Axiom dom_SubG : forall G1 G2, SubG G1 G2 -> dom G1 [=] dom G2.

Axiom binds_SubG : forall G G2 x rho1 A, SubG G G2  -> binds x (Tm rho1 A) G -> 
                                  exists rho2, SubRho rho1 rho2 /\ binds x (Tm rho2 A) G2.

End ext_wf_sig.

(**************** EXT Weak ****************)

Module Type ext_weak_sig.

Include ext_wf_sig.

Axiom weaken_available_mutual:
  (forall G1 r a A,   Typing G1 r a A -> True) /\
  (forall G1 r phi,   PropWff G1 r phi -> True) /\
  (forall G1 D r p1 p2, Iso G1 D r p1 p2 -> forall D', D [<=] D' -> Iso G1 D' r p1 p2) /\
  (forall G1 D r A B T,   DefEq G1 D r A B T -> forall D', D [<=] D' -> DefEq G1 D' r A B T) /\
  (forall G1 ,       Ctx G1 -> True).

Axiom respects_atoms_eq_mutual :
  (forall G r a A,     Typing  G r a A       -> True) /\
  (forall G r phi,     PropWff G r phi       -> True) /\
  (forall G D r p1 p2, Iso G D r p1 p2 -> forall D', D [=] D' -> Iso G D' r p1 p2) /\
  (forall G D r A B T,   DefEq G D r A B T  -> forall D', D [=] D' -> DefEq G D' r A B T) /\
  (forall G,           Ctx G           -> True).

Axiom remove_available_mutual:
  (forall G1 r a A,   Typing G1 r a A -> True) /\
  (forall G1 r phi,   PropWff G1 r phi -> True) /\
  (forall G1 D r p1 p2, Iso G1 D r p1 p2 ->
                   Iso G1 (AtomSetImpl.inter D (dom G1)) r p1 p2) /\
  (forall G1 D r A B T,   DefEq G1 D r A B T ->
                   DefEq G1 (AtomSetImpl.inter D (dom G1)) r A B T) /\
  (forall G1 ,       Ctx G1 -> True).

Axiom DefEq_weaken_available :
  forall G D r A B T, DefEq G D r A B T -> DefEq G (dom G) r A B T.

Axiom Iso_weaken_available :
  forall G D r A B, Iso G D r A B -> Iso G (dom G) r A B.

Axiom typing_weakening_mutual:
  (forall G0 r a A,   Typing G0 r a A ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> Typing (F ++ E ++ G) r a A) /\
  (forall G0 r phi,   PropWff G0 r phi ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> PropWff (F ++ E ++ G) r phi) /\
  (forall G0 D r p1 p2, Iso G0 D r p1 p2 ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> Iso (F ++ E ++ G) D r p1 p2) /\
  (forall G0 D r A B T,   DefEq G0 D r A B T ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> DefEq (F ++ E ++ G) D r A B T) /\
  (forall G0,       Ctx G0 ->
     forall E F G, (G0 = F ++ G) -> Ctx (F ++ E ++ G) -> Ctx (F ++ E ++ G)).


Definition Typing_weakening  := first  typing_weakening_mutual.
Definition PropWff_weakening := second typing_weakening_mutual.
Definition Iso_weakening     := third  typing_weakening_mutual.
Definition DefEq_weakening   := fourth typing_weakening_mutual.

Axiom SubG_mutual :
  (forall G0 r a A, Typing G0 r a A -> forall G2, SubG G0 G2 -> Typing G2 r a A) /\
  (forall G0 r phi,   PropWff G0 r phi -> forall G2, SubG G0 G2 -> PropWff G2 r phi) /\
  (forall G0 D r p1 p2, Iso G0 D r p1 p2 -> forall G2, SubG G0 G2 -> Iso G2 D r p1 p2) /\
  (forall G0 D r A B T,   DefEq G0 D r A B T -> forall G2, SubG G0 G2 -> DefEq G2 D r A B T) /\
  (forall G0, Ctx G0 -> forall G2, SubG G0 G2 -> Ctx G2).

Definition Typing_SubG := first SubG_mutual.
Definition PropWff_SubG := second SubG_mutual.
Definition Iso_SubG := third SubG_mutual.
Definition DefEq_SubG := fourth SubG_mutual.


Axiom SubRho_mutual :
  (forall G r a A, Typing G r a A -> forall r2, SubRho r2 r -> Typing G r2 a A) /\
  (forall G r phi,   PropWff G r phi -> forall r2, SubRho r2 r -> PropWff G r2 phi) /\
  (forall G D r p1 p2, Iso G D r p1 p2 -> forall r2, SubRho r2 r -> Iso G D r2 p1 p2) /\
  (forall G D r A B T,   DefEq G D r A B T -> forall r2, SubRho r2 r -> DefEq G D r2 A B T) /\
  (forall G, Ctx G -> True).

Definition Typing_SubRho := first SubRho_mutual.
Definition PropWff_SubRho := second SubRho_mutual.
Definition Iso_SubRho := third SubRho_mutual.
Definition DefEq_SubRho := fourth SubRho_mutual.

Axiom Typing_Irrel : forall G r a A, Typing G r a A -> Typing G Irrel a A.
Axiom PropWff_Irrel : forall G r phi, PropWff G r phi -> PropWff G Irrel phi.

End ext_weak_sig.


(**************** Ext Substitution ****************)

Module Type ext_subst_sig.
Include ext_weak_sig.

Axiom Ctx_strengthen : forall G1 G2, Ctx (G2 ++ G1) -> Ctx G1.

Axiom binds_to_PropWff: forall G0 A B T c,
    Ctx G0 ->
    binds c (Co (Eq A B T)) G0 -> PropWff G0 Irrel (Eq A B T).

Axiom tm_subst_tm_tm_dom_invariance: forall x a F,
    dom F = dom (map (tm_subst_tm_sort a x) F).

Axiom tm_subst_fresh_1 :
forall G r a A a0 x s,
  Typing G r a A -> Ctx ((x ~ s) ++ G) -> tm_subst_tm_tm a0 x A = A.

Axiom tm_subst_fresh_2 :
forall G r a A a0 x s,
  Typing G r a A -> Ctx ((x ~ s) ++ G) -> tm_subst_tm_tm a0 x a = a.

Axiom tm_subst_co_fresh_1 :
forall G r a A a0 c s,
  Typing G r a A -> Ctx ((c ~ s) ++ G) -> co_subst_co_tm a0 c A = A.


Axiom tm_substitution_mutual : 
  (forall G0 r b B (H : Typing G0 r b B),
      forall G r1 a A, Typing G r1 a A ->
               forall F x, G0 = (F ++ (x ~ Tm r1 A) ++ G) ->
                      Typing (map (tm_subst_tm_sort a x) F ++ G) r
                             (tm_subst_tm_tm a x b)
                             (tm_subst_tm_tm a x B)) /\
    (forall G0 r phi (H : PropWff G0 r phi),
        forall G r1 a A, Typing G r1 a A ->
                 forall F x, G0 = (F ++ (x ~ Tm r1 A) ++ G) ->
                        PropWff (map (tm_subst_tm_sort a x) F ++ G) r
                                (tm_subst_tm_constraint a x phi)) /\
    (forall G0 D r p1 p2 (H : Iso G0 D r p1 p2),
        forall G r1 a A, Typing G r1 a A ->
                 forall F x, G0 = (F ++ (x ~ Tm r1 A) ++ G) ->
                Iso (map (tm_subst_tm_sort a x) F ++ G) D r
                    (tm_subst_tm_constraint a x p1)
                    (tm_subst_tm_constraint a x p2)) /\
    (forall G0 D r A B T (H : DefEq G0 D r A B T),
       forall G r1 a A0, Typing G r1 a A0 ->
                 forall F x, G0 = (F ++ (x ~ Tm r1 A0) ++ G) ->
                        DefEq (map (tm_subst_tm_sort a x) F ++ G) D r
                              (tm_subst_tm_tm a x A)
                              (tm_subst_tm_tm a x B) (tm_subst_tm_tm a x T)) /\
    (forall G0 (H : Ctx G0),
        forall G r a A, Typing G r a A ->
                 forall F x, G0 = (F ++ (x ~ Tm r A) ++ G) ->
                        Ctx (map (tm_subst_tm_sort a x) F ++ G)).


Axiom Typing_tm_subst : forall G x r1 A r b B (H : Typing ((x ~ Tm r1 A) ++ G) r b B),
  forall a, Typing G r1 a A ->
       Typing G r (tm_subst_tm_tm a x b) (tm_subst_tm_tm a x B).

Axiom co_substitution_mutual :
    (forall G0 r b B (H : Typing G0 r b B),
        forall G D r A1 A2 T F c ,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T) ) ++ G)
          -> DefEq G D r A1 A2 T
          -> Typing (map (co_subst_co_sort g_Triv c) F ++ G) r (co_subst_co_tm g_Triv c b) (co_subst_co_tm g_Triv c B)) /\
    (forall G0 r phi (H : PropWff G0 r phi),
        forall G D A1 A2 T F c,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T) ) ++ G)
          -> DefEq G D r A1 A2 T
          -> PropWff (map (co_subst_co_sort g_Triv c) F ++ G) r (co_subst_co_constraint g_Triv c phi)) /\
    (forall G0 D0 r p1 p2 (H : Iso G0 D0 r p1 p2),
          forall G D r A1 A2 T F c,
            G0 = (F ++ (c ~ Co (Eq A1 A2 T) ) ++ G)
            -> DefEq G D r A1 A2 T
            -> Iso (map (co_subst_co_sort g_Triv c) F ++ G) (union D (remove c D0)) r
                    (co_subst_co_constraint g_Triv c p1)
                    (co_subst_co_constraint g_Triv c p2)) /\
    (forall G0 D0 r A B T (H : DefEq G0 D0 r A B T),
        forall G D r F c A1 A2 T1,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T1) ) ++ G)
          -> DefEq G D r A1 A2 T1
          -> DefEq (map (co_subst_co_sort g_Triv c) F ++ G) (union D (remove c D0)) r
                  (co_subst_co_tm g_Triv c A) (co_subst_co_tm g_Triv c B)
                  (co_subst_co_tm g_Triv c T)) /\
    (forall G0 (H : Ctx G0),
        forall G D r F c A1 A2 T,
          G0 = (F ++ (c ~ Co (Eq A1 A2 T) ) ++ G)
          -> DefEq G D r A1 A2 T
          -> Ctx (map (co_subst_co_sort g_Triv c) F ++ G)).


Axiom Typing_co_subst:
   forall G D r c a1 a2 A b B (H : Typing (c ~ (Co (Eq a1 a2 A)) ++ G) r b B),
     DefEq G D Irrel a1 a2 A ->
     Typing G r (co_subst_co_tm g_Triv c b) (co_subst_co_tm g_Triv c B).


Axiom Typing_swap : forall x1 x r r1 G a A B,
      x1 `notin` fv_tm_tm_tm a \u fv_tm_tm_tm B
    -> x `notin` dom G \u {{ x1 }}
    -> Typing ([(x1, Tm r1 A)] ++ G) r (open_tm_wrt_tm a (a_Var_f x1))
             (open_tm_wrt_tm B (a_Var_f x1))
    -> Typing ([(x, Tm r1 A)] ++ G) r (open_tm_wrt_tm a (a_Var_f x))
             (open_tm_wrt_tm B (a_Var_f x)).


Axiom E_Pi_exists : forall x (G : context) r1 (rho : relflag) (A B : tm),
      x `notin` dom G \u fv_tm_tm_tm B
      -> Typing ([(x, Tm Irrel A)] ++ G) r1 (open_tm_wrt_tm B (a_Var_f x)) a_Star
      -> Typing G r1 A a_Star
      -> Typing G r1 (a_Pi rho A B) a_Star.

Axiom E_Sigma_exists : forall x (G : context) r1 (rho : relflag) (A B : tm),
      x `notin` dom G \u fv_tm_tm_tm B
      -> Typing ([(x, Tm Irrel A)] ++ G) r1 (open_tm_wrt_tm B (a_Var_f x)) a_Star
      -> Typing G r1 A a_Star
      -> Typing G r1 (a_Sigma rho A B) a_Star.

Axiom E_Abs_exists :  forall x (G : context) r (rho : relflag) (a A B : tm),
    x `notin` fv_tm_tm_tm a \u fv_tm_tm_tm B
    -> Typing ([(x, Tm rho A)] ++ G) r (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x))
    -> Typing G Irrel A a_Star
    -> RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x))
    -> Typing G r (a_UAbs rho a) (a_Pi rho A B).

End ext_subst_sig.

(**************** Ext invert ****************)

Module Type ext_invert_sig.
  Include ext_subst_sig.

(* ---------- inversion lemmas ---------------- *)

Axiom binds_to_Typing: forall G r T A, Ctx G -> binds T (Tm r A) G -> Typing G Irrel A a_Star.

(*Axiom invert_a_Const : forall G T A,
    Typing G (a_Const T) A ->
    exists B, DataTy B a_Star /\ DefEq G (dom G) A B  a_Star
         /\ binds T (Cs B) toplevel.
*)
Axiom invert_a_Pi:
  forall G r1 rho A0 A B0,
    Typing G r1 (a_Pi rho A0 B0) A
    -> DefEq G (dom G) Irrel A a_Star a_Star
      /\ (exists L, forall x,
              x `notin` L
              -> Typing ([(x, Tm Irrel A0)] ++ G) r1 (open_tm_wrt_tm B0 (a_Var_f x)) a_Star)
      /\ Typing G r1 A0 a_Star.

Axiom invert_a_CPi: forall G r phi A B0,
    Typing G r (a_CPi phi B0) A ->
      DefEq G (dom G) Irrel A a_Star a_Star /\ (exists L, forall c, c `notin` L -> Typing ([(c, Co phi)] ++ G) r (open_tm_wrt_co B0 (g_Var_f c) ) a_Star) /\ PropWff G r phi.

Axiom invert_a_App_Rel : forall G r a b C,
    Typing G r (a_App a Rel b) C ->
    exists A B, Typing G r a (a_Pi Rel A B) /\
           Typing G r b A /\
           DefEq G (dom G) Irrel C (open_tm_wrt_tm B b) a_Star.

Axiom invert_a_App_Irrel : forall G r a b C,
    Typing G r (a_App a Irrel b) C ->
    exists A B b0, Typing G r a (a_Pi Irrel A B) /\
              Typing G Irrel b0 A /\
              DefEq G (dom G) Irrel C (open_tm_wrt_tm B b0) a_Star.

Axiom invert_a_CApp : forall G r a g A,
    Typing G r (a_CApp a g) A ->
    g = g_Triv /\
    exists a1 b1 A1 B, Typing G r a (a_CPi (Eq a1 b1 A1) B) /\
             DefEq G (dom G) r a1 b1 A1 /\
             DefEq G (dom G) Irrel A (open_tm_wrt_co B g_Triv) a_Star.

Axiom invert_a_UAbs:
  forall G r rho A b0,
    Typing G r (a_UAbs rho b0) A
    -> exists A1 B1, DefEq G (dom G) Irrel A (a_Pi rho A1 B1) a_Star
               /\ (exists L, forall x, x `notin` L ->
                            Typing ([(x, Tm rho A1)] ++ G) r
                                   (open_tm_wrt_tm b0 (a_Var_f x))
                                   (open_tm_wrt_tm B1 (a_Var_f x))
                            /\ Typing ([(x, Tm rho A1)] ++ G) Irrel
                                     (open_tm_wrt_tm B1 (a_Var_f x)) a_Star
                            /\ RhoCheck rho x (open_tm_wrt_tm b0 (a_Var_f x)))
               /\ Typing G Irrel A1 a_Star.

Axiom invert_a_UCAbs: forall G r A b0,
    Typing G r (a_UCAbs b0) A ->
    exists a b T B1, PropWff G r (Eq a b T)
                /\ DefEq G (dom G) Irrel A (a_CPi (Eq a b T) B1) a_Star /\
                (exists L, forall c, c `notin` L ->
                           Typing ([(c, Co (Eq a b T))] ++ G) r
                                  (open_tm_wrt_co b0 (g_Var_f c))
                                  (open_tm_wrt_co B1 (g_Var_f c)) /\
                           Typing ([(c, Co (Eq a b T))] ++ G) Irrel
                                  (open_tm_wrt_co B1 (g_Var_f c)) a_Star).

Axiom invert_a_Var :
  forall G r x A, Typing G r (a_Var_f x) A -> exists A', exists r1, binds x (Tm r1 A') G /\ DefEq G (dom G) Irrel A A' a_Star /\ SubRho r r1.

Axiom invert_a_Star: forall r A G, Typing G r a_Star A -> DefEq G (dom G) Irrel A a_Star a_Star.

Axiom invert_a_Const : forall G r F A,
    Typing G r (a_Const F) A ->
    exists a B, DefEq G (dom G) Irrel A B a_Star /\
           binds F (Ax a B) toplevel /\ Typing nil Irrel B a_Star.


(* ---------- context conversion -------------- *)
(* Terms still type check even after varying the context *)


Inductive context_DefEq : available_props -> context -> context -> Prop :=
| Nul_Eqcontext: forall D, context_DefEq D nil nil
| Factor_Eqcontext_tm: forall r G1 G2 D A A' x,
    context_DefEq D G1 G2 ->
    DefEq G1 D Irrel A A' a_Star ->
    DefEq G2 D Irrel A A' a_Star ->
    context_DefEq D ([(x, Tm r A)] ++ G1) ([(x, Tm r A')] ++ G2)
| Factor_Eqcontext_co: forall D G1 G2 r Phi1 Phi2 c,
    context_DefEq D G1 G2 ->
    Iso G1 D r Phi1 Phi2 ->
    Iso G2 D r Phi1 Phi2 ->
    context_DefEq D ([(c, Co Phi1)] ++ G1) ([(c, Co Phi2)] ++ G2).

Axiom refl_context_defeq: forall G D, Ctx G -> context_DefEq D G G.

Axiom context_DefEq_weaken_available :
  forall D G1 G2, context_DefEq D G1 G2 -> context_DefEq (dom G1) G1 G2.

Axiom context_DefEq_typing:
  (forall G1 r a A, Typing G1 r a A -> forall D G2, Ctx G2 -> context_DefEq D G1 G2 -> Typing G2 r a A).

(* ---------------- regularity lemmas ------------------- *)

Axiom Typing_regularity: forall r e A G, Typing G r e A -> Typing G Irrel A a_Star.

Axiom DefEq_regularity :
  forall G D r A B T, DefEq G D r A B T -> PropWff G Irrel (Eq A B T).

Axiom Iso_regularity :
  forall G D r phi1 phi2, Iso G D r phi1 phi2 -> PropWff G Irrel phi1 /\ PropWff G Irrel phi2.

Axiom PropWff_regularity :
  forall G r A B T, PropWff G r (Eq A B T) ->  Typing G r A T /\ Typing G r B T.


(* ------- smart constructors --------- *)

Axiom DefEq_conv : forall G D r a b A B, DefEq G D r a b A -> DefEq G (dom G) Irrel A B a_Star -> DefEq G D r a b B.

Axiom refl_iso: forall G D r phi, PropWff G r phi -> Iso G D r phi phi.

Axiom sym_iso: forall G D r phi1 phi2, Iso G D r phi1 phi2 -> Iso G D r phi2 phi1.

Axiom trans_iso : forall G D r phi1 phi2 phi3, Iso G D r phi1 phi2 -> Iso G D r phi2 phi3 -> Iso G D r phi1 phi3.

Axiom iso_cong : forall G D r A A' B B' T T', DefEq G D r A A' T -> DefEq G D r B B' T -> DefEq G D Irrel T T' a_Star ->
                     Iso G D r (Eq A B T) (Eq A' B' T').



Axiom E_PiCong2 :  ∀ (L : atoms) (G : context) (D : available_props) r rho (A1 B1 A2 B2 : tm),
    DefEq G D r A1 A2 a_Star
    → (∀ x : atom,
          x `notin` L
          → DefEq ([(x, Tm r A1)] ++ G) D r (open_tm_wrt_tm B1 (a_Var_f x))
                  (open_tm_wrt_tm B2 (a_Var_f x)) a_Star)
    → DefEq G D r (a_Pi rho A1 B1) (a_Pi rho A2 B2) a_Star.


Axiom E_CPiCong2  : ∀ (L : atoms) (G : context) (D : available_props) r (phi1 : constraint)
                      (A : tm) (phi2 : constraint) (B : tm),
    Iso G D r phi1 phi2
    → (∀ c : atom,
          c `notin` L
              → DefEq ([(c, Co phi1)] ++ G) D r (open_tm_wrt_co A (g_Var_f c))
                      (open_tm_wrt_co B (g_Var_f c)) a_Star)
    → DefEq G D r (a_CPi phi1 A) (a_CPi phi2 B) a_Star.

Axiom E_Pi2 : forall L G r rho A B,
    (∀ x : atom, x `notin` L → Typing ([(x, Tm r A)] ++ G) r (open_tm_wrt_tm B (a_Var_f x)) a_Star) ->
    Typing G r (a_Pi rho A B) a_Star.

Axiom E_Abs2 : ∀ (L : atoms) (G : context) r (rho : relflag) (a A B : tm),
    (∀ x : atom,
        x `notin` L → Typing ([(x, Tm rho A)] ++ G) r (open_tm_wrt_tm a (a_Var_f x)) (open_tm_wrt_tm B (a_Var_f x)))
    → (∀ x : atom, x `notin` L → RhoCheck rho x (open_tm_wrt_tm a (a_Var_f x)))
    → Typing G r (a_UAbs rho a) (a_Pi rho A B).

Axiom E_Conv2 : ∀ (G : context) r (a B A : tm),
    Typing G r a A → DefEq G (dom G) Irrel A B a_Star →
    Typing G r a B.

Axiom E_CPi2 :  ∀ (L : atoms) (G : context) r (phi : constraint) (B : tm),
    (∀ c : atom, c `notin` L → Typing ([(c, Co phi)] ++ G) r (open_tm_wrt_co B (g_Var_f c)) a_Star) ->
    Typing G r (a_CPi phi B) a_Star.

Axiom E_CAbs2 : ∀ (L : atoms) (G : context) r (a : tm) (phi : constraint) (B : tm),
       (∀ c : atom,
        c `notin` L → Typing ([(c, Co phi)] ++ G) r (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co B (g_Var_f c)))
       → Typing G r (a_UCAbs a) (a_CPi phi B).

Axiom E_AbsCong2
     : ∀ (L : atoms) (G : context) (D : available_props) r (rho : relflag) (b1 b2 A1 B : tm),
       (∀ x : atom,
        x `notin` L
        → DefEq ([(x, Tm rho A1)] ++ G) D r (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x))
            (open_tm_wrt_tm B (a_Var_f x)))
       → (∀ x : atom, x `notin` L → RhoCheck rho x (open_tm_wrt_tm b1 (a_Var_f x)))
       → (∀ x : atom, x `notin` L → RhoCheck rho x (open_tm_wrt_tm b2 (a_Var_f x)))
       → DefEq G D r (a_UAbs rho b1) (a_UAbs rho b2) (a_Pi rho A1 B).

Axiom E_CAbsCong2
     : ∀ (L : atoms) (G : context) (D : available_props) r (a b : tm) (phi1 : constraint)
       (B : tm),
       (∀ c : atom,
        c `notin` L
        → DefEq ([(c, Co phi1)] ++ G) D r (open_tm_wrt_co a (g_Var_f c)) (open_tm_wrt_co b (g_Var_f c))
                (open_tm_wrt_co B (g_Var_f c))) → DefEq G D r (a_UCAbs a) (a_UCAbs b) (a_CPi phi1 B).

End ext_invert_sig.

(**************** FC Wf ****************)

Module Type fc_wf_sig.


Axiom AnnTyping_AnnCtx  : forall G0 a A, AnnTyping G0 a A -> AnnCtx G0.
Axiom AnnPropWff_AnnCtx : forall G0 phi, AnnPropWff G0 phi -> AnnCtx G0.
Axiom AnnIso_AnnCtx     : forall G0 D g p1 p2, AnnIso G0 D g p1 p2 -> AnnCtx G0.
Axiom AnnDefEq_AnnCtx   : forall G0 D g A B,   AnnDefEq G0 D g A B -> AnnCtx G0.

Axiom AnnCtx_uniq : forall G, AnnCtx G -> uniq G.


Axiom AnnTyping_lc  :  forall G0 a A, AnnTyping G0 a A -> lc_tm a /\ lc_tm A.
Axiom AnnPropWff_lc : forall G0 phi, AnnPropWff G0 phi -> lc_constraint phi.
Axiom AnnIso_lc :  forall G0 D g p1 p2, AnnIso G0 D g p1 p2 -> lc_constraint p1 /\ lc_constraint p2 /\ lc_co g.
Axiom AnnDefEq_lc : forall G0 D g A B,  AnnDefEq G0 D g A B -> lc_tm A /\ lc_tm B /\ lc_co g.
Axiom AnnCtx_lc : forall G0, AnnCtx G0 -> forall x s , binds x s G0 -> lc_sort s.

Axiom AnnTyping_lc1 : forall G a A, AnnTyping G a A -> lc_tm a.
Axiom AnnTyping_lc2 : forall G a A, AnnTyping G a A -> lc_tm A.
Axiom AnnIso_lc1 : forall G D g p1 p2, AnnIso G D g p1 p2 -> lc_constraint p1.
Axiom AnnIso_lc2 : forall G D g p1 p2, AnnIso G D g p1 p2 -> lc_constraint p2.
Axiom AnnIso_lc3 : forall G D g p1 p2, AnnIso G D g p1 p2 -> lc_co g.
Axiom AnnDefEq_lc1 : forall G D g A B,  AnnDefEq G D g A B -> lc_tm A.
Axiom AnnDefEq_lc2 : forall G D g A B,  AnnDefEq G D g A B -> lc_tm B.
Axiom AnnDefEq_lc3 : forall G D g A B,  AnnDefEq G D g A B -> lc_co g.

Axiom AnnToplevel_lc : forall c s, binds c s an_toplevel -> lc_sig_sort s.

End fc_wf_sig.


(**************** FC Weakening ****************)

Module Type fc_weak_sig.

Axiom ann_respects_atoms_eq_mutual :
  (forall G a A,       AnnTyping  G a A       -> True) /\
  (forall G phi,       AnnPropWff G phi       -> True) /\
  (forall G D g p1 p2, AnnIso     G D g p1 p2 -> forall D', D [=] D' -> AnnIso   G D' g p1 p2) /\
  (forall G D g A B,   AnnDefEq   G D g A B   -> forall D', D [=] D' -> AnnDefEq G D' g A B) /\
  (forall G,           AnnCtx     G           -> True).

Definition AnnIso_respects_atoms_eq   := third  ann_respects_atoms_eq_mutual.
Definition AnnDefEq_respects_atoms_eq := fourth ann_respects_atoms_eq_mutual.

Axiom ann_strengthen_noncovar:
  (forall G1  a A,   AnnTyping G1 a A -> True) /\
  (forall G1  phi,   AnnPropWff G1 phi -> True) /\
  (forall G1 D g p1 p2, AnnIso G1 D g p1 p2 -> forall x, not (exists phi, binds x (Co phi) G1) ->
                     AnnIso G1 (remove x D) g p1 p2) /\
  (forall G1 D g A B,   AnnDefEq G1 D g A B ->  forall x, not (exists phi, binds x (Co phi) G1) ->
                    AnnDefEq G1 (remove x D) g A B) /\
  (forall G1 ,       AnnCtx G1 -> True).

Axiom AnnDefEq_strengthen_available_tm :
  forall G D g A B, AnnDefEq G D g A B ->  forall x r A', binds x (Tm r A') G ->
                    forall D', D' [=] remove x D ->
                    AnnDefEq G D' g A B.

Axiom ann_weaken_available_mutual:
  (forall G1  a A,   AnnTyping G1 a A -> True) /\
  (forall G1  phi,   AnnPropWff G1 phi -> True) /\
  (forall G1 D g p1 p2, AnnIso G1 D g p1 p2 -> forall D', D [<=] D' -> AnnIso G1 D' g p1 p2) /\
  (forall G1 D g A B,   AnnDefEq G1 D g A B -> forall D', D [<=] D' -> AnnDefEq G1 D' g A B) /\
  (forall G1 ,       AnnCtx G1 -> True).

Axiom ann_remove_available_mutual:
  (forall G1  a A,   AnnTyping G1 a A -> True) /\
  (forall G1  phi,   AnnPropWff G1 phi -> True) /\
  (forall G1 D g p1 p2, AnnIso G1 D g p1 p2 ->
                   AnnIso G1 (AtomSetImpl.inter D (dom G1)) g p1 p2) /\
  (forall G1 D g A B,   AnnDefEq G1 D g A B ->
                   AnnDefEq G1 (AtomSetImpl.inter D (dom G1)) g A B) /\
  (forall G1 ,       AnnCtx G1 -> True).

Axiom AnnDefEq_weaken_available :
  forall G D g A B, AnnDefEq G D g A B -> AnnDefEq G (dom G) g A B.

Axiom AnnIso_weaken_available :
  forall G D g A B, AnnIso G D g A B -> AnnIso G (dom G) g A B.


Axiom ann_typing_weakening_mutual:
  (forall G0 a A,       AnnTyping  G0 a A       ->
     forall E F G, (G0 = F ++ G) -> AnnCtx (F ++ E ++ G) -> AnnTyping (F ++ E ++ G) a A) /\
  (forall G0 phi,       AnnPropWff G0 phi       ->
     forall E F G, (G0 = F ++ G) ->
        AnnCtx (F ++ E ++ G) -> AnnPropWff (F ++ E ++ G) phi) /\
  (forall G0 D g p1 p2, AnnIso     G0 D g p1 p2 ->
     forall E F G, (G0 = F ++ G) ->
        AnnCtx (F ++ E ++ G) -> AnnIso (F ++ E ++ G) D g p1 p2) /\
  (forall G0 D g A B,   AnnDefEq   G0 D g A B   ->
     forall E F G, (G0 = F ++ G) ->
        AnnCtx (F ++ E ++ G) -> AnnDefEq (F ++ E ++ G) D g A B) /\
  (forall G0,           AnnCtx     G0           ->
     forall E F G, (G0 = F ++ G) ->
        AnnCtx (F ++ E ++ G) -> AnnCtx (F ++ E ++ G)).


Definition AnnTyping_weakening  := first  ann_typing_weakening_mutual.
Definition AnnPropWff_weakening := second ann_typing_weakening_mutual.
Definition AnnIso_weakening     := third  ann_typing_weakening_mutual.
Definition AnnDefEq_weakening   := fourth ann_typing_weakening_mutual.
Definition AnnCtx_weakening     := fifth  ann_typing_weakening_mutual.

End fc_weak_sig.




(**************** FC Substitution ****************)
Module Type fc_subst_sig.

  (*
  Axiom context_fv_mutual :
  (forall G (a : tm) A (H: AnnTyping G a A),
      fv_tm_tm_tm a [<=] dom G /\ fv_co_co_tm a [<=] dom G /\
      fv_tm_tm_tm A [<=] dom G /\ fv_co_co_tm A [<=] dom G)
  /\
  (forall G phi (H : AnnPropWff G phi),
      fv_tm_tm_constraint phi [<=] dom G /\ fv_co_co_constraint phi [<=] dom G)
  /\
  (forall G D g p1 p2 (H : AnnIso G D g p1 p2),
      fv_tm_tm_co         g  [<=] dom G /\ fv_co_co_co         g  [<=] dom G /\
      fv_tm_tm_constraint p1 [<=] dom G /\ fv_co_co_constraint p1 [<=] dom G /\
      fv_tm_tm_constraint p2 [<=] dom G /\ fv_co_co_constraint p2 [<=] dom G)
  /\
  (forall G D g A B (H : AnnDefEq G D g A B),
      fv_tm_tm_co g [<=] dom G /\ fv_co_co_co g [<=] dom G /\
      fv_tm_tm_tm A [<=] dom G /\ fv_co_co_tm A [<=] dom G /\
      fv_tm_tm_tm B [<=] dom G /\ fv_co_co_tm B [<=] dom G)
  /\
  (forall G (H : AnnCtx G),
      (forall x A,
          binds x (Tm A)   G ->
          fv_tm_tm_tm         A   [<=] dom G /\ fv_co_co_tm         A   [<=] dom G) /\
      (forall c phi,
          binds c (Co phi) G ->
          fv_tm_tm_constraint phi [<=] dom G /\ fv_co_co_constraint phi [<=] dom G)).

  Definition AnnTyping_context_fv  := @first  _ _ _ _ _ context_fv_mutual.
  Definition AnnPropWff_context_fv := @second _ _ _ _ _ context_fv_mutual.
  Definition AnnIso_context_fv     := @third  _ _ _ _ _ context_fv_mutual.
  Definition AnnDefEq_context_fv   := @fourth _ _ _ _ _ context_fv_mutual.
  Definition AnnCtx_context_fv     := @fifth  _ _ _ _ _ context_fv_mutual.
*)

  Axiom AnnCtx_strengthen : forall G1 G2, AnnCtx (G2 ++ G1) -> AnnCtx G1.

  Axiom binds_to_AnnTyping :
    forall G x r A, AnnCtx G -> binds x (Tm r A) G -> AnnTyping G A a_Star.

  Axiom binds_to_AnnPropWff: forall G0 a b A c,
      AnnCtx G0 -> binds c (Co (Eq a b A)) G0 -> AnnPropWff G0 (Eq a b A).

  Axiom tm_subst_fresh_1 :
  forall G a A a0 x s,
    AnnTyping G a A -> AnnCtx ((x ~ s) ++ G) -> tm_subst_tm_tm a0 x A = A.

  Axiom tm_subst_fresh_2 :
  forall G a A a0 x s,
    AnnTyping G a A -> AnnCtx ((x ~ s) ++ G) -> tm_subst_tm_tm a0 x a = a.

  Axiom ann_tm_substitution_mutual :
  (forall G0 b B (H : AnnTyping G0 b B),
      forall G a A, AnnTyping G a A ->
               forall F x r, G0 = (F ++ (x ~ Tm r A) ++ G) ->
                      AnnTyping (map (tm_subst_tm_sort a x) F ++ G)
                                (tm_subst_tm_tm a x b)
                                (tm_subst_tm_tm a x B)) /\
  (forall G0 phi (H : AnnPropWff G0 phi),
      forall G a A, AnnTyping G a A ->
               forall F x r, G0 = (F ++ (x ~ Tm r A) ++ G) ->
                      AnnPropWff (map (tm_subst_tm_sort a x) F ++ G)
                                 (tm_subst_tm_constraint a x phi)) /\
  (forall G0 D g p1 p2 (H : AnnIso G0 D g p1 p2),
      forall G a A, AnnTyping G a A ->
               forall F x r, G0 = (F ++ (x ~ Tm r A) ++ G) ->
                      AnnIso (map (tm_subst_tm_sort a x) F ++ G)
                             D
                             (tm_subst_tm_co a x g)
                             (tm_subst_tm_constraint a x p1)
                             (tm_subst_tm_constraint a x p2)) /\
  (forall  G0 D g A B (H : AnnDefEq G0 D g A B),
      forall G a A0, AnnTyping G a A0 ->
                forall F x r, G0 = (F ++ (x ~ Tm r A0) ++ G) ->
                       AnnDefEq (map (tm_subst_tm_sort a x) F ++ G)
                                D
                                (tm_subst_tm_co a x g)
                                (tm_subst_tm_tm a x A)
                                (tm_subst_tm_tm a x B)) /\
  (forall G0 (H : AnnCtx G0),
  forall G a A, AnnTyping G a A ->
  forall F x r, G0 = (F ++ (x ~ Tm r A) ++ G) ->
                AnnCtx (map (tm_subst_tm_sort a x) F ++ G)).



  Axiom AnnTyping_tm_subst : forall G r x A b B (H : AnnTyping ((x ~ Tm r A) ++ G) b B),
    forall a, AnnTyping G a A ->
         AnnTyping G (tm_subst_tm_tm a x b) (tm_subst_tm_tm a x B).

  Axiom AnnTyping_tm_subst_nondep : forall L G r a A b B,
      AnnTyping G a A ->
      (forall x, x `notin` L -> AnnTyping ([(x,Tm r A)] ++ G) (open_tm_wrt_tm b (a_Var_f x)) B) ->
      AnnTyping G (open_tm_wrt_tm b a) B.

  Axiom AnnTyping_co_subst : forall G x A1 A2 A3 b B
                               (H : AnnTyping ((x ~ Co (Eq A1 A2 A3)) ++ G) b B),
    forall D a, AnnDefEq G D a A1 A2 ->
         AnnTyping G (co_subst_co_tm a x b) (co_subst_co_tm a x B).

  Axiom AnnTyping_co_subst_nondep : forall L G D g A1 A2 A3 b B,
      AnnDefEq G D g A1 A2 ->
      (forall x, x `notin` L -> AnnTyping ([(x,Co (Eq A1 A2 A3))] ++ G) (open_tm_wrt_co b (g_Var_f x)) B) ->
      AnnTyping G (open_tm_wrt_co b g) B.



  (* -----  exists forms of the binding constructors ----------- *)

  Axiom An_Pi_exists : forall x G r rho A B,
      x `notin` dom G \u fv_tm_tm_tm B
    → AnnTyping ([(x, Tm r A)] ++ G)
                (open_tm_wrt_tm B (a_Var_f x)) a_Star
    → AnnTyping G A a_Star
    → AnnTyping G (a_Pi rho A B) a_Star.

  Axiom An_Abs_exists :   forall x (G:context) r rho (A a B:tm),
       x \notin dom G \u fv_tm_tm_tm a \u fv_tm_tm_tm B ->
       AnnTyping G A a_Star ->
       AnnTyping  (( x ~ Tm r A) ++ G) (open_tm_wrt_tm a (a_Var_f x))
                  (open_tm_wrt_tm B (a_Var_f x))  ->
       RhoCheck rho x (erase_tm (open_tm_wrt_tm a (a_Var_f x))) ->
        AnnTyping G (a_Abs rho A a) (a_Pi rho A B).

  Axiom An_CPi_exists :  ∀ c (G : context) (phi : constraint) (B : tm),
          c \notin dom G \u fv_co_co_tm B ->
         AnnPropWff G phi
         → AnnTyping ([(c, Co phi)] ++ G) (open_tm_wrt_co B (g_Var_f c)) a_Star
         → AnnTyping G (a_CPi phi B) a_Star.

  Axiom An_CAbs_exists :  ∀ c (G : context) (phi : constraint) (a B : tm),
      c \notin dom G \u fv_co_co_tm a \u fv_co_co_tm B ->
         AnnPropWff G phi
         → AnnTyping ([(c, Co phi)] ++ G) (open_tm_wrt_co a (g_Var_f c))
                (open_tm_wrt_co B (g_Var_f c))
         → AnnTyping G (a_CAbs phi a) (a_CPi phi B).

  Axiom An_CAbs_inversion : ∀ (G : context) (phi : constraint) (a A : tm),
    AnnTyping G (a_CAbs phi a) A ->
      exists B, A = (a_CPi phi B) /\
      forall c, c  `notin` dom G (* \u fv_co_co_tm a \u fv_co_co_tm B *) ->
        AnnPropWff G phi /\
        AnnTyping ([(c, Co phi)] ++ G) (open_tm_wrt_co a (g_Var_f c))
                  (open_tm_wrt_co B (g_Var_f c)).

  Axiom An_AbsCong_exists : ∀ x1 x2 (G : context) D rho (g1 g2 : co) (A1 b1 A2 b3 b2 B : tm),
      x1 `notin` (dom G \u fv_tm_tm_tm b1 \u fv_tm_tm_tm b2 \u  fv_tm_tm_co g2)
      -> x2 `notin` (dom G \u fv_tm_tm_tm b2 \u fv_tm_tm_tm b3 \u  fv_tm_tm_co g1)
      ->  AnnDefEq G D g1 A1 A2
      → (AnnDefEq ([(x1, Tm rho A1)] ++ G) D  (open_co_wrt_tm g2 (a_Var_f x1))
                  (open_tm_wrt_tm b1 (a_Var_f x1)) (open_tm_wrt_tm b2 (a_Var_f x1)))
      → (open_tm_wrt_tm b3 (a_Var_f x2) =
         open_tm_wrt_tm b2 (a_Conv (a_Var_f x2) (g_Sym g1)))
      → AnnTyping G A1 a_Star
      → AnnTyping G A2 a_Star
      → RhoCheck rho x1 (erase_tm (open_tm_wrt_tm b1 (a_Var_f x1)))
      → RhoCheck rho x2 (erase_tm (open_tm_wrt_tm b3 (a_Var_f x2)))
      → AnnTyping G (a_Abs rho A1 b2) B
      → AnnDefEq G D (g_AbsCong rho g1 g2) (a_Abs rho A1 b1) (a_Abs rho A2 b3).

  Axiom An_AbsCong_inversion :
    forall G D rho g1 g2 B1 B2,
      AnnDefEq G D (g_AbsCong rho g1 g2) B1 B2 ->
    exists A1 A2 b1 b2 b3 B,
      B1 = (a_Abs rho A1 b1) /\
      B2 = (a_Abs rho A2 b3) /\
      AnnTyping G A1 a_Star  /\
      AnnTyping G A2 a_Star  /\
      AnnDefEq G D g1 A1 A2  /\
      AnnTyping G (a_Abs rho A1 b2) B /\
      (forall x, x \notin dom G  (* \u fv_tm_tm_tm b1 \u fv_tm_tm_tm b2 \u fv_tm_tm_tm b3 *) ->
          AnnDefEq  (( x ~ Tm rho A1) ++  G) D (open_co_wrt_tm g2 (a_Var_f x)) (open_tm_wrt_tm b1 (a_Var_f x))  ((open_tm_wrt_tm b2 (a_Var_f x))) /\
          (open_tm_wrt_tm b3 (a_Var_f x)) = (open_tm_wrt_tm b2 (a_Conv (a_Var_f x) (g_Sym g1))) /\
          (RhoCheck rho x  (erase_tm (open_tm_wrt_tm b1 (a_Var_f x)))) /\
          (RhoCheck rho x  (erase_tm (open_tm_wrt_tm b3 (a_Var_f x))))).

  Axiom An_CPiCong_exists : ∀ c1 c2 (G : context) D (g1 g3 : co) (phi1 : constraint)
       (B1 : tm) (phi2 : constraint) (B3 B2 : tm),
    AnnIso G D  g1 phi1 phi2
    -> c1 `notin` D \u fv_co_co_tm B2 \u fv_co_co_tm B1 \u fv_co_co_co g3
    -> c2 `notin` fv_co_co_co g1 \u fv_co_co_tm B2 \u fv_co_co_tm B3
    → (AnnDefEq ([(c1, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c1))
                (open_tm_wrt_co B1 (g_Var_f c1)) (open_tm_wrt_co B2 (g_Var_f c1)))
    → (open_tm_wrt_co B3 (g_Var_f c2) =
       open_tm_wrt_co B2 (g_Cast (g_Var_f c2) (g_Sym g1)))
    → AnnTyping G (a_CPi phi1 B1) a_Star
    → AnnTyping G (a_CPi phi2 B3) a_Star
    -> AnnTyping G (a_CPi phi1 B2) a_Star
    → AnnDefEq G D (g_CPiCong g1 g3) (a_CPi phi1 B1)
               (a_CPi phi2 B3).


  Axiom An_CPiCong_inversion :  ∀ (G : context) D (g1 g3 : co) (A1 A2 : tm),
    AnnDefEq G D (g_CPiCong g1 g3) A1 A2 ->
      exists phi1 phi2 B1 B2 B3,
        A1 = (a_CPi phi1 B1) /\
        A2 = (a_CPi phi2 B3) /\
        AnnIso G D g1 phi1 phi2 /\
        AnnTyping G (a_CPi phi1 B1) a_Star /\
        AnnTyping G (a_CPi phi2 B3) a_Star /\
        AnnTyping G (a_CPi phi1 B2) a_Star /\
        (forall c, c `notin` dom G (* \u D \u fv_co_co_tm B2 \u fv_co_co_tm B1
             \u fv_co_co_co g3 \u
                fv_co_co_co g1 \u fv_co_co_tm B3 *) →
          (AnnDefEq ([(c, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c))
          (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B2 (g_Var_f c))) /\
          (open_tm_wrt_co B3 (g_Var_f c) = open_tm_wrt_co B2 (g_Cast (g_Var_f c) (g_Sym g1)))).

  Axiom An_PiCong_exists : forall x1 x2 (G:context) D r rho
                             (g1 g2 : co) (A1 B1 A2 B3 B2 : tm),
      x1 `notin` (dom G \u fv_tm_tm_tm B1 \u fv_tm_tm_tm B2 \u  fv_tm_tm_co g2)
      -> x2 `notin` (dom G \u fv_tm_tm_tm B2 \u fv_tm_tm_tm B3 \u  fv_tm_tm_co g1)
      ->  AnnDefEq G D g1 A1 A2
      → AnnDefEq ([(x1, Tm r A1)] ++ G) D (open_co_wrt_tm g2 (a_Var_f x1))
                 (open_tm_wrt_tm B1 (a_Var_f x1)) (open_tm_wrt_tm B2 (a_Var_f x1))
      → (open_tm_wrt_tm B3 (a_Var_f x2) =
         open_tm_wrt_tm B2 (a_Conv (a_Var_f x2) (g_Sym g1)))
      → AnnTyping G (a_Pi rho A1 B1) a_Star
      → AnnTyping G (a_Pi rho A2 B3) a_Star
      → AnnTyping G (a_Pi rho A1 B2) a_Star
      → AnnDefEq G D (g_PiCong rho g1 g2) (a_Pi rho A1 B1) (a_Pi rho A2 B3).

  Axiom An_PiCong_inversion : forall (G:context) (D:available_props) r (rho:relflag) (g1 g2:co) (C1 C2 :tm),
    AnnDefEq G D (g_PiCong rho g1 g2) C1 C2 ->
      exists A1 B1 A2 B2 B3,
      C1 = (a_Pi rho A1 B1) /\
      C2 = (a_Pi rho A2 B3) /\
      AnnTyping G (a_Pi rho A1 B1) a_Star /\
      AnnTyping G (a_Pi rho A2 B3) a_Star /\
      AnnTyping G (a_Pi rho A1 B2) a_Star /\
      AnnDefEq G D g1 A1 A2 /\
      (forall x , x \notin dom G  ->
            AnnDefEq  ((x ~ Tm r A1) ++ G) D (open_co_wrt_tm g2 (a_Var_f x)) (open_tm_wrt_tm B1 (a_Var_f x)) ((open_tm_wrt_tm B2 (a_Var_f x)))  /\
            (open_tm_wrt_tm B3 (a_Var_f x)  = (open_tm_wrt_tm  B2 (a_Conv (a_Var_f x) (g_Sym g1))))).

  Axiom An_CAbsCong_exists :
  forall c1 c2 (G : context) (D : available_props) (g1 g3 g4 : co)
    (phi1 : constraint) (a1 : tm) (phi2 : constraint) (a3 a2 B1 B2 B: tm),
    AnnIso G D g1 phi1 phi2
    -> c1 `notin` D \u fv_co_co_tm a2 \u fv_co_co_tm a1 \u fv_co_co_co g3
    -> c2 `notin` fv_co_co_co g1 \u fv_co_co_tm a2 \u fv_co_co_tm a3
    → (AnnDefEq ([(c1, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c1))
                (open_tm_wrt_co a1 (g_Var_f c1)) (open_tm_wrt_co a2 (g_Var_f c1)))
    → (open_tm_wrt_co a3 (g_Var_f c2) =
       open_tm_wrt_co a2 (g_Cast (g_Var_f c2) (g_Sym g1)))
    → AnnTyping G (a_CAbs phi1 a1) (a_CPi phi1 B1)
    → AnnTyping G (a_CAbs phi2 a3) (a_CPi phi2 B2)
    → AnnDefEq G (dom G) g4 (a_CPi phi1 B1) (a_CPi phi2 B2)
    -> AnnTyping G (a_CAbs phi1 a2) B
    → AnnDefEq G D (g_CAbsCong g1 g3 g4) (a_CAbs phi1 a1) (a_CAbs phi2 a3).

  Axiom An_CAbsCong_inversion :
  forall (G : context) (D : available_props) (g1 g3 g4 : co) A1 A2,
    AnnDefEq G D (g_CAbsCong g1 g3 g4) A1 A2
    -> exists phi1 phi2 a1 a2 a3 B1 B2 B,
      A1 = (a_CAbs phi1 a1) /\
      A2 = (a_CAbs phi2 a3) /\
      AnnIso G D g1 phi1 phi2 /\
      AnnTyping G (a_CAbs phi1 a1) (a_CPi phi1 B1) /\
      AnnTyping G (a_CAbs phi2 a3) (a_CPi phi2 B2) /\
      AnnTyping G (a_CAbs phi1 a2) B /\
      AnnDefEq G (dom G) g4 (a_CPi phi1 B1) (a_CPi phi2 B2) /\
 forall c1,
      c1`notin` dom G (* \u D \u fv_co_co_tm a2 \u fv_co_co_tm a1 \u fv_co_co_co g3
                  \u fv_co_co_co g1 \u fv_co_co_tm a3 *)
    → (AnnDefEq ([(c1, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c1))
                (open_tm_wrt_co a1 (g_Var_f c1)) (open_tm_wrt_co a2 (g_Var_f c1))) /\
      (open_tm_wrt_co a3 (g_Var_f c1) =
       open_tm_wrt_co a2 (g_Cast (g_Var_f c1) (g_Sym g1))).

  (* -----  inversion lemmas for some typing judgments (with maximal co-finite quantification) ----------- *)

  Axiom An_Pi_inversion :
    ∀ (G:context) r rho A B T,
      AnnTyping G (a_Pi rho A B) T ->
      T = a_Star /\
      AnnTyping G A a_Star /\
      ∀ x, x \notin dom G -> AnnTyping (( x ~ Tm r A) ++ G) (open_tm_wrt_tm B (a_Var_f x)) a_Star.

  Axiom An_Abs_inversion :
    ∀ (G:context) r rho (a:tm) A A1,
    AnnTyping G (a_Abs rho A a) A1 ->
    (exists B, A1 = a_Pi rho A B /\
    AnnTyping G A a_Star /\
    ∀ x, x \notin dom G ->
      RhoCheck rho x (erase_tm (open_tm_wrt_tm a (a_Var_f x))) /\
      AnnTyping (( x ~ Tm r A) ++ G)
                (open_tm_wrt_tm a (a_Var_f x))
                (open_tm_wrt_tm B (a_Var_f x))).

  Axiom An_CPi_inversion :
    ∀ (G:context) (phi : constraint) (B T : tm),
      AnnTyping G (a_CPi phi B) T ->
      T = a_Star /\
      AnnPropWff G phi /\
      ∀ c, c \notin dom G -> AnnTyping ([(c, Co phi)] ++ G) (open_tm_wrt_co B (g_Var_f c)) a_Star.

  (* -------------- name swapping ------------------------ *)

  Axiom AnnTyping_tm_swap : forall c c0 r B G a A,
    c `notin` fv_tm_tm_tm A ->
    c `notin` fv_tm_tm_tm a ->
    c0 `notin` dom G \u {{ c }} ->
    AnnTyping ([(c, Tm r B)] ++ G) (open_tm_wrt_tm a (a_Var_f c))
         (open_tm_wrt_tm A (a_Var_f c)) ->
    AnnTyping ([(c0, Tm r B)] ++ G) (open_tm_wrt_tm a (a_Var_f c0))
                  (open_tm_wrt_tm A (a_Var_f c0)).

  Axiom AnnDefEq_tm_swap : forall x1 x r G A1 D g2 b1 b2,
   x1 `notin` fv_tm_tm_co g2 \u fv_tm_tm_tm b1 \u fv_tm_tm_tm b2
  -> x `notin` dom G \u {{ x1 }}
  -> AnnDefEq ([(x1, Tm r A1)] ++ G) D  (open_co_wrt_tm g2 (a_Var_f x1))
             (open_tm_wrt_tm b1 (a_Var_f x1)) (open_tm_wrt_tm b2 (a_Var_f x1))
  -> AnnDefEq ([(x, Tm r A1)] ++ G) D  (open_co_wrt_tm g2 (a_Var_f x))
             (open_tm_wrt_tm b1 (a_Var_f x)) (open_tm_wrt_tm b2 (a_Var_f x)).


 Axiom AnnTyping_co_swap : forall c c0 phi G a A,
    c `notin` fv_co_co_tm A ->
    c `notin` fv_co_co_tm a ->
    c0 `notin` dom G \u {{ c }} ->
    AnnTyping ([(c, Co phi)] ++ G) (open_tm_wrt_co a (g_Var_f c))
         (open_tm_wrt_co A (g_Var_f c)) ->
    AnnTyping ([(c0, Co phi)] ++ G) (open_tm_wrt_co a (g_Var_f c0))
                  (open_tm_wrt_co A (g_Var_f c0)).

  Axiom AnnDefEq_co_swap : forall c1 c phi1 G D g3 B1 B2,
    c1 `notin` D \u fv_co_co_tm B1 \u fv_co_co_tm B2 \u fv_co_co_co g3 ->
    c `notin` dom G \u {{ c1 }} ->
    (AnnDefEq ([(c1, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c1))
              (open_tm_wrt_co B1 (g_Var_f c1)) (open_tm_wrt_co B2 (g_Var_f c1)))
    -> (AnnDefEq ([(c, Co phi1)] ++ G) D (open_co_wrt_co g3 (g_Var_f c))
              (open_tm_wrt_co B1 (g_Var_f c)) (open_tm_wrt_co B2 (g_Var_f c))).

  Create HintDb smart_cons_exists discriminated.
  Hint Resolve An_Pi_exists An_Abs_exists An_CPi_exists An_CAbs_exists An_AbsCong_exists An_CPiCong_exists An_CAbsCong_exists : smart_cons_exists.


End fc_subst_sig.




(**************** FC Uniqueness ****************)
Module Type fc_unique_sig.

Axiom AnnTyping_unique :
    forall G a A1, AnnTyping G a A1 -> forall {A2}, AnnTyping G a A2 -> A1 = A2.
Axiom AnnIso_unique  :
  forall G D g p1 p2, AnnIso G D g p1 p2 ->
                 forall {q1 q2}, AnnIso G D g q1 q2 -> p1 = q1 /\ p2 = q2.
Axiom AnnDefEq_unique    :
  forall G D g a b,
      AnnDefEq G D g a b -> forall {a1 b1}, AnnDefEq G D g a1 b1 -> a = a1 /\ b = b1.

End fc_unique_sig.