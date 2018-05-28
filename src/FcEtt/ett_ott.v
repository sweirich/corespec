Require Import Metalib.Metatheory.
(** syntax *)
Definition tmvar := var. (*r variables *)
Definition covar := var. (*r coercion variables *)
Definition datacon := atom.
Definition const := atom.
Definition index := nat. (*r indices *)

Inductive relflag : Set :=  (*r relevance flag *)
 | Rel : relflag
 | Irrel : relflag.

Inductive role : Set :=  (*r Role *)
 | Nom : role
 | Rep : role.

Inductive appflag : Set :=  (*r applicative flag *)
 | Role (R:role)
 | Rho (rho:relflag).

Inductive constraint : Set :=  (*r props *)
 | Eq (a:tm) (b:tm) (A:tm) (R:role)
with tm : Set :=  (*r types and kinds *)
 | a_Star : tm
 | a_Var_b (_:nat)
 | a_Var_f (x:tmvar)
 | a_Abs (rho:relflag) (A:tm) (b:tm)
 | a_UAbs (rho:relflag) (b:tm)
 | a_App (a:tm) (nu:appflag) (b:tm)
 | a_Pi (rho:relflag) (A:tm) (B:tm)
 | a_CAbs (phi:constraint) (b:tm)
 | a_UCAbs (b:tm)
 | a_CApp (a:tm) (g:co)
 | a_CPi (phi:constraint) (B:tm)
 | a_Conv (a:tm) (R:role) (g:co)
 | a_Fam (F:const)
 | a_Bullet : tm
 | a_Pattern (R:role) (a:tm) (F:const) (b1:tm) (b2:tm)
 | a_DataCon (K:datacon)
 | a_Case (a:tm) (brs5:brs)
 | a_Sub (R:role) (a:tm)
with brs : Set :=  (*r case branches *)
 | br_None : brs
 | br_One (K:datacon) (a:tm) (brs5:brs)
with co : Set :=  (*r explicit coercions *)
 | g_Triv : co
 | g_Var_b (_:nat)
 | g_Var_f (c:covar)
 | g_Beta (a:tm) (b:tm)
 | g_Refl (a:tm)
 | g_Refl2 (a:tm) (b:tm) (g:co)
 | g_Sym (g:co)
 | g_Trans (g1:co) (g2:co)
 | g_Sub (g:co)
 | g_PiCong (rho:relflag) (R:role) (g1:co) (g2:co)
 | g_AbsCong (rho:relflag) (R:role) (g1:co) (g2:co)
 | g_AppCong (g1:co) (rho:relflag) (R:role) (g2:co)
 | g_PiFst (g:co)
 | g_CPiFst (g:co)
 | g_IsoSnd (g:co)
 | g_PiSnd (g1:co) (g2:co)
 | g_CPiCong (g1:co) (g3:co)
 | g_CAbsCong (g1:co) (g3:co) (g4:co)
 | g_CAppCong (g:co) (g1:co) (g2:co)
 | g_CPiSnd (g:co) (g1:co) (g2:co)
 | g_Cast (g1:co) (R:role) (g2:co)
 | g_EqCong (g1:co) (A:tm) (g2:co)
 | g_IsoConv (phi1:constraint) (phi2:constraint) (g:co)
 | g_Eta (a:tm)
 | g_Left (g:co) (g':co)
 | g_Right (g:co) (g':co).

Definition roles : Set := list role.

Definition available_props : Type := atoms.

Inductive sort : Set :=  (*r binding classifier *)
 | Tm (A:tm)
 | Co (phi:constraint).

Inductive sig_sort : Type :=  (*r signature classifier *)
 | Cs (A:tm) (Rs:roles)
 | Ax (p:tm) (a:tm) (A:tm) (R:role) (Rs:roles) (D:available_props).

Definition context : Set := list ( atom * sort ).

Definition role_context : Set := list ( atom * role ).

Definition sig : Type := list (atom * sig_sort).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_co_wrt_co_rec (k:nat) (g_5:co) (g__6:co) {struct g__6}: co :=
  match g__6 with
  | g_Triv => g_Triv 
  | (g_Var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => g_Var_b nat
        | inleft (right _) => g_5
        | inright _ => g_Var_b (nat - 1)
      end
  | (g_Var_f c) => g_Var_f c
  | (g_Beta a b) => g_Beta (open_tm_wrt_co_rec k g_5 a) (open_tm_wrt_co_rec k g_5 b)
  | (g_Refl a) => g_Refl (open_tm_wrt_co_rec k g_5 a)
  | (g_Refl2 a b g) => g_Refl2 (open_tm_wrt_co_rec k g_5 a) (open_tm_wrt_co_rec k g_5 b) (open_co_wrt_co_rec k g_5 g)
  | (g_Sym g) => g_Sym (open_co_wrt_co_rec k g_5 g)
  | (g_Trans g1 g2) => g_Trans (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_Sub g) => g_Sub (open_co_wrt_co_rec k g_5 g)
  | (g_PiCong rho R g1 g2) => g_PiCong rho R (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_AbsCong rho R g1 g2) => g_AbsCong rho R (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_AppCong g1 rho R g2) => g_AppCong (open_co_wrt_co_rec k g_5 g1) rho R (open_co_wrt_co_rec k g_5 g2)
  | (g_PiFst g) => g_PiFst (open_co_wrt_co_rec k g_5 g)
  | (g_CPiFst g) => g_CPiFst (open_co_wrt_co_rec k g_5 g)
  | (g_IsoSnd g) => g_IsoSnd (open_co_wrt_co_rec k g_5 g)
  | (g_PiSnd g1 g2) => g_PiSnd (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_CPiCong g1 g3) => g_CPiCong (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec (S k) g_5 g3)
  | (g_CAbsCong g1 g3 g4) => g_CAbsCong (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec (S k) g_5 g3) (open_co_wrt_co_rec k g_5 g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (open_co_wrt_co_rec k g_5 g) (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (open_co_wrt_co_rec k g_5 g) (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_Cast g1 R g2) => g_Cast (open_co_wrt_co_rec k g_5 g1) R (open_co_wrt_co_rec k g_5 g2)
  | (g_EqCong g1 A g2) => g_EqCong (open_co_wrt_co_rec k g_5 g1) (open_tm_wrt_co_rec k g_5 A) (open_co_wrt_co_rec k g_5 g2)
  | (g_IsoConv phi1 phi2 g) => g_IsoConv (open_constraint_wrt_co_rec k g_5 phi1) (open_constraint_wrt_co_rec k g_5 phi2) (open_co_wrt_co_rec k g_5 g)
  | (g_Eta a) => g_Eta (open_tm_wrt_co_rec k g_5 a)
  | (g_Left g g') => g_Left (open_co_wrt_co_rec k g_5 g) (open_co_wrt_co_rec k g_5 g')
  | (g_Right g g') => g_Right (open_co_wrt_co_rec k g_5 g) (open_co_wrt_co_rec k g_5 g')
end
with open_brs_wrt_co_rec (k:nat) (g5:co) (brs_6:brs) {struct brs_6}: brs :=
  match brs_6 with
  | br_None => br_None 
  | (br_One K a brs5) => br_One K (open_tm_wrt_co_rec k g5 a) (open_brs_wrt_co_rec k g5 brs5)
end
with open_tm_wrt_co_rec (k:nat) (g5:co) (a5:tm) {struct a5}: tm :=
  match a5 with
  | a_Star => a_Star 
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => a_Var_f x
  | (a_Abs rho A b) => a_Abs rho (open_tm_wrt_co_rec k g5 A) (open_tm_wrt_co_rec k g5 b)
  | (a_UAbs rho b) => a_UAbs rho (open_tm_wrt_co_rec k g5 b)
  | (a_App a nu b) => a_App (open_tm_wrt_co_rec k g5 a) nu (open_tm_wrt_co_rec k g5 b)
  | (a_Pi rho A B) => a_Pi rho (open_tm_wrt_co_rec k g5 A) (open_tm_wrt_co_rec k g5 B)
  | (a_CAbs phi b) => a_CAbs (open_constraint_wrt_co_rec k g5 phi) (open_tm_wrt_co_rec (S k) g5 b)
  | (a_UCAbs b) => a_UCAbs (open_tm_wrt_co_rec (S k) g5 b)
  | (a_CApp a g) => a_CApp (open_tm_wrt_co_rec k g5 a) (open_co_wrt_co_rec k g5 g)
  | (a_CPi phi B) => a_CPi (open_constraint_wrt_co_rec k g5 phi) (open_tm_wrt_co_rec (S k) g5 B)
  | (a_Conv a R g) => a_Conv (open_tm_wrt_co_rec k g5 a) R (open_co_wrt_co_rec k g5 g)
  | (a_Fam F) => a_Fam F
  | a_Bullet => a_Bullet 
  | (a_Pattern R a F b1 b2) => a_Pattern R (open_tm_wrt_co_rec k g5 a) F (open_tm_wrt_co_rec k g5 b1) (open_tm_wrt_co_rec k g5 b2)
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (open_tm_wrt_co_rec k g5 a) (open_brs_wrt_co_rec k g5 brs5)
  | (a_Sub R a) => a_Sub R (open_tm_wrt_co_rec k g5 a)
end
with open_constraint_wrt_co_rec (k:nat) (g5:co) (phi5:constraint) : constraint :=
  match phi5 with
  | (Eq a b A R) => Eq (open_tm_wrt_co_rec k g5 a) (open_tm_wrt_co_rec k g5 b) (open_tm_wrt_co_rec k g5 A) R
end.

Fixpoint open_co_wrt_tm_rec (k:nat) (a5:tm) (g_5:co) {struct g_5}: co :=
  match g_5 with
  | g_Triv => g_Triv 
  | (g_Var_b nat) => g_Var_b nat
  | (g_Var_f c) => g_Var_f c
  | (g_Beta a b) => g_Beta (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b)
  | (g_Refl a) => g_Refl (open_tm_wrt_tm_rec k a5 a)
  | (g_Refl2 a b g) => g_Refl2 (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b) (open_co_wrt_tm_rec k a5 g)
  | (g_Sym g) => g_Sym (open_co_wrt_tm_rec k a5 g)
  | (g_Trans g1 g2) => g_Trans (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g2)
  | (g_Sub g) => g_Sub (open_co_wrt_tm_rec k a5 g)
  | (g_PiCong rho R g1 g2) => g_PiCong rho R (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec (S k) a5 g2)
  | (g_AbsCong rho R g1 g2) => g_AbsCong rho R (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec (S k) a5 g2)
  | (g_AppCong g1 rho R g2) => g_AppCong (open_co_wrt_tm_rec k a5 g1) rho R (open_co_wrt_tm_rec k a5 g2)
  | (g_PiFst g) => g_PiFst (open_co_wrt_tm_rec k a5 g)
  | (g_CPiFst g) => g_CPiFst (open_co_wrt_tm_rec k a5 g)
  | (g_IsoSnd g) => g_IsoSnd (open_co_wrt_tm_rec k a5 g)
  | (g_PiSnd g1 g2) => g_PiSnd (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g2)
  | (g_CPiCong g1 g3) => g_CPiCong (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g3)
  | (g_CAbsCong g1 g3 g4) => g_CAbsCong (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g3) (open_co_wrt_tm_rec k a5 g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (open_co_wrt_tm_rec k a5 g) (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (open_co_wrt_tm_rec k a5 g) (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g2)
  | (g_Cast g1 R g2) => g_Cast (open_co_wrt_tm_rec k a5 g1) R (open_co_wrt_tm_rec k a5 g2)
  | (g_EqCong g1 A g2) => g_EqCong (open_co_wrt_tm_rec k a5 g1) (open_tm_wrt_tm_rec k a5 A) (open_co_wrt_tm_rec k a5 g2)
  | (g_IsoConv phi1 phi2 g) => g_IsoConv (open_constraint_wrt_tm_rec k a5 phi1) (open_constraint_wrt_tm_rec k a5 phi2) (open_co_wrt_tm_rec k a5 g)
  | (g_Eta a) => g_Eta (open_tm_wrt_tm_rec k a5 a)
  | (g_Left g g') => g_Left (open_co_wrt_tm_rec k a5 g) (open_co_wrt_tm_rec k a5 g')
  | (g_Right g g') => g_Right (open_co_wrt_tm_rec k a5 g) (open_co_wrt_tm_rec k a5 g')
end
with open_brs_wrt_tm_rec (k:nat) (a5:tm) (brs_6:brs) {struct brs_6}: brs :=
  match brs_6 with
  | br_None => br_None 
  | (br_One K a brs5) => br_One K (open_tm_wrt_tm_rec k a5 a) (open_brs_wrt_tm_rec k a5 brs5)
end
with open_tm_wrt_tm_rec (k:nat) (a5:tm) (a_6:tm) {struct a_6}: tm :=
  match a_6 with
  | a_Star => a_Star 
  | (a_Var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => a_Var_b nat
        | inleft (right _) => a5
        | inright _ => a_Var_b (nat - 1)
      end
  | (a_Var_f x) => a_Var_f x
  | (a_Abs rho A b) => a_Abs rho (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 b)
  | (a_UAbs rho b) => a_UAbs rho (open_tm_wrt_tm_rec (S k) a5 b)
  | (a_App a nu b) => a_App (open_tm_wrt_tm_rec k a5 a) nu (open_tm_wrt_tm_rec k a5 b)
  | (a_Pi rho A B) => a_Pi rho (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 B)
  | (a_CAbs phi b) => a_CAbs (open_constraint_wrt_tm_rec k a5 phi) (open_tm_wrt_tm_rec k a5 b)
  | (a_UCAbs b) => a_UCAbs (open_tm_wrt_tm_rec k a5 b)
  | (a_CApp a g) => a_CApp (open_tm_wrt_tm_rec k a5 a) (open_co_wrt_tm_rec k a5 g)
  | (a_CPi phi B) => a_CPi (open_constraint_wrt_tm_rec k a5 phi) (open_tm_wrt_tm_rec k a5 B)
  | (a_Conv a R g) => a_Conv (open_tm_wrt_tm_rec k a5 a) R (open_co_wrt_tm_rec k a5 g)
  | (a_Fam F) => a_Fam F
  | a_Bullet => a_Bullet 
  | (a_Pattern R a F b1 b2) => a_Pattern R (open_tm_wrt_tm_rec k a5 a) F (open_tm_wrt_tm_rec k a5 b1) (open_tm_wrt_tm_rec k a5 b2)
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (open_tm_wrt_tm_rec k a5 a) (open_brs_wrt_tm_rec k a5 brs5)
  | (a_Sub R a) => a_Sub R (open_tm_wrt_tm_rec k a5 a)
end
with open_constraint_wrt_tm_rec (k:nat) (a5:tm) (phi5:constraint) : constraint :=
  match phi5 with
  | (Eq a b A R) => Eq (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b) (open_tm_wrt_tm_rec k a5 A) R
end.

Definition open_sort_wrt_co_rec (k:nat) (g5:co) (sort5:sort) : sort :=
  match sort5 with
  | (Tm A) => Tm (open_tm_wrt_co_rec k g5 A)
  | (Co phi) => Co (open_constraint_wrt_co_rec k g5 phi)
end.

Definition open_sig_sort_wrt_co_rec (k:nat) (g5:co) (sig_sort5:sig_sort) : sig_sort :=
  match sig_sort5 with
  | (Cs A Rs) => Cs (open_tm_wrt_co_rec k g5 A) Rs
  | (Ax p a A R Rs D) => Ax (open_tm_wrt_co_rec k g5 p) (open_tm_wrt_co_rec k g5 a) (open_tm_wrt_co_rec k g5 A) R Rs D
end.

Definition open_sig_sort_wrt_tm_rec (k:nat) (a5:tm) (sig_sort5:sig_sort) : sig_sort :=
  match sig_sort5 with
  | (Cs A Rs) => Cs (open_tm_wrt_tm_rec k a5 A) Rs
  | (Ax p a A R Rs D) => Ax (open_tm_wrt_tm_rec k a5 p) (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 A) R Rs D
end.

Definition open_sort_wrt_tm_rec (k:nat) (a5:tm) (sort5:sort) : sort :=
  match sort5 with
  | (Tm A) => Tm (open_tm_wrt_tm_rec k a5 A)
  | (Co phi) => Co (open_constraint_wrt_tm_rec k a5 phi)
end.

Definition open_brs_wrt_co g5 brs_6 := open_brs_wrt_co_rec 0 brs_6 g5.

Definition open_tm_wrt_co g5 a5 := open_tm_wrt_co_rec 0 a5 g5.

Definition open_brs_wrt_tm a5 brs_6 := open_brs_wrt_tm_rec 0 brs_6 a5.

Definition open_sort_wrt_co g5 sort5 := open_sort_wrt_co_rec 0 sort5 g5.

Definition open_sig_sort_wrt_co g5 sig_sort5 := open_sig_sort_wrt_co_rec 0 sig_sort5 g5.

Definition open_co_wrt_co g_5 g__6 := open_co_wrt_co_rec 0 g__6 g_5.

Definition open_sig_sort_wrt_tm a5 sig_sort5 := open_sig_sort_wrt_tm_rec 0 sig_sort5 a5.

Definition open_constraint_wrt_co g5 phi5 := open_constraint_wrt_co_rec 0 phi5 g5.

Definition open_constraint_wrt_tm a5 phi5 := open_constraint_wrt_tm_rec 0 phi5 a5.

Definition open_co_wrt_tm a5 g_5 := open_co_wrt_tm_rec 0 g_5 a5.

Definition open_sort_wrt_tm a5 sort5 := open_sort_wrt_tm_rec 0 sort5 a5.

Definition open_tm_wrt_tm a5 a_6 := open_tm_wrt_tm_rec 0 a_6 a5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_co_brs_tm_constraint *)
Inductive lc_co : co -> Prop :=    (* defn lc_co *)
 | lc_g_Triv : 
     (lc_co g_Triv)
 | lc_g_Var_f : forall (c:covar),
     (lc_co (g_Var_f c))
 | lc_g_Beta : forall (a b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_co (g_Beta a b))
 | lc_g_Refl : forall (a:tm),
     (lc_tm a) ->
     (lc_co (g_Refl a))
 | lc_g_Refl2 : forall (a b:tm) (g:co),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_co g) ->
     (lc_co (g_Refl2 a b g))
 | lc_g_Sym : forall (g:co),
     (lc_co g) ->
     (lc_co (g_Sym g))
 | lc_g_Trans : forall (g1 g2:co),
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_Trans g1 g2))
 | lc_g_Sub : forall (g:co),
     (lc_co g) ->
     (lc_co (g_Sub g))
 | lc_g_PiCong : forall (rho:relflag) (R:role) (g1 g2:co),
     (lc_co g1) ->
      ( forall x , lc_co  ( open_co_wrt_tm g2 (a_Var_f x) )  )  ->
     (lc_co (g_PiCong rho R g1 g2))
 | lc_g_AbsCong : forall (rho:relflag) (R:role) (g1 g2:co),
     (lc_co g1) ->
      ( forall x , lc_co  ( open_co_wrt_tm g2 (a_Var_f x) )  )  ->
     (lc_co (g_AbsCong rho R g1 g2))
 | lc_g_AppCong : forall (g1:co) (rho:relflag) (R:role) (g2:co),
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_AppCong g1 rho R g2))
 | lc_g_PiFst : forall (g:co),
     (lc_co g) ->
     (lc_co (g_PiFst g))
 | lc_g_CPiFst : forall (g:co),
     (lc_co g) ->
     (lc_co (g_CPiFst g))
 | lc_g_IsoSnd : forall (g:co),
     (lc_co g) ->
     (lc_co (g_IsoSnd g))
 | lc_g_PiSnd : forall (g1 g2:co),
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_PiSnd g1 g2))
 | lc_g_CPiCong : forall (g1 g3:co),
     (lc_co g1) ->
      ( forall c , lc_co  ( open_co_wrt_co g3 (g_Var_f c) )  )  ->
     (lc_co (g_CPiCong g1 g3))
 | lc_g_CAbsCong : forall (g1 g3 g4:co),
     (lc_co g1) ->
      ( forall c , lc_co  ( open_co_wrt_co g3 (g_Var_f c) )  )  ->
     (lc_co g4) ->
     (lc_co (g_CAbsCong g1 g3 g4))
 | lc_g_CAppCong : forall (g g1 g2:co),
     (lc_co g) ->
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_CAppCong g g1 g2))
 | lc_g_CPiSnd : forall (g g1 g2:co),
     (lc_co g) ->
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_CPiSnd g g1 g2))
 | lc_g_Cast : forall (g1:co) (R:role) (g2:co),
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_Cast g1 R g2))
 | lc_g_EqCong : forall (g1:co) (A:tm) (g2:co),
     (lc_co g1) ->
     (lc_tm A) ->
     (lc_co g2) ->
     (lc_co (g_EqCong g1 A g2))
 | lc_g_IsoConv : forall (phi1 phi2:constraint) (g:co),
     (lc_constraint phi1) ->
     (lc_constraint phi2) ->
     (lc_co g) ->
     (lc_co (g_IsoConv phi1 phi2 g))
 | lc_g_Eta : forall (a:tm),
     (lc_tm a) ->
     (lc_co (g_Eta a))
 | lc_g_Left : forall (g g':co),
     (lc_co g) ->
     (lc_co g') ->
     (lc_co (g_Left g g'))
 | lc_g_Right : forall (g g':co),
     (lc_co g) ->
     (lc_co g') ->
     (lc_co (g_Right g g'))
with lc_brs : brs -> Prop :=    (* defn lc_brs *)
 | lc_br_None : 
     (lc_brs br_None)
 | lc_br_One : forall (K:datacon) (a:tm) (brs5:brs),
     (lc_tm a) ->
     (lc_brs brs5) ->
     (lc_brs (br_One K a brs5))
with lc_tm : tm -> Prop :=    (* defn lc_tm *)
 | lc_a_Star : 
     (lc_tm a_Star)
 | lc_a_Var_f : forall (x:tmvar),
     (lc_tm (a_Var_f x))
 | lc_a_Abs : forall (rho:relflag) (A b:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     (lc_tm (a_Abs rho A b))
 | lc_a_UAbs : forall (rho:relflag) (b:tm),
      ( forall x , lc_tm  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     (lc_tm (a_UAbs rho b))
 | lc_a_App : forall (a:tm) (nu:appflag) (b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_App a nu b))
 | lc_a_Pi : forall (rho:relflag) (A B:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     (lc_tm (a_Pi rho A B))
 | lc_a_CAbs : forall (phi:constraint) (b:tm),
     (lc_constraint phi) ->
      ( forall c , lc_tm  ( open_tm_wrt_co b (g_Var_f c) )  )  ->
     (lc_tm (a_CAbs phi b))
 | lc_a_UCAbs : forall (b:tm),
      ( forall c , lc_tm  ( open_tm_wrt_co b (g_Var_f c) )  )  ->
     (lc_tm (a_UCAbs b))
 | lc_a_CApp : forall (a:tm) (g:co),
     (lc_tm a) ->
     (lc_co g) ->
     (lc_tm (a_CApp a g))
 | lc_a_CPi : forall (phi:constraint) (B:tm),
     (lc_constraint phi) ->
      ( forall c , lc_tm  ( open_tm_wrt_co B (g_Var_f c) )  )  ->
     (lc_tm (a_CPi phi B))
 | lc_a_Conv : forall (a:tm) (R:role) (g:co),
     (lc_tm a) ->
     (lc_co g) ->
     (lc_tm (a_Conv a R g))
 | lc_a_Fam : forall (F:const),
     (lc_tm (a_Fam F))
 | lc_a_Bullet : 
     (lc_tm a_Bullet)
 | lc_a_Pattern : forall (R:role) (a:tm) (F:const) (b1 b2:tm),
     (lc_tm a) ->
     (lc_tm b1) ->
     (lc_tm b2) ->
     (lc_tm (a_Pattern R a F b1 b2))
 | lc_a_DataCon : forall (K:datacon),
     (lc_tm (a_DataCon K))
 | lc_a_Case : forall (a:tm) (brs5:brs),
     (lc_tm a) ->
     (lc_brs brs5) ->
     (lc_tm (a_Case a brs5))
 | lc_a_Sub : forall (R:role) (a:tm),
     (lc_tm a) ->
     (lc_tm (a_Sub R a))
with lc_constraint : constraint -> Prop :=    (* defn lc_constraint *)
 | lc_Eq : forall (a b A:tm) (R:role),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm A) ->
     (lc_constraint (Eq a b A R)).

(* defns LC_sort *)
Inductive lc_sort : sort -> Prop :=    (* defn lc_sort *)
 | lc_Tm : forall (A:tm),
     (lc_tm A) ->
     (lc_sort (Tm A))
 | lc_Co : forall (phi:constraint),
     (lc_constraint phi) ->
     (lc_sort (Co phi)).

(* defns LC_sig_sort *)
Inductive lc_sig_sort : sig_sort -> Prop :=    (* defn lc_sig_sort *)
 | lc_Cs : forall (A:tm) (Rs:roles),
     (lc_tm A) ->
     (lc_sig_sort (Cs A Rs))
 | lc_Ax : forall (p a A:tm) (R:role) (Rs:roles) (D:available_props),
     (lc_tm p) ->
     (lc_tm a) ->
     (lc_tm A) ->
     (lc_sig_sort (Ax p a A R Rs D)).
(** free variables *)
Fixpoint fv_tm_tm_co (g_5:co) : vars :=
  match g_5 with
  | g_Triv => {}
  | (g_Var_b nat) => {}
  | (g_Var_f c) => {}
  | (g_Beta a b) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm b)
  | (g_Refl a) => (fv_tm_tm_tm a)
  | (g_Refl2 a b g) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm b) \u (fv_tm_tm_co g)
  | (g_Sym g) => (fv_tm_tm_co g)
  | (g_Trans g1 g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_Sub g) => (fv_tm_tm_co g)
  | (g_PiCong rho R g1 g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_AbsCong rho R g1 g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_AppCong g1 rho R g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_PiFst g) => (fv_tm_tm_co g)
  | (g_CPiFst g) => (fv_tm_tm_co g)
  | (g_IsoSnd g) => (fv_tm_tm_co g)
  | (g_PiSnd g1 g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_CPiCong g1 g3) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g3)
  | (g_CAbsCong g1 g3 g4) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g3) \u (fv_tm_tm_co g4)
  | (g_CAppCong g g1 g2) => (fv_tm_tm_co g) \u (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_CPiSnd g g1 g2) => (fv_tm_tm_co g) \u (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_Cast g1 R g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_EqCong g1 A g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_tm A) \u (fv_tm_tm_co g2)
  | (g_IsoConv phi1 phi2 g) => (fv_tm_tm_constraint phi1) \u (fv_tm_tm_constraint phi2) \u (fv_tm_tm_co g)
  | (g_Eta a) => (fv_tm_tm_tm a)
  | (g_Left g g') => (fv_tm_tm_co g) \u (fv_tm_tm_co g')
  | (g_Right g g') => (fv_tm_tm_co g) \u (fv_tm_tm_co g')
end
with fv_tm_tm_brs (brs_6:brs) : vars :=
  match brs_6 with
  | br_None => {}
  | (br_One K a brs5) => (fv_tm_tm_tm a) \u (fv_tm_tm_brs brs5)
end
with fv_tm_tm_tm (a5:tm) : vars :=
  match a5 with
  | a_Star => {}
  | (a_Var_b nat) => {}
  | (a_Var_f x) => {{x}}
  | (a_Abs rho A b) => (fv_tm_tm_tm A) \u (fv_tm_tm_tm b)
  | (a_UAbs rho b) => (fv_tm_tm_tm b)
  | (a_App a nu b) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm b)
  | (a_Pi rho A B) => (fv_tm_tm_tm A) \u (fv_tm_tm_tm B)
  | (a_CAbs phi b) => (fv_tm_tm_constraint phi) \u (fv_tm_tm_tm b)
  | (a_UCAbs b) => (fv_tm_tm_tm b)
  | (a_CApp a g) => (fv_tm_tm_tm a) \u (fv_tm_tm_co g)
  | (a_CPi phi B) => (fv_tm_tm_constraint phi) \u (fv_tm_tm_tm B)
  | (a_Conv a R g) => (fv_tm_tm_tm a) \u (fv_tm_tm_co g)
  | (a_Fam F) => {}
  | a_Bullet => {}
  | (a_Pattern R a F b1 b2) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm b1) \u (fv_tm_tm_tm b2)
  | (a_DataCon K) => {}
  | (a_Case a brs5) => (fv_tm_tm_tm a) \u (fv_tm_tm_brs brs5)
  | (a_Sub R a) => (fv_tm_tm_tm a)
end
with fv_tm_tm_constraint (phi5:constraint) : vars :=
  match phi5 with
  | (Eq a b A R) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm b) \u (fv_tm_tm_tm A)
end.

Fixpoint fv_co_co_co (g_5:co) : vars :=
  match g_5 with
  | g_Triv => {}
  | (g_Var_b nat) => {}
  | (g_Var_f c) => {{c}}
  | (g_Beta a b) => (fv_co_co_tm a) \u (fv_co_co_tm b)
  | (g_Refl a) => (fv_co_co_tm a)
  | (g_Refl2 a b g) => (fv_co_co_tm a) \u (fv_co_co_tm b) \u (fv_co_co_co g)
  | (g_Sym g) => (fv_co_co_co g)
  | (g_Trans g1 g2) => (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_Sub g) => (fv_co_co_co g)
  | (g_PiCong rho R g1 g2) => (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_AbsCong rho R g1 g2) => (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_AppCong g1 rho R g2) => (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_PiFst g) => (fv_co_co_co g)
  | (g_CPiFst g) => (fv_co_co_co g)
  | (g_IsoSnd g) => (fv_co_co_co g)
  | (g_PiSnd g1 g2) => (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_CPiCong g1 g3) => (fv_co_co_co g1) \u (fv_co_co_co g3)
  | (g_CAbsCong g1 g3 g4) => (fv_co_co_co g1) \u (fv_co_co_co g3) \u (fv_co_co_co g4)
  | (g_CAppCong g g1 g2) => (fv_co_co_co g) \u (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_CPiSnd g g1 g2) => (fv_co_co_co g) \u (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_Cast g1 R g2) => (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_EqCong g1 A g2) => (fv_co_co_co g1) \u (fv_co_co_tm A) \u (fv_co_co_co g2)
  | (g_IsoConv phi1 phi2 g) => (fv_co_co_constraint phi1) \u (fv_co_co_constraint phi2) \u (fv_co_co_co g)
  | (g_Eta a) => (fv_co_co_tm a)
  | (g_Left g g') => (fv_co_co_co g) \u (fv_co_co_co g')
  | (g_Right g g') => (fv_co_co_co g) \u (fv_co_co_co g')
end
with fv_co_co_brs (brs_6:brs) : vars :=
  match brs_6 with
  | br_None => {}
  | (br_One K a brs5) => (fv_co_co_tm a) \u (fv_co_co_brs brs5)
end
with fv_co_co_tm (a5:tm) : vars :=
  match a5 with
  | a_Star => {}
  | (a_Var_b nat) => {}
  | (a_Var_f x) => {}
  | (a_Abs rho A b) => (fv_co_co_tm A) \u (fv_co_co_tm b)
  | (a_UAbs rho b) => (fv_co_co_tm b)
  | (a_App a nu b) => (fv_co_co_tm a) \u (fv_co_co_tm b)
  | (a_Pi rho A B) => (fv_co_co_tm A) \u (fv_co_co_tm B)
  | (a_CAbs phi b) => (fv_co_co_constraint phi) \u (fv_co_co_tm b)
  | (a_UCAbs b) => (fv_co_co_tm b)
  | (a_CApp a g) => (fv_co_co_tm a) \u (fv_co_co_co g)
  | (a_CPi phi B) => (fv_co_co_constraint phi) \u (fv_co_co_tm B)
  | (a_Conv a R g) => (fv_co_co_tm a) \u (fv_co_co_co g)
  | (a_Fam F) => {}
  | a_Bullet => {}
  | (a_Pattern R a F b1 b2) => (fv_co_co_tm a) \u (fv_co_co_tm b1) \u (fv_co_co_tm b2)
  | (a_DataCon K) => {}
  | (a_Case a brs5) => (fv_co_co_tm a) \u (fv_co_co_brs brs5)
  | (a_Sub R a) => (fv_co_co_tm a)
end
with fv_co_co_constraint (phi5:constraint) : vars :=
  match phi5 with
  | (Eq a b A R) => (fv_co_co_tm a) \u (fv_co_co_tm b) \u (fv_co_co_tm A)
end.

Definition fv_tm_tm_sort (sort5:sort) : vars :=
  match sort5 with
  | (Tm A) => (fv_tm_tm_tm A)
  | (Co phi) => (fv_tm_tm_constraint phi)
end.

Definition fv_co_co_sort (sort5:sort) : vars :=
  match sort5 with
  | (Tm A) => (fv_co_co_tm A)
  | (Co phi) => (fv_co_co_constraint phi)
end.

Definition fv_tm_tm_sig_sort (sig_sort5:sig_sort) : vars :=
  match sig_sort5 with
  | (Cs A Rs) => (fv_tm_tm_tm A)
  | (Ax p a A R Rs D) => (fv_tm_tm_tm p) \u (fv_tm_tm_tm a) \u (fv_tm_tm_tm A)
end.

Definition fv_co_co_sig_sort (sig_sort5:sig_sort) : vars :=
  match sig_sort5 with
  | (Cs A Rs) => (fv_co_co_tm A)
  | (Ax p a A R Rs D) => (fv_co_co_tm p) \u (fv_co_co_tm a) \u (fv_co_co_tm A)
end.

(** substitutions *)
Fixpoint tm_subst_tm_co (a5:tm) (x5:tmvar) (g_5:co) {struct g_5} : co :=
  match g_5 with
  | g_Triv => g_Triv 
  | (g_Var_b nat) => g_Var_b nat
  | (g_Var_f c) => g_Var_f c
  | (g_Beta a b) => g_Beta (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_tm a5 x5 b)
  | (g_Refl a) => g_Refl (tm_subst_tm_tm a5 x5 a)
  | (g_Refl2 a b g) => g_Refl2 (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_tm a5 x5 b) (tm_subst_tm_co a5 x5 g)
  | (g_Sym g) => g_Sym (tm_subst_tm_co a5 x5 g)
  | (g_Trans g1 g2) => g_Trans (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_Sub g) => g_Sub (tm_subst_tm_co a5 x5 g)
  | (g_PiCong rho R g1 g2) => g_PiCong rho R (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_AbsCong rho R g1 g2) => g_AbsCong rho R (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_AppCong g1 rho R g2) => g_AppCong (tm_subst_tm_co a5 x5 g1) rho R (tm_subst_tm_co a5 x5 g2)
  | (g_PiFst g) => g_PiFst (tm_subst_tm_co a5 x5 g)
  | (g_CPiFst g) => g_CPiFst (tm_subst_tm_co a5 x5 g)
  | (g_IsoSnd g) => g_IsoSnd (tm_subst_tm_co a5 x5 g)
  | (g_PiSnd g1 g2) => g_PiSnd (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_CPiCong g1 g3) => g_CPiCong (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g3)
  | (g_CAbsCong g1 g3 g4) => g_CAbsCong (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g3) (tm_subst_tm_co a5 x5 g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (tm_subst_tm_co a5 x5 g) (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (tm_subst_tm_co a5 x5 g) (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_Cast g1 R g2) => g_Cast (tm_subst_tm_co a5 x5 g1) R (tm_subst_tm_co a5 x5 g2)
  | (g_EqCong g1 A g2) => g_EqCong (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_tm a5 x5 A) (tm_subst_tm_co a5 x5 g2)
  | (g_IsoConv phi1 phi2 g) => g_IsoConv (tm_subst_tm_constraint a5 x5 phi1) (tm_subst_tm_constraint a5 x5 phi2) (tm_subst_tm_co a5 x5 g)
  | (g_Eta a) => g_Eta (tm_subst_tm_tm a5 x5 a)
  | (g_Left g g') => g_Left (tm_subst_tm_co a5 x5 g) (tm_subst_tm_co a5 x5 g')
  | (g_Right g g') => g_Right (tm_subst_tm_co a5 x5 g) (tm_subst_tm_co a5 x5 g')
end
with tm_subst_tm_brs (a5:tm) (x5:tmvar) (brs_6:brs) {struct brs_6} : brs :=
  match brs_6 with
  | br_None => br_None 
  | (br_One K a brs5) => br_One K (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_brs a5 x5 brs5)
end
with tm_subst_tm_tm (a5:tm) (x5:tmvar) (a_6:tm) {struct a_6} : tm :=
  match a_6 with
  | a_Star => a_Star 
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => (if eq_var x x5 then a5 else (a_Var_f x))
  | (a_Abs rho A b) => a_Abs rho (tm_subst_tm_tm a5 x5 A) (tm_subst_tm_tm a5 x5 b)
  | (a_UAbs rho b) => a_UAbs rho (tm_subst_tm_tm a5 x5 b)
  | (a_App a nu b) => a_App (tm_subst_tm_tm a5 x5 a) nu (tm_subst_tm_tm a5 x5 b)
  | (a_Pi rho A B) => a_Pi rho (tm_subst_tm_tm a5 x5 A) (tm_subst_tm_tm a5 x5 B)
  | (a_CAbs phi b) => a_CAbs (tm_subst_tm_constraint a5 x5 phi) (tm_subst_tm_tm a5 x5 b)
  | (a_UCAbs b) => a_UCAbs (tm_subst_tm_tm a5 x5 b)
  | (a_CApp a g) => a_CApp (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_co a5 x5 g)
  | (a_CPi phi B) => a_CPi (tm_subst_tm_constraint a5 x5 phi) (tm_subst_tm_tm a5 x5 B)
  | (a_Conv a R g) => a_Conv (tm_subst_tm_tm a5 x5 a) R (tm_subst_tm_co a5 x5 g)
  | (a_Fam F) => a_Fam F
  | a_Bullet => a_Bullet 
  | (a_Pattern R a F b1 b2) => a_Pattern R (tm_subst_tm_tm a5 x5 a) F (tm_subst_tm_tm a5 x5 b1) (tm_subst_tm_tm a5 x5 b2)
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_brs a5 x5 brs5)
  | (a_Sub R a) => a_Sub R (tm_subst_tm_tm a5 x5 a)
end
with tm_subst_tm_constraint (a5:tm) (x5:tmvar) (phi5:constraint) {struct phi5} : constraint :=
  match phi5 with
  | (Eq a b A R) => Eq (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_tm a5 x5 b) (tm_subst_tm_tm a5 x5 A) R
end.

Fixpoint co_subst_co_co (g_5:co) (c5:covar) (g__6:co) {struct g__6} : co :=
  match g__6 with
  | g_Triv => g_Triv 
  | (g_Var_b nat) => g_Var_b nat
  | (g_Var_f c) => (if eq_var c c5 then g_5 else (g_Var_f c))
  | (g_Beta a b) => g_Beta (co_subst_co_tm g_5 c5 a) (co_subst_co_tm g_5 c5 b)
  | (g_Refl a) => g_Refl (co_subst_co_tm g_5 c5 a)
  | (g_Refl2 a b g) => g_Refl2 (co_subst_co_tm g_5 c5 a) (co_subst_co_tm g_5 c5 b) (co_subst_co_co g_5 c5 g)
  | (g_Sym g) => g_Sym (co_subst_co_co g_5 c5 g)
  | (g_Trans g1 g2) => g_Trans (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g2)
  | (g_Sub g) => g_Sub (co_subst_co_co g_5 c5 g)
  | (g_PiCong rho R g1 g2) => g_PiCong rho R (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g2)
  | (g_AbsCong rho R g1 g2) => g_AbsCong rho R (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g2)
  | (g_AppCong g1 rho R g2) => g_AppCong (co_subst_co_co g_5 c5 g1) rho R (co_subst_co_co g_5 c5 g2)
  | (g_PiFst g) => g_PiFst (co_subst_co_co g_5 c5 g)
  | (g_CPiFst g) => g_CPiFst (co_subst_co_co g_5 c5 g)
  | (g_IsoSnd g) => g_IsoSnd (co_subst_co_co g_5 c5 g)
  | (g_PiSnd g1 g2) => g_PiSnd (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g2)
  | (g_CPiCong g1 g3) => g_CPiCong (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g3)
  | (g_CAbsCong g1 g3 g4) => g_CAbsCong (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g3) (co_subst_co_co g_5 c5 g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (co_subst_co_co g_5 c5 g) (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (co_subst_co_co g_5 c5 g) (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g2)
  | (g_Cast g1 R g2) => g_Cast (co_subst_co_co g_5 c5 g1) R (co_subst_co_co g_5 c5 g2)
  | (g_EqCong g1 A g2) => g_EqCong (co_subst_co_co g_5 c5 g1) (co_subst_co_tm g_5 c5 A) (co_subst_co_co g_5 c5 g2)
  | (g_IsoConv phi1 phi2 g) => g_IsoConv (co_subst_co_constraint g_5 c5 phi1) (co_subst_co_constraint g_5 c5 phi2) (co_subst_co_co g_5 c5 g)
  | (g_Eta a) => g_Eta (co_subst_co_tm g_5 c5 a)
  | (g_Left g g') => g_Left (co_subst_co_co g_5 c5 g) (co_subst_co_co g_5 c5 g')
  | (g_Right g g') => g_Right (co_subst_co_co g_5 c5 g) (co_subst_co_co g_5 c5 g')
end
with co_subst_co_brs (g5:co) (c5:covar) (brs_6:brs) {struct brs_6} : brs :=
  match brs_6 with
  | br_None => br_None 
  | (br_One K a brs5) => br_One K (co_subst_co_tm g5 c5 a) (co_subst_co_brs g5 c5 brs5)
end
with co_subst_co_tm (g5:co) (c5:covar) (a5:tm) {struct a5} : tm :=
  match a5 with
  | a_Star => a_Star 
  | (a_Var_b nat) => a_Var_b nat
  | (a_Var_f x) => a_Var_f x
  | (a_Abs rho A b) => a_Abs rho (co_subst_co_tm g5 c5 A) (co_subst_co_tm g5 c5 b)
  | (a_UAbs rho b) => a_UAbs rho (co_subst_co_tm g5 c5 b)
  | (a_App a nu b) => a_App (co_subst_co_tm g5 c5 a) nu (co_subst_co_tm g5 c5 b)
  | (a_Pi rho A B) => a_Pi rho (co_subst_co_tm g5 c5 A) (co_subst_co_tm g5 c5 B)
  | (a_CAbs phi b) => a_CAbs (co_subst_co_constraint g5 c5 phi) (co_subst_co_tm g5 c5 b)
  | (a_UCAbs b) => a_UCAbs (co_subst_co_tm g5 c5 b)
  | (a_CApp a g) => a_CApp (co_subst_co_tm g5 c5 a) (co_subst_co_co g5 c5 g)
  | (a_CPi phi B) => a_CPi (co_subst_co_constraint g5 c5 phi) (co_subst_co_tm g5 c5 B)
  | (a_Conv a R g) => a_Conv (co_subst_co_tm g5 c5 a) R (co_subst_co_co g5 c5 g)
  | (a_Fam F) => a_Fam F
  | a_Bullet => a_Bullet 
  | (a_Pattern R a F b1 b2) => a_Pattern R (co_subst_co_tm g5 c5 a) F (co_subst_co_tm g5 c5 b1) (co_subst_co_tm g5 c5 b2)
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (co_subst_co_tm g5 c5 a) (co_subst_co_brs g5 c5 brs5)
  | (a_Sub R a) => a_Sub R (co_subst_co_tm g5 c5 a)
end
with co_subst_co_constraint (g5:co) (c5:covar) (phi5:constraint) {struct phi5} : constraint :=
  match phi5 with
  | (Eq a b A R) => Eq (co_subst_co_tm g5 c5 a) (co_subst_co_tm g5 c5 b) (co_subst_co_tm g5 c5 A) R
end.

Definition tm_subst_tm_sort (a5:tm) (x5:tmvar) (sort5:sort) : sort :=
  match sort5 with
  | (Tm A) => Tm (tm_subst_tm_tm a5 x5 A)
  | (Co phi) => Co (tm_subst_tm_constraint a5 x5 phi)
end.

Definition co_subst_co_sort (g5:co) (c5:covar) (sort5:sort) : sort :=
  match sort5 with
  | (Tm A) => Tm (co_subst_co_tm g5 c5 A)
  | (Co phi) => Co (co_subst_co_constraint g5 c5 phi)
end.

Definition tm_subst_tm_sig_sort (a5:tm) (x5:tmvar) (sig_sort5:sig_sort) : sig_sort :=
  match sig_sort5 with
  | (Cs A Rs) => Cs (tm_subst_tm_tm a5 x5 A) Rs
  | (Ax p a A R Rs D) => Ax (tm_subst_tm_tm a5 x5 p) (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_tm a5 x5 A) R Rs D
end.

Definition co_subst_co_sig_sort (g5:co) (c5:covar) (sig_sort5:sig_sort) : sig_sort :=
  match sig_sort5 with
  | (Cs A Rs) => Cs (co_subst_co_tm g5 c5 A) Rs
  | (Ax p a A R Rs D) => Ax (co_subst_co_tm g5 c5 p) (co_subst_co_tm g5 c5 a) (co_subst_co_tm g5 c5 A) R Rs D
end.


Definition app_role (rr : appflag) : role :=
  match rr with
  | Rho _ => Nom
  | Role r => r
  end.

Definition app_rho (rr : appflag) : relflag :=
  match rr with
  | Rho p => p
  | Role _ => Rel
  end.

Definition min (r1 : role) (r2 : role) : role :=
  match r1 , r2 with
  | Nom, _   => Nom
  | _  , Nom => Nom
  | Rep, Rep => Rep
  end.

Definition max (r1 : role) (r2 : role) : role :=
  match r1 , r2 with
  | _, Rep   => Rep
  | Rep, _   => Rep
  | Nom, Nom => Nom
  end.

Definition lte_role (r1 : role) (r2 : role) : bool :=
  match r1 , r2 with
  | Nom, _   => true
  | Rep, Nom => false
  | Rep, Rep => true
  end.

Parameter str : bool.
Definition param (r1 : role) (r2 : role) :=
  if str then r1 else min r1 r2.

Fixpoint erase_tm (a : tm) (r : role) : tm :=
   match a with
   | a_Star    => a_Star
   | a_Var_b n => a_Var_b n
   | a_Var_f x => a_Var_f x
   | a_Abs rho A b => a_UAbs rho (erase_tm b r)
   | a_UAbs rho b => a_UAbs rho (erase_tm b r)
   | a_App a (Role R) b => a_App (erase_tm a r) (Role R) (erase_tm b r)
   | a_App a (Rho Rel) b => a_App (erase_tm a r) (Rho Rel) (erase_tm b r)
   | a_App a (Rho Irrel) b => a_App (erase_tm a r) (Rho Irrel) a_Bullet
   | a_Fam F => a_Fam F
   | a_Pi rho A B => a_Pi rho (erase_tm A r) (erase_tm B r)
   | a_Conv a r1 g => if (lte_role r1 r) then
                        erase_tm a r else
                                 a_Conv (erase_tm a r) r1 g_Triv
   | a_CPi phi B => a_CPi (erase_constraint phi r) (erase_tm B r)
   | a_CAbs phi b => a_UCAbs (erase_tm b r)
   | a_UCAbs b => a_UCAbs (erase_tm b r)
   | a_CApp a g => a_CApp (erase_tm a r) g_Triv
   | a_DataCon K => a_Star  (* a_DataCon K *)
   | a_Case a brs => a_Star (* a_Case (erase_tm a) (erase_brs brs) *)
   | a_Bullet => a_Bullet
   | a_Pattern R a1 F b1 b2 => a_Pattern R (erase_tm a1 r) F (erase_tm b1 r) (erase_tm b2 r)
   | a_Sub _ a => erase_tm a r
   end
with erase_brs (x : brs) (r:role): brs :=
   match x with
   | br_None => br_None
   | br_One k a y => br_One k (erase_tm a r) (erase_brs y r)
   end
with erase_constraint (phi : constraint) (r:role): constraint :=
   match phi with
   | Eq A B A1 R => Eq (erase_tm A R) (erase_tm B R) (erase_tm A1 R) R
   end.

Definition erase_sort s r :=
 match s with
 | Tm a => Tm (erase_tm a r)
 | Co p => Co (erase_constraint p r)
end.


Definition erase_csort s r :=
 match s with
 | Cs a Rs => Cs (erase_tm a r) Rs
 | Ax p a A R Rs D => Ax (erase_tm p r) (erase_tm a r) (erase_tm A r) R Rs D
end.

Definition erase_context G r := map (fun s => erase_sort s r) G.
Definition erase_sig S r := map (fun s => erase_csort s r) S.

(* -------------- A specific signature with Fix ------------ *)
Definition Fix : atom.
  pick fresh F.
  exact F.
Qed.

Definition FixVar1 : atom.
 pick fresh F.
 exact F.
Qed.

Definition FixVar2 : atom.
 pick fresh F.
 exact F.
Qed.

Definition FixPat : tm := a_App (a_App (a_Fam Fix) (Rho Irrel) (a_Var_f FixVar1)) (Rho Rel) (a_Var_f FixVar2).

Definition FixDef : tm := a_App (a_Var_f FixVar2) (Rho Rel) (a_App (a_App (a_Fam Fix) (Rho Irrel) a_Bullet) (Rho Rel) (a_Var_f FixVar2)).

Definition FixTy : tm := a_Var_f FixVar1.

Definition an_toplevel : sig := Fix ~ Ax FixPat FixDef FixTy Rep (Nom :: [Nom]) empty.

Definition toplevel : sig := erase_sig an_toplevel Nom.

Fixpoint range (L : role_context) : roles :=
  match L with
  | nil => nil
  | (x,R) :: L' => R :: range(L')
  end.

Fixpoint var_pat (p : tm) : role_context := 
   match p with
      a_App p (Role R) (a_Var_f x) => (x, R) :: (var_pat p)
    | a_App p (Rho Irrel) Bullet => var_pat p
    | a_CApp p g_Triv => var_pat p
    | _  => nil
   end.


(** definitions *)

(* defns JSubRole *)
Inductive SubRole : role -> role -> Prop :=    (* defn SubRole *)
 | NomBot : forall (R:role),
     SubRole Nom R
 | RepTop : forall (R:role),
     SubRole R Rep
 | Refl : forall (R:role),
     SubRole R R
 | Trans : forall (R1 R3 R2:role),
     SubRole R1 R2 ->
     SubRole R2 R3 ->
     SubRole R1 R3.

(* defns JPath *)
Inductive Path : tm -> const -> roles -> Prop :=    (* defn Path *)
 | Path_AbsConst : forall (F:const) (Rs:roles) (A:tm),
      binds  F  ( (Cs A Rs) )   toplevel   ->
     Path (a_Fam F) F Rs
 | Path_Const : forall (F:const) (Rs:roles) (p a A:tm) (R1:role) (D:available_props),
      binds  F  ( (Ax p a A R1 Rs D) )   toplevel   ->
     Path (a_Fam F) F Rs
 | Path_App : forall (a:tm) (R1:role) (b':tm) (F:const) (Rs:roles),
     lc_tm b' ->
     Path a F  ( R1 :: Rs )  ->
     Path  ( (a_App a (Role R1) b') )  F Rs
 | Path_IApp : forall (a:tm) (F:const) (Rs:roles),
     Path a F Rs ->
     Path  ( (a_App a (Rho Irrel) a_Bullet) )  F Rs
 | Path_CApp : forall (a:tm) (F:const) (Rs:roles),
     Path a F Rs ->
     Path  ( (a_CApp a g_Triv) )  F Rs.

(* defns JCasePath *)
Inductive CasePath : role -> tm -> const -> Prop :=    (* defn CasePath *)
 | CasePath_AbsConst : forall (R:role) (F:const) (A:tm) (Rs:roles),
      binds  F  ( (Cs A Rs) )   toplevel   ->
     CasePath R (a_Fam F) F
 | CasePath_Const : forall (R:role) (F:const) (p a A:tm) (R1:role) (Rs:roles) (D:available_props),
      binds  F  ( (Ax p a A R1 Rs D) )   toplevel   ->
      not (  ( SubRole R1 R )  )  ->
     CasePath R (a_Fam F) F
 | CasePath_App : forall (R:role) (a:tm) (rho:relflag) (b':tm) (F:const),
     lc_tm b' ->
     CasePath R a F ->
     CasePath R  ( (a_App a (Rho rho) b') )  F
 | CasePath_CApp : forall (R:role) (a:tm) (F:const),
     CasePath R a F ->
     CasePath R  ( (a_CApp a g_Triv) )  F.

(* defns JValuePath *)
Inductive ValuePath : tm -> const -> Prop :=    (* defn ValuePath *)
 | ValuePath_AbsConst : forall (F:const) (A:tm) (Rs:roles),
      binds  F  ( (Cs A Rs) )   toplevel   ->
     ValuePath (a_Fam F) F
 | ValuePath_Const : forall (F:const) (p a A:tm) (R1:role) (Rs:roles) (D:available_props),
      binds  F  ( (Ax p a A R1 Rs D) )   toplevel   ->
     ValuePath (a_Fam F) F
 | ValuePath_App : forall (a:tm) (nu:appflag) (b':tm) (F:const),
     lc_tm b' ->
     ValuePath a F ->
     ValuePath  ( (a_App a nu b') )  F
 | ValuePath_CApp : forall (a:tm) (F:const),
     ValuePath a F ->
     ValuePath  ( (a_CApp a g_Triv) )  F.

(* defns JPatCtx *)
Inductive PatternContexts : role_context -> context -> const -> tm -> available_props -> tm -> tm -> Prop :=    (* defn PatternContexts *)
 | PatCtx_Const : forall (F:const) (A:tm) (D:available_props),
     lc_tm A ->
     PatternContexts  nil   nil  F A D (a_Fam F) A
 | PatCtx_PiRel : forall (W:role_context) (x:tmvar) (R:role) (G:context) (A':tm) (F:const) (B:tm) (D:available_props) (p A:tm),
     PatternContexts W G F B D p (a_Pi Rel A' A) ->
      ~ AtomSetImpl.In  x   D  ->
     PatternContexts  (( x  ~  R ) ++  W )   (( x ~ Tm  A' ) ++  G )  F B D (a_App p (Role R) (a_Var_f x))  (open_tm_wrt_tm  A   (a_Var_f x) ) 
 | PatCtx_PiIrr : forall (W:role_context) (G:context) (x:tmvar) (A':tm) (F:const) (B:tm) (D:available_props) (p A:tm),
     PatternContexts W G F B D p (a_Pi Irrel A' A) ->
      ~ AtomSetImpl.In  x   D  ->
     PatternContexts W  (( x ~ Tm  A' ) ++  G )  F B D (a_App p (Rho Irrel) a_Bullet)  (open_tm_wrt_tm  A   (a_Var_f x) ) 
 | PatCtx_CPi : forall (W:role_context) (G:context) (c:covar) (phi:constraint) (F:const) (B:tm) (D:available_props) (p A:tm),
     PatternContexts W G F B D p (a_CPi phi A) ->
      ~ AtomSetImpl.In  c   D  ->
     PatternContexts W  (( c ~ Co  phi ) ++  G )  F B D (a_CApp p g_Triv)  (open_tm_wrt_co  A   (g_Var_f c) ) .

(* defns JMatchSubst *)
Inductive MatchSubst : const -> tm -> tm -> tm -> tm -> Prop :=    (* defn MatchSubst *)
 | MatchSubst_Const : forall (F:const) (b p a A:tm) (R1:role) (Rs:roles) (D:available_props),
     lc_tm b ->
      binds  F  ( (Ax p a A R1 Rs D) )   toplevel   ->
     MatchSubst F (a_Fam F) (a_Fam F) b b
 | MatchSubst_AppRelR : forall (F:const) (a1:tm) (R:role) (a a2:tm) (x:tmvar) (b1 b2:tm),
     lc_tm a ->
     MatchSubst F a1 a2 b1 b2 ->
     MatchSubst F  ( (a_App a1 (Role R) a) )   ( (a_App a2 (Role R) (a_Var_f x)) )  b1  (  (tm_subst_tm_tm  a   x   b2 )  ) 
 | MatchSubst_AppIrrel : forall (F:const) (a1 a2 b1 b2:tm),
     MatchSubst F a1 a2 b1 b2 ->
     MatchSubst F  ( (a_App a1 (Rho Irrel) a_Bullet) )   ( (a_App a2 (Rho Irrel) a_Bullet) )  b1 b2
 | MatchSubst_CApp : forall (F:const) (a1 a2 b1 b2:tm),
     MatchSubst F a1 a2 b1 b2 ->
     MatchSubst F  ( (a_CApp a1 g_Triv) )   ( (a_CApp a2 g_Triv) )  b1 b2.

(* defns JApplyArgs *)
Inductive ApplyArgs : tm -> tm -> tm -> Prop :=    (* defn ApplyArgs *)
 | ApplyArgs_Const : forall (F:const) (b:tm),
     lc_tm b ->
     ApplyArgs (a_Fam F) b b
 | ApplyArgs_App : forall (a:tm) (rho:relflag) (a' b b':tm),
     lc_tm a' ->
     ApplyArgs a b b' ->
     ApplyArgs (a_App a (Rho rho) a') b (a_App b' (Rho rho) a')
 | ApplyArgs_CApp : forall (a b b':tm),
     ApplyArgs a b b' ->
     ApplyArgs (a_CApp a g_Triv) b (a_CApp b' g_Triv).

(* defns JValue *)
Inductive Value : role -> tm -> Prop :=    (* defn Value *)
 | Value_Star : forall (R:role),
     Value R a_Star
 | Value_Pi : forall (R:role) (rho:relflag) (A B:tm),
     lc_tm A ->
     lc_tm (a_Pi rho A B) ->
     Value R (a_Pi rho A B)
 | Value_CPi : forall (R:role) (phi:constraint) (B:tm),
     lc_constraint phi ->
     lc_tm (a_CPi phi B) ->
     Value R (a_CPi phi B)
 | Value_AbsRel : forall (R:role) (A a:tm),
     lc_tm A ->
     lc_tm (a_Abs Rel A a) ->
     Value R (a_Abs Rel A a)
 | Value_UAbsRel : forall (R:role) (a:tm),
     lc_tm (a_UAbs Rel a) ->
     Value R (a_UAbs Rel a)
 | Value_UAbsIrrel : forall (L:vars) (R:role) (a:tm),
      ( forall x , x \notin  L  -> Value R  ( open_tm_wrt_tm a (a_Var_f x) )  )  ->
     Value R (a_UAbs Irrel a)
 | Value_CAbs : forall (R:role) (phi:constraint) (a:tm),
     lc_constraint phi ->
     lc_tm (a_CAbs phi a) ->
     Value R (a_CAbs phi a)
 | Value_UCAbs : forall (R:role) (a:tm),
     lc_tm (a_UCAbs a) ->
     Value R (a_UCAbs a)
 | Value_Const : forall (R:role) (a:tm) (F:const) (A:tm) (Rs:roles),
     ValuePath a F ->
      binds  F  ( (Cs A Rs) )   toplevel   ->
     Value R a
 | Value_Path : forall (R:role) (a:tm) (F:const) (p b A:tm) (R1:role) (Rs:roles) (D':available_props),
     ValuePath a F ->
      binds  F  ( (Ax p b A R1 Rs  (  (  (fv_tm_tm_tm  a )   `union`  D' )  ) ) )   toplevel   ->
      not (  ( MatchSubst F a p a_Bullet a_Bullet )  )  ->
     Value R a
 | Value_PathMatch : forall (R:role) (a:tm) (F:const) (p b A:tm) (R1:role) (Rs:roles) (D':available_props),
     ValuePath a F ->
      binds  F  ( (Ax p b A R1 Rs  (  (  (fv_tm_tm_tm  a )   `union`  D' )  ) ) )   toplevel   ->
     MatchSubst F a p a_Bullet a_Bullet ->
      not (  ( SubRole R1 R )  )  ->
     Value R a.

(* defns JValueType *)
Inductive value_type : role -> tm -> Prop :=    (* defn value_type *)
 | value_type_Star : forall (R:role),
     value_type R a_Star
 | value_type_Pi : forall (R:role) (rho:relflag) (A B:tm),
     lc_tm A ->
     lc_tm (a_Pi rho A B) ->
     value_type R (a_Pi rho A B)
 | value_type_CPi : forall (R:role) (phi:constraint) (B:tm),
     lc_constraint phi ->
     lc_tm (a_CPi phi B) ->
     value_type R (a_CPi phi B)
 | value_type_ValuePath : forall (R:role) (a:tm) (F:const),
     ValuePath a F ->
     value_type R a.

(* defns Jconsistent *)
Inductive consistent : tm -> tm -> role -> Prop :=    (* defn consistent *)
 | consistent_a_Star : forall (R:role),
     consistent a_Star a_Star R
 | consistent_a_Pi : forall (rho:relflag) (A1 B1 A2 B2:tm) (R':role),
     lc_tm A1 ->
     lc_tm (a_Pi rho A1 B1) ->
     lc_tm A2 ->
     lc_tm (a_Pi rho A2 B2) ->
     consistent  ( (a_Pi rho A1 B1) )   ( (a_Pi rho A2 B2) )  R'
 | consistent_a_CPi : forall (phi1:constraint) (A1:tm) (phi2:constraint) (A2:tm) (R:role),
     lc_constraint phi1 ->
     lc_tm (a_CPi phi1 A1) ->
     lc_constraint phi2 ->
     lc_tm (a_CPi phi2 A2) ->
     consistent  ( (a_CPi phi1 A1) )   ( (a_CPi phi2 A2) )  R
 | consistent_a_ValuePath : forall (a1 a2:tm) (R:role) (F:const),
     ValuePath a1 F ->
     ValuePath a2 F ->
     consistent a1 a2 R
 | consistent_a_Step_R : forall (a b:tm) (R:role),
     lc_tm a ->
      not ( value_type R b )  ->
     consistent a b R
 | consistent_a_Step_L : forall (a b:tm) (R:role),
     lc_tm b ->
      not ( value_type R a )  ->
     consistent a b R.

(* defns Jroleing *)
Inductive roleing : role_context -> tm -> role -> Prop :=    (* defn roleing *)
 | role_a_Bullet : forall (W:role_context) (R:role),
      uniq  W  ->
     roleing W a_Bullet R
 | role_a_Star : forall (W:role_context) (R:role),
      uniq  W  ->
     roleing W a_Star R
 | role_a_Var : forall (W:role_context) (x:tmvar) (R1 R:role),
      uniq  W  ->
      binds  x   R   W  ->
     SubRole R R1 ->
     roleing W (a_Var_f x) R1
 | role_a_Abs : forall (L:vars) (W:role_context) (rho:relflag) (a:tm) (R:role),
      ( forall x , x \notin  L  -> roleing  (( x  ~  Nom ) ++  W )   ( open_tm_wrt_tm a (a_Var_f x) )  R )  ->
     roleing W  ( (a_UAbs rho a) )  R
 | role_a_App : forall (W:role_context) (a:tm) (rho:relflag) (b:tm) (R:role),
     roleing W a R ->
     roleing W b Nom ->
     roleing W  ( (a_App a (Rho rho) b) )  R
 | role_a_TApp : forall (W:role_context) (a:tm) (R1:role) (b:tm) (R:role) (F:const) (Rs:roles),
     roleing W a R ->
     Path a F  ( R1 :: Rs )  ->
     roleing W b R1 ->
     roleing W (a_App a (Role R1) b) R
 | role_a_Pi : forall (L:vars) (W:role_context) (rho:relflag) (A B:tm) (R:role),
     roleing W A R ->
      ( forall x , x \notin  L  -> roleing  (( x  ~  Nom ) ++  W )   ( open_tm_wrt_tm B (a_Var_f x) )  R )  ->
     roleing W  ( (a_Pi rho A B) )  R
 | role_a_CPi : forall (L:vars) (W:role_context) (a b A:tm) (R1:role) (B:tm) (R R0:role),
     roleing W a R1 ->
     roleing W b R1 ->
     roleing W A R0 ->
      ( forall c , c \notin  L  -> roleing W  ( open_tm_wrt_co B (g_Var_f c) )  R )  ->
     roleing W  ( (a_CPi (Eq a b A R1) B) )  R
 | role_a_CAbs : forall (L:vars) (W:role_context) (b:tm) (R:role),
      ( forall c , c \notin  L  -> roleing W  ( open_tm_wrt_co b (g_Var_f c) )  R )  ->
     roleing W  ( (a_UCAbs b) )  R
 | role_a_CApp : forall (W:role_context) (a:tm) (R:role),
     roleing W a R ->
     roleing W  ( (a_CApp a g_Triv) )  R
 | role_a_Const : forall (W:role_context) (F:const) (R:role) (A:tm) (Rs:roles),
      uniq  W  ->
      binds  F  ( (Cs A Rs) )   toplevel   ->
     roleing W (a_Fam F) R
 | role_a_Fam : forall (W:role_context) (F:const) (R1:role) (p a A:tm) (R:role) (Rs:roles) (D:available_props),
      uniq  W  ->
      binds  F  ( (Ax p a A R Rs D) )   toplevel   ->
     roleing W (a_Fam F) R1
 | role_a_Pattern : forall (W:role_context) (R:role) (a:tm) (F:const) (b1 b2:tm) (R1:role),
     roleing W a R ->
     roleing W b1 R1 ->
     roleing W b2 R1 ->
     roleing W (a_Pattern R a F b1 b2) R1.

(* defns JChk *)
Inductive RhoCheck : relflag -> tmvar -> tm -> Prop :=    (* defn RhoCheck *)
 | Rho_Rel : forall (x:tmvar) (A:tm),
      True  ->
     RhoCheck Rel x A
 | Rho_IrrRel : forall (x:tmvar) (A:tm),
      ~ AtomSetImpl.In  x    (fv_tm_tm_tm  A )   ->
     RhoCheck Irrel x A.

(* defns Jpar *)
Inductive Par : role_context -> tm -> tm -> role -> Prop :=    (* defn Par *)
 | Par_Refl : forall (W:role_context) (a:tm) (R:role),
     roleing W a R ->
     Par W a a R
 | Par_Beta : forall (W:role_context) (a:tm) (rho:relflag) (b a' b':tm) (R:role),
     Par W a  ( (a_UAbs rho a') )  R ->
     Par W b b' Nom ->
     Par W (a_App a (Rho rho) b)  (open_tm_wrt_tm  a'   b' )  R
 | Par_App : forall (W:role_context) (a:tm) (rho:relflag) (b a' b':tm) (R:role),
     Par W a a' R ->
     Par W b b' Nom ->
     Par W (a_App a (Rho rho) b) (a_App a' (Rho rho) b') R
 | Par_CBeta : forall (W:role_context) (a a':tm) (R:role),
     Par W a  ( (a_UCAbs a') )  R ->
     Par W (a_CApp a g_Triv)  (open_tm_wrt_co  a'   g_Triv )  R
 | Par_CApp : forall (W:role_context) (a a':tm) (R:role),
     Par W a a' R ->
     Par W (a_CApp a g_Triv) (a_CApp a' g_Triv) R
 | Par_Abs : forall (L:vars) (W:role_context) (rho:relflag) (a a':tm) (R:role),
      ( forall x , x \notin  L  -> Par  (( x  ~  Nom ) ++  W )   ( open_tm_wrt_tm a (a_Var_f x) )   ( open_tm_wrt_tm a' (a_Var_f x) )  R )  ->
     Par W (a_UAbs rho a) (a_UAbs rho a') R
 | Par_Pi : forall (L:vars) (W:role_context) (rho:relflag) (A B A' B':tm) (R:role),
     Par W A A' R ->
      ( forall x , x \notin  L  -> Par  (( x  ~  Nom ) ++  W )   ( open_tm_wrt_tm B (a_Var_f x) )   ( open_tm_wrt_tm B' (a_Var_f x) )  R )  ->
     Par W (a_Pi rho A B) (a_Pi rho A' B') R
 | Par_CAbs : forall (L:vars) (W:role_context) (a a':tm) (R:role),
      ( forall c , c \notin  L  -> Par W  ( open_tm_wrt_co a (g_Var_f c) )   ( open_tm_wrt_co a' (g_Var_f c) )  R )  ->
     Par W (a_UCAbs a) (a_UCAbs a') R
 | Par_CPi : forall (L:vars) (W:role_context) (a b A:tm) (R1:role) (B a' b' A' B':tm) (R R0:role),
     Par W A A' R0 ->
     Par W a a' R1 ->
     Par W b b' R1 ->
      ( forall c , c \notin  L  -> Par W  ( open_tm_wrt_co B (g_Var_f c) )   ( open_tm_wrt_co B' (g_Var_f c) )  R )  ->
     Par W (a_CPi (Eq a b A R1) B) (a_CPi (Eq a' b' A' R1) B') R
 | Par_Axiom : forall (W:role_context) (a a':tm) (R:role) (F:const) (p b A:tm) (R1:role) (Rs:roles) (D':available_props),
      binds  F  ( (Ax p b A R1 Rs  (  (  (  (  (dom  W )   `union`   (fv_tm_tm_tm  p )  )  )   `union`  D' )  ) ) )   toplevel   ->
     roleing W a R ->
      uniq  W  ->
     MatchSubst F a p b a' ->
     SubRole R1 R ->
     Par W a a' R
 | Par_Pattern : forall (W:role_context) (R:role) (a:tm) (F:const) (b1 b2 a' b1' b2':tm) (R0:role),
     Par W a a' R ->
     Par W b1 b1' R0 ->
     Par W b2 b2' R0 ->
     Par W  ( (a_Pattern R a F b1 b2) )   ( (a_Pattern R a' F b1' b2') )  R0
 | Par_PatternTrue : forall (W:role_context) (R:role) (a:tm) (F:const) (b1 b2 b:tm) (R0:role) (a' b1' b2':tm),
     Par W a a' R ->
     Par W b1 b1' R0 ->
     Par W b2 b2' R0 ->
     CasePath R a' F ->
     ApplyArgs a' b1' b ->
     Par W  ( (a_Pattern R a F b1 b2) )  (a_CApp b g_Triv) R0
 | Par_PatternFalse : forall (W:role_context) (R:role) (a:tm) (F:const) (b1 b2 b2':tm) (R0:role) (a' b1':tm),
     Par W a a' R ->
     Par W b1 b1' R0 ->
     Par W b2 b2' R0 ->
     Value R a' ->
      not (  ( CasePath R a' F )  )  ->
     Par W  ( (a_Pattern R a F b1 b2) )  b2' R0
with MultiPar : role_context -> tm -> tm -> role -> Prop :=    (* defn MultiPar *)
 | MP_Refl : forall (W:role_context) (a:tm) (R:role),
     lc_tm a ->
     MultiPar W a a R
 | MP_Step : forall (W:role_context) (a a':tm) (R:role) (b:tm),
     Par W a b R ->
     MultiPar W b a' R ->
     MultiPar W a a' R
with joins : role_context -> tm -> tm -> role -> Prop :=    (* defn joins *)
 | join : forall (W:role_context) (a1 a2:tm) (R:role) (b:tm),
     MultiPar W a1 b R ->
     MultiPar W a2 b R ->
     joins W a1 a2 R.

(* defns Jbeta *)
Inductive Beta : tm -> tm -> role -> Prop :=    (* defn Beta *)
 | Beta_AppAbs : forall (rho:relflag) (v b:tm) (R1:role),
     lc_tm b ->
     Value R1  ( (a_UAbs rho v) )  ->
     Beta (a_App  ( (a_UAbs rho v) )  (Rho rho) b)  (open_tm_wrt_tm  v   b )  R1
 | Beta_CAppCAbs : forall (a':tm) (R:role),
     lc_tm (a_UCAbs a') ->
     Beta (a_CApp  ( (a_UCAbs a') )  g_Triv)  (open_tm_wrt_co  a'   g_Triv )  R
 | Beta_Axiom : forall (a b':tm) (R:role) (F:const) (p b A:tm) (R1:role) (Rs:roles) (D':available_props),
      binds  F  ( (Ax p b A R1 Rs  (  (  (  (fv_tm_tm_tm  a )  )   `union`  D' )  ) ) )   toplevel   ->
     MatchSubst F a p b b' ->
     SubRole R1 R ->
     Beta a b' R
 | Beta_PatternTrue : forall (R:role) (a:tm) (F:const) (b1 b2 b1':tm) (R0:role),
     lc_tm b2 ->
     CasePath R a F ->
     ApplyArgs a b1 b1' ->
     Beta (a_Pattern R a F b1 b2) (a_CApp b1' g_Triv) R0
 | Beta_PatternFalse : forall (R:role) (a:tm) (F:const) (b1 b2:tm) (R0:role),
     lc_tm b1 ->
     lc_tm b2 ->
     Value R a ->
      not (  ( CasePath R a F )  )  ->
     Beta (a_Pattern R a F b1 b2) b2 R0
with reduction_in_one : tm -> tm -> role -> Prop :=    (* defn reduction_in_one *)
 | E_AbsTerm : forall (L:vars) (a a':tm) (R1:role),
      ( forall x , x \notin  L  -> reduction_in_one  ( open_tm_wrt_tm a (a_Var_f x) )   ( open_tm_wrt_tm a' (a_Var_f x) )  R1 )  ->
     reduction_in_one (a_UAbs Irrel a) (a_UAbs Irrel a') R1
 | E_AppLeft : forall (a:tm) (rho:relflag) (b a':tm) (R1:role),
     lc_tm b ->
     reduction_in_one a a' R1 ->
     reduction_in_one (a_App a (Rho rho) b) (a_App a' (Rho rho) b) R1
 | E_CAppLeft : forall (a a':tm) (R:role),
     reduction_in_one a a' R ->
     reduction_in_one (a_CApp a g_Triv) (a_CApp a' g_Triv) R
 | E_Pattern : forall (R:role) (a:tm) (F:const) (b1 b2 a':tm) (R0:role),
     lc_tm b1 ->
     lc_tm b2 ->
     reduction_in_one a a' R ->
     reduction_in_one (a_Pattern R a F b1 b2) (a_Pattern R a' F b1 b2) R0
 | E_Prim : forall (a b:tm) (R:role),
     Beta a b R ->
     reduction_in_one a b R
with reduction : tm -> tm -> role -> Prop :=    (* defn reduction *)
 | Equal : forall (a:tm) (R:role),
     lc_tm a ->
     reduction a a R
 | Step : forall (a a':tm) (R:role) (b:tm),
     reduction_in_one a b R ->
     reduction b a' R ->
     reduction a a' R.

(* defns JBranchTyping *)
Inductive BranchTyping : context -> role -> tm -> tm -> tm -> tm -> tm -> tm -> Prop :=    (* defn BranchTyping *)
 | BranchTyping_Base : forall (L:vars) (G:context) (R:role) (a A b C:tm),
     lc_tm C  ->
     lc_tm a ->
     lc_tm b ->
     lc_tm A ->
     lc_tm (a_CPi  ( (Eq a b A R) )  C) ->
      uniq  G  ->
      ( forall c , c \notin  L  -> BranchTyping G R a A b A (a_CPi  ( (Eq a b A R) )  C)  ( open_tm_wrt_co C (g_Var_f c) )  ) 
 | BranchTyping_PiRel : forall (L:vars) (G:context) (R:role) (a A1 b A B C C':tm),
      ( forall x , x \notin  L  -> BranchTyping  (( x ~ Tm  A ) ++  G )  R a A1 (a_App b (Rho Rel) (a_Var_f x))  ( open_tm_wrt_tm B (a_Var_f x) )   ( open_tm_wrt_tm C (a_Var_f x) )  C' )  ->
     BranchTyping G R a A1 b (a_Pi Rel A B) (a_Pi Rel A C) C'
 | BranchTyping_PiIrrel : forall (L:vars) (G:context) (R:role) (a A1 b A B C C':tm),
      ( forall x , x \notin  L  -> BranchTyping  (( x ~ Tm  A ) ++  G )  R a A1 (a_App b (Rho Irrel) a_Bullet)  ( open_tm_wrt_tm B (a_Var_f x) )   ( open_tm_wrt_tm C (a_Var_f x) )  C' )  ->
     BranchTyping G R a A1 b (a_Pi Irrel A B) (a_Pi Irrel A C) C'
 | BranchTyping_CPi : forall (L:vars) (G:context) (R:role) (a A b:tm) (phi:constraint) (B C C':tm),
      ( forall c , c \notin  L  -> BranchTyping  (( c ~ Co  phi ) ++  G )  R a A (a_CApp b g_Triv)  ( open_tm_wrt_co B (g_Var_f c) )   ( open_tm_wrt_co C (g_Var_f c) )  C' )  ->
     BranchTyping G R a A b (a_CPi phi B) (a_CPi phi C) C'.

(* defns Jett *)
Inductive PropWff : context -> constraint -> Prop :=    (* defn PropWff *)
 | E_Wff : forall (G:context) (a b A:tm) (R:role),
     Typing G a A ->
     Typing G b A ->
      ( Typing G A a_Star )  ->
     PropWff G (Eq a b A R)
with Typing : context -> tm -> tm -> Prop :=    (* defn Typing *)
 | E_Star : forall (G:context),
     Ctx G ->
     Typing G a_Star a_Star
 | E_Var : forall (G:context) (x:tmvar) (A:tm),
     Ctx G ->
      binds  x  (Tm  A )  G  ->
     Typing G (a_Var_f x) A
 | E_Pi : forall (L:vars) (G:context) (rho:relflag) (A B:tm),
      ( forall x , x \notin  L  -> Typing  (( x ~ Tm  A ) ++  G )   ( open_tm_wrt_tm B (a_Var_f x) )  a_Star )  ->
     Typing G A a_Star ->
     Typing G (a_Pi rho A B) a_Star
 | E_Abs : forall (L:vars) (G:context) (rho:relflag) (a A B:tm),
      ( forall x , x \notin  L  -> Typing  (( x ~ Tm  A ) ++  G )   ( open_tm_wrt_tm a (a_Var_f x) )   ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
      ( Typing G A a_Star )  ->
      ( forall x , x \notin  L  -> RhoCheck rho x  ( open_tm_wrt_tm a (a_Var_f x) )  )  ->
     Typing G (a_UAbs rho a)  ( (a_Pi rho A B) ) 
 | E_App : forall (G:context) (b a B A:tm),
     Typing G b (a_Pi Rel A B) ->
     Typing G a A ->
     Typing G (a_App b (Rho Rel) a)  (open_tm_wrt_tm  B   a ) 
 | E_TApp : forall (G:context) (b:tm) (R:role) (a B A:tm) (F:const) (Rs:roles),
     Typing G b (a_Pi Rel A B) ->
     Typing G a A ->
     Path b F  ( R :: Rs )  ->
     Typing G (a_App b (Role R) a)  (open_tm_wrt_tm  B   a ) 
 | E_IApp : forall (G:context) (b B a A:tm),
     Typing G b (a_Pi Irrel A B) ->
     Typing G a A ->
     Typing G (a_App b (Rho Irrel) a_Bullet)  (open_tm_wrt_tm  B   a ) 
 | E_Conv : forall (G:context) (a B A:tm),
     Typing G a A ->
     DefEq G  (dom  G )  A B a_Star Rep ->
      ( Typing G B a_Star )  ->
     Typing G a B
 | E_CPi : forall (L:vars) (G:context) (phi:constraint) (B:tm),
      ( forall c , c \notin  L  -> Typing  (( c ~ Co  phi ) ++  G )   ( open_tm_wrt_co B (g_Var_f c) )  a_Star )  ->
      ( PropWff G phi )  ->
     Typing G (a_CPi phi B) a_Star
 | E_CAbs : forall (L:vars) (G:context) (a:tm) (phi:constraint) (B:tm),
      ( forall c , c \notin  L  -> Typing  (( c ~ Co  phi ) ++  G )   ( open_tm_wrt_co a (g_Var_f c) )   ( open_tm_wrt_co B (g_Var_f c) )  )  ->
      ( PropWff G phi )  ->
     Typing G (a_UCAbs a) (a_CPi phi B)
 | E_CApp : forall (G:context) (a1 B1 a b A:tm) (R:role),
     Typing G a1 (a_CPi  ( (Eq a b A R) )  B1) ->
     DefEq G  (dom  G )  a b A R ->
     Typing G (a_CApp a1 g_Triv)  (open_tm_wrt_co  B1   g_Triv ) 
 | E_Const : forall (G:context) (F:const) (A:tm) (Rs:roles),
     Ctx G ->
      binds  F  ( (Cs A Rs) )   toplevel   ->
     Typing  nil  A a_Star ->
     Typing G (a_Fam F) A
 | E_Fam : forall (G:context) (F:const) (A p a:tm) (R1:role) (Rs:roles) (D:available_props),
     Ctx G ->
      binds  F  ( (Ax p a A R1 Rs D) )   toplevel   ->
     Typing G (a_Fam F) A
 | E_Case : forall (G:context) (R:role) (a:tm) (F:const) (b1 b2 C A A1 B:tm),
     Typing G a A ->
     Typing G (a_Fam F) A1 ->
     Typing G b1 B ->
     Typing G b2 C ->
     BranchTyping G R a A (a_Fam F) A1 B C ->
     Typing G (a_Pattern R a F b1 b2) C
with Iso : context -> available_props -> constraint -> constraint -> Prop :=    (* defn Iso *)
 | E_PropCong : forall (G:context) (D:available_props) (A1 B1 A:tm) (R:role) (A2 B2:tm),
     DefEq G D A1 A2 A R ->
     DefEq G D B1 B2 A R ->
     Iso G D (Eq A1 B1 A R) (Eq A2 B2 A R)
 | E_IsoConv : forall (G:context) (D:available_props) (A1 A2 A:tm) (R:role) (B:tm) (R0:role),
     DefEq G D A B a_Star R0 ->
     PropWff G (Eq A1 A2 A R) ->
     PropWff G (Eq A1 A2 B R) ->
     Iso G D (Eq A1 A2 A R) (Eq A1 A2 B R)
 | E_CPiFst : forall (G:context) (D:available_props) (a1 a2 A:tm) (R1:role) (b1 b2 B:tm) (R2:role) (B1 B2:tm) (R':role),
     DefEq G D (a_CPi  ( (Eq a1 a2 A R1) )  B1) (a_CPi  ( (Eq b1 b2 B R2) )  B2) a_Star R' ->
     Iso G D (Eq a1 a2 A R1) (Eq b1 b2 B R2)
with DefEq : context -> available_props -> tm -> tm -> tm -> role -> Prop :=    (* defn DefEq *)
 | E_Assn : forall (G:context) (D:available_props) (a b A:tm) (R:role) (c:covar),
     Ctx G ->
      binds  c  (Co   ( (Eq a b A R) )  )  G  ->
      AtomSetImpl.In  c   D  ->
     DefEq G D a b A R
 | E_Refl : forall (G:context) (D:available_props) (a A:tm) (R:role),
     Typing G a A ->
     DefEq G D a a A R
 | E_Sym : forall (G:context) (D:available_props) (a b A:tm) (R:role),
     DefEq G D b a A R ->
     DefEq G D a b A R
 | E_Trans : forall (G:context) (D:available_props) (a b A:tm) (R:role) (a1:tm),
     DefEq G D a a1 A R ->
     DefEq G D a1 b A R ->
     DefEq G D a b A R
 | E_Sub : forall (G:context) (D:available_props) (a b A:tm) (R2 R1:role),
     DefEq G D a b A R1 ->
     SubRole R1 R2 ->
     DefEq G D a b A R2
 | E_Beta : forall (G:context) (D:available_props) (a1 a2 B:tm) (R:role),
     Typing G a1 B ->
      ( Typing G a2 B )  ->
     Beta a1 a2 R ->
     DefEq G D a1 a2 B R
 | E_PiCong : forall (L:vars) (G:context) (D:available_props) (rho:relflag) (A1 B1 A2 B2:tm) (R':role),
     DefEq G D A1 A2 a_Star R' ->
      ( forall x , x \notin  L  -> DefEq  (( x ~ Tm  A1 ) ++  G )  D  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  a_Star R' )  ->
      ( Typing G A1 a_Star )  ->
      ( Typing G (a_Pi rho A1 B1) a_Star )  ->
      ( Typing G (a_Pi rho A2 B2) a_Star )  ->
     DefEq G D  ( (a_Pi rho A1 B1) )   ( (a_Pi rho A2 B2) )  a_Star R'
 | E_AbsCong : forall (L:vars) (G:context) (D:available_props) (rho:relflag) (b1 b2 A1 B:tm) (R':role),
      ( forall x , x \notin  L  -> DefEq  (( x ~ Tm  A1 ) ++  G )  D  ( open_tm_wrt_tm b1 (a_Var_f x) )   ( open_tm_wrt_tm b2 (a_Var_f x) )   ( open_tm_wrt_tm B (a_Var_f x) )  R' )  ->
      ( Typing G A1 a_Star )  ->
      ( forall x , x \notin  L  -> RhoCheck rho x  ( open_tm_wrt_tm b1 (a_Var_f x) )  )  ->
      ( forall x , x \notin  L  -> RhoCheck rho x  ( open_tm_wrt_tm b2 (a_Var_f x) )  )  ->
     DefEq G D  ( (a_UAbs rho b1) )   ( (a_UAbs rho b2) )   ( (a_Pi rho A1 B) )  R'
 | E_AppCong : forall (G:context) (D:available_props) (a1 a2 b1 b2 B:tm) (R':role) (A:tm),
     DefEq G D a1 b1  ( (a_Pi Rel A B) )  R' ->
     DefEq G D a2 b2 A Nom ->
     DefEq G D (a_App a1 (Rho Rel) a2) (a_App b1 (Rho Rel) b2)  (  (open_tm_wrt_tm  B   a2 )  )  R'
 | E_TAppCong : forall (G:context) (D:available_props) (a1:tm) (R:role) (a2 b1 b2 B:tm) (R':role) (A:tm) (F:const) (Rs:roles) (F':const) (Rs':roles),
     DefEq G D a1 b1  ( (a_Pi Rel A B) )  R' ->
     DefEq G D a2 b2 A  (param R   R' )  ->
     Path a1 F  ( R :: Rs )  ->
     Path b1 F'  ( R :: Rs' )  ->
     DefEq G D (a_App a1 (Role R) a2) (a_App b1 (Role R) b2)  (  (open_tm_wrt_tm  B   a2 )  )  R'
 | E_IAppCong : forall (G:context) (D:available_props) (a1 b1 B a:tm) (R':role) (A:tm),
     DefEq G D a1 b1  ( (a_Pi Irrel A B) )  R' ->
     Typing G a A ->
     DefEq G D (a_App a1 (Rho Irrel) a_Bullet) (a_App b1 (Rho Irrel) a_Bullet)  (  (open_tm_wrt_tm  B   a )  )  R'
 | E_PiFst : forall (G:context) (D:available_props) (A1 A2:tm) (R':role) (rho:relflag) (B1 B2:tm),
     DefEq G D (a_Pi rho A1 B1) (a_Pi rho A2 B2) a_Star R' ->
     DefEq G D A1 A2 a_Star R'
 | E_PiSnd : forall (G:context) (D:available_props) (B1 a1 B2 a2:tm) (R':role) (rho:relflag) (A1 A2:tm),
     DefEq G D (a_Pi rho A1 B1) (a_Pi rho A2 B2) a_Star R' ->
     DefEq G D a1 a2 A1 R' ->
     DefEq G D  (open_tm_wrt_tm  B1   a1 )   (open_tm_wrt_tm  B2   a2 )  a_Star R'
 | E_CPiCong : forall (L:vars) (G:context) (D:available_props) (a1 b1 A1:tm) (R:role) (A a2 b2 A2 B:tm) (R':role),
     Iso G D (Eq a1 b1 A1 R) (Eq a2 b2 A2 R) ->
      ( forall c , c \notin  L  -> DefEq  (( c ~ Co  (Eq a1 b1 A1 R) ) ++  G )  D  ( open_tm_wrt_co A (g_Var_f c) )   ( open_tm_wrt_co B (g_Var_f c) )  a_Star R' )  ->
      ( PropWff G (Eq a1 b1 A1 R) )  ->
      ( Typing G (a_CPi (Eq a1 b1 A1 R) A) a_Star )  ->
      ( Typing G (a_CPi (Eq a2 b2 A2 R) B) a_Star )  ->
     DefEq G D (a_CPi (Eq a1 b1 A1 R) A) (a_CPi (Eq a2 b2 A2 R) B) a_Star R'
 | E_CAbsCong : forall (L:vars) (G:context) (D:available_props) (a b:tm) (phi1:constraint) (B:tm) (R:role),
      ( forall c , c \notin  L  -> DefEq  (( c ~ Co  phi1 ) ++  G )  D  ( open_tm_wrt_co a (g_Var_f c) )   ( open_tm_wrt_co b (g_Var_f c) )   ( open_tm_wrt_co B (g_Var_f c) )  R )  ->
      ( PropWff G phi1 )  ->
     DefEq G D  ( (a_UCAbs a) )   ( (a_UCAbs b) )  (a_CPi phi1 B) R
 | E_CAppCong : forall (G:context) (D:available_props) (a1 b1 B:tm) (R':role) (a b A:tm) (R:role),
     DefEq G D a1 b1  ( (a_CPi  ( (Eq a b A R) )  B) )  R' ->
     DefEq G  (dom  G )  a b A  (param R   R' )  ->
     DefEq G D (a_CApp a1 g_Triv) (a_CApp b1 g_Triv)  (  (open_tm_wrt_co  B   g_Triv )  )  R'
 | E_CPiSnd : forall (G:context) (D:available_props) (B1 B2:tm) (R0:role) (a1 a2 A:tm) (R:role) (a1' a2' A':tm) (R':role),
     DefEq G D (a_CPi  ( (Eq a1 a2 A R) )  B1) (a_CPi  ( (Eq a1' a2' A' R') )  B2) a_Star R0 ->
     DefEq G  (dom  G )  a1 a2 A  (param R   R0 )  ->
     DefEq G  (dom  G )  a1' a2' A'  (param R'   R0 )  ->
     DefEq G D  (open_tm_wrt_co  B1   g_Triv )   (open_tm_wrt_co  B2   g_Triv )  a_Star R0
 | E_Cast : forall (G:context) (D:available_props) (a' b' A':tm) (R':role) (a b A:tm) (R:role),
     DefEq G D a b A R ->
     Iso G D (Eq a b A R) (Eq a' b' A' R') ->
     DefEq G D a' b' A' R'
 | E_EqConv : forall (G:context) (D:available_props) (a b B:tm) (R:role) (A:tm),
     DefEq G D a b A R ->
     DefEq G  (dom  G )  A B a_Star Rep ->
      ( Typing G B a_Star )  ->
     DefEq G D a b B R
 | E_IsoSnd : forall (G:context) (D:available_props) (A A' a b:tm) (R1:role) (a' b':tm),
     Iso G D (Eq a b A R1) (Eq a' b' A' R1) ->
     DefEq G D A A' a_Star Rep
 | E_PatCong : forall (G:context) (D:available_props) (R:role) (a:tm) (F:const) (b1 b2 a' b1' b2' B:tm) (R0:role) (A:tm),
     DefEq G D a a' A R ->
     DefEq G D b1 b1' B R0 ->
     DefEq G D b2 b2' B R0 ->
     DefEq G D (a_Pattern R a F b1 b2) (a_Pattern R a' F b1' b2') B R0
 | E_LeftRel : forall (G:context) (D:available_props) (a a' A B:tm) (R':role) (F:const) (b b':tm) (R1:role),
     ValuePath a F ->
     ValuePath a' F ->
     Typing G a (a_Pi Rel A B) ->
     Typing G b A ->
     Typing G a' (a_Pi Rel A B) ->
     Typing G b' A ->
     DefEq G D (a_App a (Role R1) b) (a_App a' (Role R1) b')  (open_tm_wrt_tm  B   b )  R' ->
     DefEq G  (dom  G )   (open_tm_wrt_tm  B   b )   (open_tm_wrt_tm  B   b' )  a_Star R' ->
     DefEq G D a a' (a_Pi Rel A B) R'
 | E_LeftIrrel : forall (G:context) (D:available_props) (a a' A B:tm) (R':role) (F:const) (b b':tm) (R0:role),
     ValuePath a F ->
     ValuePath a' F ->
     Typing G a (a_Pi Irrel A B) ->
     Typing G b A ->
     Typing G a' (a_Pi Irrel A B) ->
     Typing G b' A ->
     DefEq G D (a_App a (Rho Irrel) a_Bullet) (a_App a' (Rho Irrel) a_Bullet)  (open_tm_wrt_tm  B   b )  R' ->
     DefEq G  (dom  G )   (open_tm_wrt_tm  B   b )   (open_tm_wrt_tm  B   b' )  a_Star R0 ->
     DefEq G D a a' (a_Pi Irrel A B) R'
 | E_Right : forall (G:context) (D:available_props) (b b' A:tm) (R1 R':role) (a:tm) (F:const) (a' B:tm) (R0:role),
     ValuePath a F ->
     ValuePath a' F ->
     Typing G a (a_Pi Rel A B) ->
     Typing G b A ->
     Typing G a' (a_Pi Rel A B) ->
     Typing G b' A ->
     DefEq G D (a_App a (Rho Rel) b) (a_App a' (Rho Rel) b')  (open_tm_wrt_tm  B   b )  R' ->
     DefEq G  (dom  G )   (open_tm_wrt_tm  B   b )   (open_tm_wrt_tm  B   b' )  a_Star R0 ->
     DefEq G D b b' A  (param R1   R' ) 
 | E_CLeft : forall (G:context) (D:available_props) (a a' a1 a2 A:tm) (R1:role) (B:tm) (R':role) (F:const),
     ValuePath a F ->
     ValuePath a' F ->
     Typing G a (a_CPi  ( (Eq a1 a2 A R1) )  B) ->
     Typing G a' (a_CPi  ( (Eq a1 a2 A R1) )  B) ->
     DefEq G  (dom  G )  a1 a2 A R' ->
     DefEq G D (a_CApp a g_Triv) (a_CApp a' g_Triv)  (open_tm_wrt_co  B   g_Triv )  R' ->
     DefEq G D a a' (a_CPi  ( (Eq a1 a2 A R1) )  B) R'
with Ctx : context -> Prop :=    (* defn Ctx *)
 | E_Empty : 
     Ctx  nil 
 | E_ConsTm : forall (G:context) (x:tmvar) (A:tm),
     Ctx G ->
     Typing G A a_Star ->
      ~ AtomSetImpl.In  x    (dom  G )   ->
     Ctx  (( x ~ Tm  A ) ++  G ) 
 | E_ConsCo : forall (G:context) (c:covar) (phi:constraint),
     Ctx G ->
     PropWff G phi ->
      ~ AtomSetImpl.In  c    (dom  G )   ->
     Ctx  (( c ~ Co  phi ) ++  G ) .

(* defns Jsig *)
Inductive Sig : sig -> Prop :=    (* defn Sig *)
 | Sig_Empty : 
     Sig  nil 
 | Sig_ConsConst : forall (S:sig) (F:const) (A:tm) (Rs:roles),
     Sig S ->
     Typing  nil  A a_Star ->
      ~ AtomSetImpl.In  F  (dom  S )  ->
     Sig  (( F ~ (Cs A Rs) )++ S ) 
 | Sig_ConsAx : forall (S:sig) (F:const) (p a A:tm) (R:role) (W:role_context) (G:context) (B:tm),
     Sig S ->
      ~ AtomSetImpl.In  F  (dom  S )  ->
     Typing  nil  A a_Star ->
     PatternContexts W G F A  AtomSetImpl.empty  p B ->
     Typing G a B ->
     roleing W a R ->
     Sig  (( F ~ (Ax p a A R   (range( W ))    AtomSetImpl.empty ) )++ S ) 
 | Sig_ConsExcl : forall (S:sig) (F:const) (p' a' A:tm) (R:role) (W:role_context) (D:available_props) (p a:tm) (Rs:roles) (G:context) (B':tm),
      binds  F  ( (Ax p a A R Rs  AtomSetImpl.empty ) )  S  ->
     PatternContexts W G F A D p' B' ->
     Typing G a' B' ->
     roleing W a' R ->
     Sig  (( F ~ (Ax p' a' A R   (range( W ))   D) )++ S ) .

(* defns Jann *)
Inductive AnnPropWff : context -> constraint -> Prop :=    (* defn AnnPropWff *)
with AnnTyping : context -> tm -> tm -> role -> Prop :=    (* defn AnnTyping *)
with AnnIso : context -> available_props -> co -> constraint -> constraint -> Prop :=    (* defn AnnIso *)
with AnnDefEq : context -> available_props -> co -> tm -> tm -> role -> Prop :=    (* defn AnnDefEq *)
with AnnCtx : context -> Prop :=    (* defn AnnCtx *).

(* defns Jred *)
Inductive head_reduction : context -> tm -> tm -> role -> Prop :=    (* defn head_reduction *).


(** infrastructure *)
Hint Constructors SubRole Path CasePath ValuePath PatternContexts MatchSubst ApplyArgs Value value_type consistent roleing RhoCheck Par MultiPar joins Beta reduction_in_one reduction BranchTyping PropWff Typing Iso DefEq Ctx Sig AnnPropWff AnnTyping AnnIso AnnDefEq AnnCtx head_reduction lc_co lc_brs lc_tm lc_constraint lc_sort lc_sig_sort.


