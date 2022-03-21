Require Import Bool.
Require Import Metalib.Metatheory.
Require Export FcEtt.grade_sig.

(** syntax *)
Definition tmvar : Set := var. (*r variables *)
Definition covar : Set := var. (*r coercion variables *)
Definition datacon : Set := atom.
Definition const : Set := atom.
Definition tyfam : Set := atom.
Definition index : Set := nat. (*r indices *)

Definition grade : Set := grade.

Inductive constraint : Set :=  (*r props *)
 | Eq (a:tm) (b:tm) (A:tm)
 | Impl (phi1:constraint) (phi2:constraint)
with tm : Set :=  (*r types and kinds *)
 | a_Star : tm
 | a_Var_b (_:nat)
 | a_Var_f (x:tmvar)
 | a_Abs (psi:grade) (A:tm) (b:tm)
 | a_UAbs (psi:grade) (b:tm)
 | a_App (a:tm) (psi:grade) (b:tm)
 | a_Fam (F:tyfam)
 | a_Const (T:const)
 | a_Pi (psi:grade) (A:tm) (B:tm)
 | a_Conv (a:tm) (g:co)
 | a_CPi (psi:grade) (phi:constraint) (B:tm)
 | a_CAbs (psi:grade) (phi:constraint) (b:tm)
 | a_UCAbs (psi:grade) (b:tm)
 | a_CApp (a:tm) (g:co)
 | a_DataCon (K:datacon)
 | a_Case (a:tm) (brs5:brs)
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
 | g_PiCong (psi:grade) (g1:co) (g2:co)
 | g_AbsCong (psi:grade) (g1:co) (g2:co)
 | g_AppCong (g1:co) (psi:grade) (g2:co)
 | g_PiFst (g:co)
 | g_CPiFst (g:co)
 | g_IsoSnd (g:co)
 | g_PiSnd (g1:co) (g2:co)
 | g_CPiCong (g1:co) (g3:co)
 | g_CAbsCong (psi:grade) (g1:co) (g3:co) (g4:co)
 | g_CAppCong (g:co) (g1:co) (g2:co)
 | g_CPiSnd (g:co) (g1:co) (g2:co)
 | g_Cast (g1:co) (g2:co)
 | g_EqCong (g1:co) (A:tm) (g2:co)
 | g_IsoConv (phi1:constraint) (phi2:constraint) (g:co)
 | g_Eta (a:tm)
 | g_Left (g:co) (g':co)
 | g_Right (g:co) (g':co).

Inductive sig_sort : Set :=  (*r signature classifier *)
 | Cs (A:tm)
 | Ax (a:tm) (A:tm).

Inductive sort : Set :=  (*r binding classifier *)
 | Tm (A:tm)
 | Co (phi:constraint).

Inductive esort : Set :=  (*r binding classifier *)
 | e_Tm : esort
 | e_Co : esort.

Definition sig : Set := list (atom * (grade * sig_sort)).

Definition context : Set := list ( atom * (grade * sort) ).

Definition econtext : Set := list ( atom * (grade * esort) ).

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
  | (g_PiCong psi g1 g2) => g_PiCong psi (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_AbsCong psi g1 g2) => g_AbsCong psi (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_AppCong g1 psi g2) => g_AppCong (open_co_wrt_co_rec k g_5 g1) psi (open_co_wrt_co_rec k g_5 g2)
  | (g_PiFst g) => g_PiFst (open_co_wrt_co_rec k g_5 g)
  | (g_CPiFst g) => g_CPiFst (open_co_wrt_co_rec k g_5 g)
  | (g_IsoSnd g) => g_IsoSnd (open_co_wrt_co_rec k g_5 g)
  | (g_PiSnd g1 g2) => g_PiSnd (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_CPiCong g1 g3) => g_CPiCong (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec (S k) g_5 g3)
  | (g_CAbsCong psi g1 g3 g4) => g_CAbsCong psi (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec (S k) g_5 g3) (open_co_wrt_co_rec k g_5 g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (open_co_wrt_co_rec k g_5 g) (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (open_co_wrt_co_rec k g_5 g) (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
  | (g_Cast g1 g2) => g_Cast (open_co_wrt_co_rec k g_5 g1) (open_co_wrt_co_rec k g_5 g2)
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
  | (a_Abs psi A b) => a_Abs psi (open_tm_wrt_co_rec k g5 A) (open_tm_wrt_co_rec k g5 b)
  | (a_UAbs psi b) => a_UAbs psi (open_tm_wrt_co_rec k g5 b)
  | (a_App a psi b) => a_App (open_tm_wrt_co_rec k g5 a) psi (open_tm_wrt_co_rec k g5 b)
  | (a_Fam F) => a_Fam F
  | (a_Const T) => a_Const T
  | (a_Pi psi A B) => a_Pi psi (open_tm_wrt_co_rec k g5 A) (open_tm_wrt_co_rec k g5 B)
  | (a_Conv a g) => a_Conv (open_tm_wrt_co_rec k g5 a) (open_co_wrt_co_rec k g5 g)
  | (a_CPi psi phi B) => a_CPi psi (open_constraint_wrt_co_rec k g5 phi) (open_tm_wrt_co_rec (S k) g5 B)
  | (a_CAbs psi phi b) => a_CAbs psi (open_constraint_wrt_co_rec k g5 phi) (open_tm_wrt_co_rec (S k) g5 b)
  | (a_UCAbs psi b) => a_UCAbs psi (open_tm_wrt_co_rec (S k) g5 b)
  | (a_CApp a g) => a_CApp (open_tm_wrt_co_rec k g5 a) (open_co_wrt_co_rec k g5 g)
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (open_tm_wrt_co_rec k g5 a) (open_brs_wrt_co_rec k g5 brs5)
end
with open_constraint_wrt_co_rec (k:nat) (g5:co) (phi_5:constraint) {struct phi_5}: constraint :=
  match phi_5 with
  | (Eq a b A) => Eq (open_tm_wrt_co_rec k g5 a) (open_tm_wrt_co_rec k g5 b) (open_tm_wrt_co_rec k g5 A)
  | (Impl phi1 phi2) => Impl (open_constraint_wrt_co_rec k g5 phi1) (open_constraint_wrt_co_rec k g5 phi2)
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
  | (g_PiCong psi g1 g2) => g_PiCong psi (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec (S k) a5 g2)
  | (g_AbsCong psi g1 g2) => g_AbsCong psi (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec (S k) a5 g2)
  | (g_AppCong g1 psi g2) => g_AppCong (open_co_wrt_tm_rec k a5 g1) psi (open_co_wrt_tm_rec k a5 g2)
  | (g_PiFst g) => g_PiFst (open_co_wrt_tm_rec k a5 g)
  | (g_CPiFst g) => g_CPiFst (open_co_wrt_tm_rec k a5 g)
  | (g_IsoSnd g) => g_IsoSnd (open_co_wrt_tm_rec k a5 g)
  | (g_PiSnd g1 g2) => g_PiSnd (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g2)
  | (g_CPiCong g1 g3) => g_CPiCong (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g3)
  | (g_CAbsCong psi g1 g3 g4) => g_CAbsCong psi (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g3) (open_co_wrt_tm_rec k a5 g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (open_co_wrt_tm_rec k a5 g) (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (open_co_wrt_tm_rec k a5 g) (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g2)
  | (g_Cast g1 g2) => g_Cast (open_co_wrt_tm_rec k a5 g1) (open_co_wrt_tm_rec k a5 g2)
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
  | (a_Abs psi A b) => a_Abs psi (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 b)
  | (a_UAbs psi b) => a_UAbs psi (open_tm_wrt_tm_rec (S k) a5 b)
  | (a_App a psi b) => a_App (open_tm_wrt_tm_rec k a5 a) psi (open_tm_wrt_tm_rec k a5 b)
  | (a_Fam F) => a_Fam F
  | (a_Const T) => a_Const T
  | (a_Pi psi A B) => a_Pi psi (open_tm_wrt_tm_rec k a5 A) (open_tm_wrt_tm_rec (S k) a5 B)
  | (a_Conv a g) => a_Conv (open_tm_wrt_tm_rec k a5 a) (open_co_wrt_tm_rec k a5 g)
  | (a_CPi psi phi B) => a_CPi psi (open_constraint_wrt_tm_rec k a5 phi) (open_tm_wrt_tm_rec k a5 B)
  | (a_CAbs psi phi b) => a_CAbs psi (open_constraint_wrt_tm_rec k a5 phi) (open_tm_wrt_tm_rec k a5 b)
  | (a_UCAbs psi b) => a_UCAbs psi (open_tm_wrt_tm_rec k a5 b)
  | (a_CApp a g) => a_CApp (open_tm_wrt_tm_rec k a5 a) (open_co_wrt_tm_rec k a5 g)
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (open_tm_wrt_tm_rec k a5 a) (open_brs_wrt_tm_rec k a5 brs5)
end
with open_constraint_wrt_tm_rec (k:nat) (a5:tm) (phi_5:constraint) {struct phi_5}: constraint :=
  match phi_5 with
  | (Eq a b A) => Eq (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 b) (open_tm_wrt_tm_rec k a5 A)
  | (Impl phi1 phi2) => Impl (open_constraint_wrt_tm_rec k a5 phi1) (open_constraint_wrt_tm_rec k a5 phi2)
end.

Definition open_sort_wrt_co_rec (k:nat) (g5:co) (sort5:sort) : sort :=
  match sort5 with
  | (Tm A) => Tm (open_tm_wrt_co_rec k g5 A)
  | (Co phi) => Co (open_constraint_wrt_co_rec k g5 phi)
end.

Definition open_sig_sort_wrt_co_rec (k:nat) (g5:co) (sig_sort5:sig_sort) : sig_sort :=
  match sig_sort5 with
  | (Cs A) => Cs (open_tm_wrt_co_rec k g5 A)
  | (Ax a A) => Ax (open_tm_wrt_co_rec k g5 a) (open_tm_wrt_co_rec k g5 A)
end.

Definition open_sig_sort_wrt_tm_rec (k:nat) (a5:tm) (sig_sort5:sig_sort) : sig_sort :=
  match sig_sort5 with
  | (Cs A) => Cs (open_tm_wrt_tm_rec k a5 A)
  | (Ax a A) => Ax (open_tm_wrt_tm_rec k a5 a) (open_tm_wrt_tm_rec k a5 A)
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

Definition open_constraint_wrt_co g5 phi_5 := open_constraint_wrt_co_rec 0 phi_5 g5.

Definition open_constraint_wrt_tm a5 phi_5 := open_constraint_wrt_tm_rec 0 phi_5 a5.

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
 | lc_g_PiCong : forall (psi:grade) (g1 g2:co),
     (lc_co g1) ->
      ( forall x , lc_co  ( open_co_wrt_tm g2 (a_Var_f x) )  )  ->
     (lc_co (g_PiCong psi g1 g2))
 | lc_g_AbsCong : forall (psi:grade) (g1 g2:co),
     (lc_co g1) ->
      ( forall x , lc_co  ( open_co_wrt_tm g2 (a_Var_f x) )  )  ->
     (lc_co (g_AbsCong psi g1 g2))
 | lc_g_AppCong : forall (g1:co) (psi:grade) (g2:co),
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_AppCong g1 psi g2))
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
 | lc_g_CAbsCong : forall (psi:grade) (g1 g3 g4:co),
     (lc_co g1) ->
      ( forall c , lc_co  ( open_co_wrt_co g3 (g_Var_f c) )  )  ->
     (lc_co g4) ->
     (lc_co (g_CAbsCong psi g1 g3 g4))
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
 | lc_g_Cast : forall (g1 g2:co),
     (lc_co g1) ->
     (lc_co g2) ->
     (lc_co (g_Cast g1 g2))
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
 | lc_a_Abs : forall (psi:grade) (A b:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     (lc_tm (a_Abs psi A b))
 | lc_a_UAbs : forall (psi:grade) (b:tm),
      ( forall x , lc_tm  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     (lc_tm (a_UAbs psi b))
 | lc_a_App : forall (a:tm) (psi:grade) (b:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm (a_App a psi b))
 | lc_a_Fam : forall (F:tyfam),
     (lc_tm (a_Fam F))
 | lc_a_Const : forall (T:const),
     (lc_tm (a_Const T))
 | lc_a_Pi : forall (psi:grade) (A B:tm),
     (lc_tm A) ->
      ( forall x , lc_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     (lc_tm (a_Pi psi A B))
 | lc_a_Conv : forall (a:tm) (g:co),
     (lc_tm a) ->
     (lc_co g) ->
     (lc_tm (a_Conv a g))
 | lc_a_CPi : forall (psi:grade) (phi:constraint) (B:tm),
     (lc_constraint phi) ->
      ( forall c , lc_tm  ( open_tm_wrt_co B (g_Var_f c) )  )  ->
     (lc_tm (a_CPi psi phi B))
 | lc_a_CAbs : forall (psi:grade) (phi:constraint) (b:tm),
     (lc_constraint phi) ->
      ( forall c , lc_tm  ( open_tm_wrt_co b (g_Var_f c) )  )  ->
     (lc_tm (a_CAbs psi phi b))
 | lc_a_UCAbs : forall (psi:grade) (b:tm),
      ( forall c , lc_tm  ( open_tm_wrt_co b (g_Var_f c) )  )  ->
     (lc_tm (a_UCAbs psi b))
 | lc_a_CApp : forall (a:tm) (g:co),
     (lc_tm a) ->
     (lc_co g) ->
     (lc_tm (a_CApp a g))
 | lc_a_DataCon : forall (K:datacon),
     (lc_tm (a_DataCon K))
 | lc_a_Case : forall (a:tm) (brs5:brs),
     (lc_tm a) ->
     (lc_brs brs5) ->
     (lc_tm (a_Case a brs5))
with lc_constraint : constraint -> Prop :=    (* defn lc_constraint *)
 | lc_Eq : forall (a b A:tm),
     (lc_tm a) ->
     (lc_tm b) ->
     (lc_tm A) ->
     (lc_constraint (Eq a b A))
 | lc_Impl : forall (phi1 phi2:constraint),
     (lc_constraint phi1) ->
     (lc_constraint phi2) ->
     (lc_constraint (Impl phi1 phi2)).

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
 | lc_Cs : forall (A:tm),
     (lc_tm A) ->
     (lc_sig_sort (Cs A))
 | lc_Ax : forall (a A:tm),
     (lc_tm a) ->
     (lc_tm A) ->
     (lc_sig_sort (Ax a A)).
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
  | (g_PiCong psi g1 g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_AbsCong psi g1 g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_AppCong g1 psi g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_PiFst g) => (fv_tm_tm_co g)
  | (g_CPiFst g) => (fv_tm_tm_co g)
  | (g_IsoSnd g) => (fv_tm_tm_co g)
  | (g_PiSnd g1 g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_CPiCong g1 g3) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g3)
  | (g_CAbsCong psi g1 g3 g4) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g3) \u (fv_tm_tm_co g4)
  | (g_CAppCong g g1 g2) => (fv_tm_tm_co g) \u (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_CPiSnd g g1 g2) => (fv_tm_tm_co g) \u (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
  | (g_Cast g1 g2) => (fv_tm_tm_co g1) \u (fv_tm_tm_co g2)
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
  | (a_Abs psi A b) => (fv_tm_tm_tm A) \u (fv_tm_tm_tm b)
  | (a_UAbs psi b) => (fv_tm_tm_tm b)
  | (a_App a psi b) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm b)
  | (a_Fam F) => {}
  | (a_Const T) => {}
  | (a_Pi psi A B) => (fv_tm_tm_tm A) \u (fv_tm_tm_tm B)
  | (a_Conv a g) => (fv_tm_tm_tm a) \u (fv_tm_tm_co g)
  | (a_CPi psi phi B) => (fv_tm_tm_constraint phi) \u (fv_tm_tm_tm B)
  | (a_CAbs psi phi b) => (fv_tm_tm_constraint phi) \u (fv_tm_tm_tm b)
  | (a_UCAbs psi b) => (fv_tm_tm_tm b)
  | (a_CApp a g) => (fv_tm_tm_tm a) \u (fv_tm_tm_co g)
  | (a_DataCon K) => {}
  | (a_Case a brs5) => (fv_tm_tm_tm a) \u (fv_tm_tm_brs brs5)
end
with fv_tm_tm_constraint (phi_5:constraint) : vars :=
  match phi_5 with
  | (Eq a b A) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm b) \u (fv_tm_tm_tm A)
  | (Impl phi1 phi2) => (fv_tm_tm_constraint phi1) \u (fv_tm_tm_constraint phi2)
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
  | (g_PiCong psi g1 g2) => (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_AbsCong psi g1 g2) => (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_AppCong g1 psi g2) => (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_PiFst g) => (fv_co_co_co g)
  | (g_CPiFst g) => (fv_co_co_co g)
  | (g_IsoSnd g) => (fv_co_co_co g)
  | (g_PiSnd g1 g2) => (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_CPiCong g1 g3) => (fv_co_co_co g1) \u (fv_co_co_co g3)
  | (g_CAbsCong psi g1 g3 g4) => (fv_co_co_co g1) \u (fv_co_co_co g3) \u (fv_co_co_co g4)
  | (g_CAppCong g g1 g2) => (fv_co_co_co g) \u (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_CPiSnd g g1 g2) => (fv_co_co_co g) \u (fv_co_co_co g1) \u (fv_co_co_co g2)
  | (g_Cast g1 g2) => (fv_co_co_co g1) \u (fv_co_co_co g2)
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
  | (a_Abs psi A b) => (fv_co_co_tm A) \u (fv_co_co_tm b)
  | (a_UAbs psi b) => (fv_co_co_tm b)
  | (a_App a psi b) => (fv_co_co_tm a) \u (fv_co_co_tm b)
  | (a_Fam F) => {}
  | (a_Const T) => {}
  | (a_Pi psi A B) => (fv_co_co_tm A) \u (fv_co_co_tm B)
  | (a_Conv a g) => (fv_co_co_tm a) \u (fv_co_co_co g)
  | (a_CPi psi phi B) => (fv_co_co_constraint phi) \u (fv_co_co_tm B)
  | (a_CAbs psi phi b) => (fv_co_co_constraint phi) \u (fv_co_co_tm b)
  | (a_UCAbs psi b) => (fv_co_co_tm b)
  | (a_CApp a g) => (fv_co_co_tm a) \u (fv_co_co_co g)
  | (a_DataCon K) => {}
  | (a_Case a brs5) => (fv_co_co_tm a) \u (fv_co_co_brs brs5)
end
with fv_co_co_constraint (phi_5:constraint) : vars :=
  match phi_5 with
  | (Eq a b A) => (fv_co_co_tm a) \u (fv_co_co_tm b) \u (fv_co_co_tm A)
  | (Impl phi1 phi2) => (fv_co_co_constraint phi1) \u (fv_co_co_constraint phi2)
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
  | (Cs A) => (fv_tm_tm_tm A)
  | (Ax a A) => (fv_tm_tm_tm a) \u (fv_tm_tm_tm A)
end.

Definition fv_co_co_sig_sort (sig_sort5:sig_sort) : vars :=
  match sig_sort5 with
  | (Cs A) => (fv_co_co_tm A)
  | (Ax a A) => (fv_co_co_tm a) \u (fv_co_co_tm A)
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
  | (g_PiCong psi g1 g2) => g_PiCong psi (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_AbsCong psi g1 g2) => g_AbsCong psi (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_AppCong g1 psi g2) => g_AppCong (tm_subst_tm_co a5 x5 g1) psi (tm_subst_tm_co a5 x5 g2)
  | (g_PiFst g) => g_PiFst (tm_subst_tm_co a5 x5 g)
  | (g_CPiFst g) => g_CPiFst (tm_subst_tm_co a5 x5 g)
  | (g_IsoSnd g) => g_IsoSnd (tm_subst_tm_co a5 x5 g)
  | (g_PiSnd g1 g2) => g_PiSnd (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_CPiCong g1 g3) => g_CPiCong (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g3)
  | (g_CAbsCong psi g1 g3 g4) => g_CAbsCong psi (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g3) (tm_subst_tm_co a5 x5 g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (tm_subst_tm_co a5 x5 g) (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (tm_subst_tm_co a5 x5 g) (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
  | (g_Cast g1 g2) => g_Cast (tm_subst_tm_co a5 x5 g1) (tm_subst_tm_co a5 x5 g2)
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
  | (a_Abs psi A b) => a_Abs psi (tm_subst_tm_tm a5 x5 A) (tm_subst_tm_tm a5 x5 b)
  | (a_UAbs psi b) => a_UAbs psi (tm_subst_tm_tm a5 x5 b)
  | (a_App a psi b) => a_App (tm_subst_tm_tm a5 x5 a) psi (tm_subst_tm_tm a5 x5 b)
  | (a_Fam F) => a_Fam F
  | (a_Const T) => a_Const T
  | (a_Pi psi A B) => a_Pi psi (tm_subst_tm_tm a5 x5 A) (tm_subst_tm_tm a5 x5 B)
  | (a_Conv a g) => a_Conv (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_co a5 x5 g)
  | (a_CPi psi phi B) => a_CPi psi (tm_subst_tm_constraint a5 x5 phi) (tm_subst_tm_tm a5 x5 B)
  | (a_CAbs psi phi b) => a_CAbs psi (tm_subst_tm_constraint a5 x5 phi) (tm_subst_tm_tm a5 x5 b)
  | (a_UCAbs psi b) => a_UCAbs psi (tm_subst_tm_tm a5 x5 b)
  | (a_CApp a g) => a_CApp (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_co a5 x5 g)
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_brs a5 x5 brs5)
end
with tm_subst_tm_constraint (a5:tm) (x5:tmvar) (phi_5:constraint) {struct phi_5} : constraint :=
  match phi_5 with
  | (Eq a b A) => Eq (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_tm a5 x5 b) (tm_subst_tm_tm a5 x5 A)
  | (Impl phi1 phi2) => Impl (tm_subst_tm_constraint a5 x5 phi1) (tm_subst_tm_constraint a5 x5 phi2)
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
  | (g_PiCong psi g1 g2) => g_PiCong psi (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g2)
  | (g_AbsCong psi g1 g2) => g_AbsCong psi (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g2)
  | (g_AppCong g1 psi g2) => g_AppCong (co_subst_co_co g_5 c5 g1) psi (co_subst_co_co g_5 c5 g2)
  | (g_PiFst g) => g_PiFst (co_subst_co_co g_5 c5 g)
  | (g_CPiFst g) => g_CPiFst (co_subst_co_co g_5 c5 g)
  | (g_IsoSnd g) => g_IsoSnd (co_subst_co_co g_5 c5 g)
  | (g_PiSnd g1 g2) => g_PiSnd (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g2)
  | (g_CPiCong g1 g3) => g_CPiCong (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g3)
  | (g_CAbsCong psi g1 g3 g4) => g_CAbsCong psi (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g3) (co_subst_co_co g_5 c5 g4)
  | (g_CAppCong g g1 g2) => g_CAppCong (co_subst_co_co g_5 c5 g) (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g2)
  | (g_CPiSnd g g1 g2) => g_CPiSnd (co_subst_co_co g_5 c5 g) (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g2)
  | (g_Cast g1 g2) => g_Cast (co_subst_co_co g_5 c5 g1) (co_subst_co_co g_5 c5 g2)
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
  | (a_Abs psi A b) => a_Abs psi (co_subst_co_tm g5 c5 A) (co_subst_co_tm g5 c5 b)
  | (a_UAbs psi b) => a_UAbs psi (co_subst_co_tm g5 c5 b)
  | (a_App a psi b) => a_App (co_subst_co_tm g5 c5 a) psi (co_subst_co_tm g5 c5 b)
  | (a_Fam F) => a_Fam F
  | (a_Const T) => a_Const T
  | (a_Pi psi A B) => a_Pi psi (co_subst_co_tm g5 c5 A) (co_subst_co_tm g5 c5 B)
  | (a_Conv a g) => a_Conv (co_subst_co_tm g5 c5 a) (co_subst_co_co g5 c5 g)
  | (a_CPi psi phi B) => a_CPi psi (co_subst_co_constraint g5 c5 phi) (co_subst_co_tm g5 c5 B)
  | (a_CAbs psi phi b) => a_CAbs psi (co_subst_co_constraint g5 c5 phi) (co_subst_co_tm g5 c5 b)
  | (a_UCAbs psi b) => a_UCAbs psi (co_subst_co_tm g5 c5 b)
  | (a_CApp a g) => a_CApp (co_subst_co_tm g5 c5 a) (co_subst_co_co g5 c5 g)
  | (a_DataCon K) => a_DataCon K
  | (a_Case a brs5) => a_Case (co_subst_co_tm g5 c5 a) (co_subst_co_brs g5 c5 brs5)
end
with co_subst_co_constraint (g5:co) (c5:covar) (phi_5:constraint) {struct phi_5} : constraint :=
  match phi_5 with
  | (Eq a b A) => Eq (co_subst_co_tm g5 c5 a) (co_subst_co_tm g5 c5 b) (co_subst_co_tm g5 c5 A)
  | (Impl phi1 phi2) => Impl (co_subst_co_constraint g5 c5 phi1) (co_subst_co_constraint g5 c5 phi2)
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
  | (Cs A) => Cs (tm_subst_tm_tm a5 x5 A)
  | (Ax a A) => Ax (tm_subst_tm_tm a5 x5 a) (tm_subst_tm_tm a5 x5 A)
end.

Definition co_subst_co_sig_sort (g5:co) (c5:covar) (sig_sort5:sig_sort) : sig_sort :=
  match sig_sort5 with
  | (Cs A) => Cs (co_subst_co_tm g5 c5 A)
  | (Ax a A) => Ax (co_subst_co_tm g5 c5 a) (co_subst_co_tm g5 c5 A)
end.

Local Open Scope grade_scope.

Definition sort_to_esort (s:sort) : esort :=
  match s with
  | Tm _ => e_Tm
  | Co _ => e_Co
  end.

Definition labels : context -> econtext :=
  map (fun '(u , s) => (u , sort_to_esort s)).

Definition subst_ctx (a : tm) (x:var) : context -> context :=
  map (fun '(g, A) => (g, (tm_subst_tm_sort a x A))).

Definition join_ctx_l (psi : grade) : context -> context :=    
  map (fun '(g, A) => (psi * g, A)).

Definition join_ctx_r (psi : grade) : context -> context :=
  map (fun '(g, A) => (g * psi, A)).

Definition meet_ctx_l (psi : grade) : context -> context :=
  map (fun '(g, A) => (psi + g, A)).

Definition meet_ctx_r (psi : grade) : context -> context :=
  map (fun '(g, A) => (g + psi, A)).

Fixpoint erase_tm (a : tm) : tm :=
   match a with
   | a_Star    => a_Star
   | a_Var_b n => a_Var_b n
   | a_Var_f x => a_Var_f x
   | a_Abs rho A b => a_UAbs rho (erase_tm b)
   | a_UAbs rho b => a_UAbs rho (erase_tm b)
   | a_App a psi0 b => a_App (erase_tm a) psi0 (erase_tm b)
   | a_Const T => a_Const T
   | a_Fam F => a_Fam F
   | a_Pi rho A B => a_Pi rho (erase_tm A) (erase_tm B)
   | a_Conv a _ => erase_tm a
   | a_CPi psi0 phi B => a_CPi psi0 (erase_constraint phi) (erase_tm B)
   | a_CAbs psi0 phi b => a_UCAbs psi0 (erase_tm b)
   | a_UCAbs psi0 b => a_UCAbs psi0 (erase_tm b)
   | a_CApp a g => a_CApp (erase_tm a) g_Triv
   | a_DataCon K => a_Star  (* a_DataCon K *)
   | a_Case a brs => a_Star (* a_Case (erase_tm a) (erase_brs brs) *)
   end
with erase_brs (x : brs) : brs :=
   match x with
   | br_None => br_None
   | br_One k a y => br_One k (erase_tm a) (erase_brs y)
   end
with erase_constraint (phi : constraint) : constraint :=
   match phi with
   | Eq A B A1 => Eq (erase_tm A) (erase_tm B) (erase_tm A1)
   | Impl phi1 phi2 => Impl (erase_constraint phi1) (erase_constraint phi2)
   end.

Definition erase_sort s :=
 match s with
 | Tm a => Tm (erase_tm a)
 | Co p => Co (erase_constraint p)
end.


Definition erase_csort s :=
 match s with
 | Cs a   => Cs (erase_tm a)
 | Ax a A => Ax (erase_tm a) (erase_tm A)
end.

Definition erase_context (G : context) := map (fun '(psi, s) => (psi, erase_sort s)) G.
Definition erase_sig (S : sig) := map (fun '(psi, s) => (psi, erase_csort s)) S.

(* -------------- A specific signature with Fix ------------ *)
Definition Fix : atom.
  pick fresh F.
  exact F.
Qed.

Definition FixDef : tm :=
  (a_Abs q_C a_Star
         (a_Abs q_R (a_Pi q_R (a_Var_b 0) (a_Var_b 1))
                (a_App (a_Var_b 0) q_R
                       (a_App (a_App (a_Fam Fix) q_C (a_Var_b 1)) q_R (a_Var_b 0))))).

Definition FixTy : tm :=
  a_Pi q_C a_Star
       (a_Pi q_R (a_Pi q_R (a_Var_b 0) (a_Var_b 1))
             (a_Var_b 1)).


Definition an_toplevel : sig := Fix ~ (q_R, Ax FixDef FixTy).

Definition toplevel : sig := erase_sig an_toplevel.



(** definitions *)

(* defns JValue *)
Inductive CoercedValue : tm -> Prop :=    (* defn CoercedValue *)
 | CV : forall (a:tm),
     Value a ->
     CoercedValue a
 | CC : forall (a:tm) (g:co),
     lc_co g ->
     Value a ->
     CoercedValue  ( (a_Conv a g) ) 
with Value : tm -> Prop :=    (* defn Value *)
 | Value_Star : 
     Value a_Star
 | Value_Pi : forall (psi:grade) (A B:tm),
     lc_tm A ->
     lc_tm (a_Pi psi A B) ->
     Value (a_Pi psi A B)
 | Value_CPi : forall (psi:grade) (phi:constraint) (B:tm),
     lc_constraint phi ->
     lc_tm (a_CPi psi phi B) ->
     Value (a_CPi psi phi B)
 | Value_Abs : forall (psi:grade) (A a:tm),
     lc_tm A ->
     lc_tm (a_Abs psi A a) ->
     Value (a_Abs psi A a)
 | Value_UAbs : forall (psi:grade) (a:tm),
     lc_tm (a_UAbs psi a) ->
     Value (a_UAbs psi a)
 | Value_CAbs : forall (psi:grade) (phi:constraint) (a:tm),
     lc_constraint phi ->
     lc_tm (a_CAbs psi phi a) ->
     Value (a_CAbs psi phi a)
 | Value_UCAbs : forall (psi:grade) (a:tm),
     lc_tm (a_UCAbs psi a) ->
     Value (a_UCAbs psi a)
with value_type : tm -> Prop :=    (* defn value_type *)
 | value_type_Star : 
     value_type a_Star
 | value_type_Pi : forall (psi:grade) (A B:tm),
     lc_tm A ->
     lc_tm (a_Pi psi A B) ->
     value_type (a_Pi psi A B)
 | value_type_CPi : forall (psi:grade) (phi:constraint) (B:tm),
     lc_constraint phi ->
     lc_tm (a_CPi psi phi B) ->
     value_type (a_CPi psi phi B).

(* defns Jconsistent *)
Inductive consistent : tm -> tm -> Prop :=    (* defn consistent *)
 | consistent_a_Star : 
     consistent a_Star a_Star
 | consistent_a_Pi : forall (psi1:grade) (A1 B1:tm) (psi2:grade) (A2 B2:tm),
     lc_tm A1 ->
     lc_tm (a_Pi psi1 A1 B1) ->
     lc_tm A2 ->
     lc_tm (a_Pi psi2 A2 B2) ->
     consistent  ( (a_Pi psi1 A1 B1) )   ( (a_Pi psi2 A2 B2) ) 
 | consistent_a_CPi : forall (psi1:grade) (phi1:constraint) (A1:tm) (psi2:grade) (phi2:constraint) (A2:tm),
     lc_constraint phi1 ->
     lc_tm (a_CPi psi1 phi1 A1) ->
     lc_constraint phi2 ->
     lc_tm (a_CPi psi2 phi2 A2) ->
     consistent  ( (a_CPi psi1 phi1 A1) )   ( (a_CPi psi2 phi2 A2) ) 
 | consistent_a_Step_R : forall (a b:tm),
     lc_tm a ->
      not ( value_type b )  ->
     consistent a b
 | consistent_a_Step_L : forall (a b:tm),
     lc_tm b ->
      not ( value_type a )  ->
     consistent a b.

(* defns Jerased *)
Inductive erased_constraint : constraint -> Prop :=    (* defn erased_constraint *)
 | erased_c_Eq : forall (a b A:tm),
     erased_tm a ->
     erased_tm b ->
     erased_tm A ->
     erased_constraint (Eq a b A)
 | erased_c_Impl : forall (phi1 phi2:constraint),
     erased_constraint phi1 ->
     erased_constraint phi2 ->
     erased_constraint (Impl phi1 phi2)
with erased_tm : tm -> Prop :=    (* defn erased_tm *)
 | erased_a_Star : 
     erased_tm a_Star
 | erased_a_Var : forall (x:tmvar),
     erased_tm (a_Var_f x)
 | erased_a_Abs : forall (L:vars) (psi:grade) (a:tm),
      ( forall x , x \notin  L  -> erased_tm  ( open_tm_wrt_tm a (a_Var_f x) )  )  ->
     erased_tm  ( (a_UAbs psi a) ) 
 | erased_a_App : forall (a:tm) (psi:grade) (b:tm),
     erased_tm a ->
     erased_tm b ->
     erased_tm  ( (a_App a psi b) ) 
 | erased_a_Pi : forall (L:vars) (psi:grade) (A B:tm),
     erased_tm A ->
      ( forall x , x \notin  L  -> erased_tm  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     erased_tm  ( (a_Pi psi A B) ) 
 | erased_a_CPi : forall (L:vars) (psi:grade) (phi:constraint) (B:tm),
     erased_constraint phi ->
      ( forall c , c \notin  L  -> erased_tm  ( open_tm_wrt_co B (g_Var_f c) )  )  ->
     erased_tm  ( (a_CPi psi phi B) ) 
 | erased_a_CAbs : forall (L:vars) (psi:grade) (b:tm),
      ( forall c , c \notin  L  -> erased_tm  ( open_tm_wrt_co b (g_Var_f c) )  )  ->
     erased_tm  ( (a_UCAbs psi b) ) 
 | erased_a_CApp : forall (a:tm),
     erased_tm a ->
     erased_tm  ( (a_CApp a g_Triv) ) 
 | erased_a_Fam : forall (F:tyfam),
     erased_tm (a_Fam F).

(* defns Jsub *)
Inductive P_sub : econtext -> econtext -> Prop :=    (* defn P_sub *)
 | P_Empty : 
     P_sub  nil   nil 
 | P_ConsTm : forall (P1:econtext) (x:tmvar) (psi1:grade) (P2:econtext) (psi2:grade),
      ( psi1  <=  psi2 )  ->
     P_sub P1 P2 ->
      ~ AtomSetImpl.In  x  (dom  P1 )  ->
      ~ AtomSetImpl.In  x  (dom  P2 )  ->
     P_sub  (( x  ~ ( psi1 ,e_Tm)) ++  P1 )   (( x  ~ ( psi2 ,e_Tm)) ++  P2 ) 
 | P_ConsCo : forall (P1:econtext) (c:covar) (psi1:grade) (P2:econtext) (psi2:grade),
      ( psi1  <=  psi2 )  ->
     P_sub P1 P2 ->
      ~ AtomSetImpl.In  c  (dom  P1 )  ->
      ~ AtomSetImpl.In  c  (dom  P2 )  ->
     P_sub  (( c  ~ ( psi1 ,e_Co)) ++  P1 )   (( c  ~ ( psi2 ,e_Co)) ++  P2 ) .

(* defns Wsub *)
Inductive ctx_sub : context -> context -> Prop :=    (* defn ctx_sub *)
 | CS_Empty : 
     ctx_sub  nil   nil 
 | CS_ConsTm : forall (G1:context) (x:tmvar) (psi1:grade) (A:tm) (G2:context) (psi2:grade),
      ( psi1  <=  psi2 )  ->
     ctx_sub G1 G2 ->
      ~ AtomSetImpl.In  x  (dom  G1 )  ->
      ~ AtomSetImpl.In  x  (dom  G2 )  ->
      True  ->
     ctx_sub  (( x ~ ( psi1 , Tm  A )) ++  G1 )   (( x ~ ( psi2 , Tm  A )) ++  G2 ) 
 | CS_ConsCo : forall (G1:context) (c:covar) (psi1:grade) (phi:constraint) (G2:context) (psi2:grade),
      ( psi1  <=  psi2 )  ->
     ctx_sub G1 G2 ->
      ~ AtomSetImpl.In  c  (dom  G1 )  ->
      ~ AtomSetImpl.In  c  (dom  G2 )  ->
      True  ->
     ctx_sub  (( c ~ ( psi1 , Co  phi )) ++  G1 )   (( c ~ ( psi2 , Co  phi )) ++  G2 ) .

(* defns JGrade *)
Inductive ECtx : econtext -> Prop :=    (* defn ECtx *)
 | G_Empty : 
     ECtx  nil 
 | G_ConsTm : forall (P:econtext) (x:tmvar) (psi:grade),
     ECtx P ->
      ~ AtomSetImpl.In  x  (dom  P )  ->
     ECtx  (( x  ~ ( psi ,e_Tm)) ++  P ) 
 | G_ConsCo : forall (P:econtext) (c:covar) (psi:grade),
     ECtx P ->
      ~ AtomSetImpl.In  c  (dom  P )  ->
     ECtx  (( c  ~ ( psi ,e_Co)) ++  P ) 
with CoGrade : econtext -> grade -> constraint -> Prop :=    (* defn CoGrade *)
 | CoG_Eq : forall (P:econtext) (psi:grade) (a b A:tm),
     Grade P psi a ->
     Grade P psi b ->
     Grade P psi A ->
     CoGrade P psi (Eq a b A)
 | CoG_Impl : forall (P:econtext) (psi:grade) (phi1 phi2:constraint),
     CoGrade P psi phi1 ->
     CoGrade P psi phi2 ->
     CoGrade P psi (Impl phi1 phi2)
with CGrade : econtext -> grade -> grade -> tm -> Prop :=    (* defn CGrade *)
 | CG_Leq : forall (P:econtext) (psi psi0:grade) (a:tm),
      ( psi0  <=  psi )  ->
     Grade P psi a ->
     CGrade P psi psi0 a
 | CG_Nleq : forall (P:econtext) (psi psi0:grade) (a:tm),
     lc_tm a ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     ECtx P ->
     CGrade P psi psi0 a
with Grade : econtext -> grade -> tm -> Prop :=    (* defn Grade *)
 | G_Var : forall (P:econtext) (psi:grade) (x:tmvar) (psi0:grade),
     ECtx P ->
      binds  x  ( psi0 ,e_Tm)  P  ->
      ( psi0  <=  psi )  ->
     Grade P psi (a_Var_f x)
 | G_Type : forall (P:econtext) (psi:grade),
     ECtx P ->
     Grade P psi a_Star
 | G_Pi : forall (L:vars) (P:econtext) (psi psi0:grade) (A B:tm),
     Grade P psi A ->
      ( forall x , x \notin  L  -> Grade  (( x  ~ ( psi ,e_Tm)) ++  P )  psi  ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     Grade P psi (a_Pi psi0 A B)
 | G_Abs : forall (L:vars) (P:econtext) (psi psi0:grade) (b:tm),
      ( forall x , x \notin  L  -> Grade  (( x  ~ ( psi0 ,e_Tm)) ++  P )  psi  ( open_tm_wrt_tm b (a_Var_f x) )  )  ->
     Grade P psi (a_UAbs psi0 b)
 | G_App : forall (P:econtext) (psi:grade) (b:tm) (psi0:grade) (a:tm),
     Grade P psi b ->
     CGrade P psi psi0 a ->
     Grade P psi (a_App b psi0 a)
 | G_CPi : forall (L:vars) (P:econtext) (psi psi0:grade) (phi:constraint) (B:tm),
     CoGrade P psi phi ->
      ( forall c , c \notin  L  -> Grade  (( c  ~ ( psi ,e_Co)) ++  P )  psi  ( open_tm_wrt_co B (g_Var_f c) )  )  ->
     Grade P psi (a_CPi psi0 phi B)
 | G_CAbs : forall (L:vars) (P:econtext) (psi psi0:grade) (b:tm),
      ( forall c , c \notin  L  -> Grade  (( c  ~ ( psi0 ,e_Co)) ++  P )  psi  ( open_tm_wrt_co b (g_Var_f c) )  )  ->
     Grade P psi (a_UCAbs psi0 b)
 | G_CApp : forall (P:econtext) (psi:grade) (b:tm),
     Grade P psi b ->
     Grade P psi (a_CApp b g_Triv)
 | G_Fam : forall (P:econtext) (psi:grade) (F:tyfam) (a:tm) (psi0:grade) (A:tm),
      binds  F  ( psi0 , (Ax  a A ))   toplevel   ->
      ( psi0  <=  psi )  ->
      ( Grade  nil   q_C  A )  ->
     ECtx P ->
     Grade P psi (a_Fam F).

(* defns JGEq *)
Inductive CoGEq : econtext -> grade -> constraint -> constraint -> Prop :=    (* defn CoGEq *)
 | CoGEq_Eq : forall (P:econtext) (psi:grade) (a b A a' b' A':tm),
     GEq P psi a a' ->
     GEq P psi b b' ->
     GEq P psi A A' ->
     CoGEq P psi (Eq a b A) (Eq a' b' A')
 | CoGEq_Impl : forall (P:econtext) (psi:grade) (phi1 phi3 phi2 phi4:constraint),
     CoGEq P psi phi1 phi2 ->
     CoGEq P psi phi3 phi4 ->
     CoGEq P psi (Impl phi1 phi3) (Impl phi2 phi4)
with CEq : econtext -> grade -> grade -> tm -> tm -> Prop :=    (* defn CEq *)
 | CEq_Leq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
      ( psi0  <=  psi )  ->
     GEq P psi a1 a2 ->
     CEq P psi psi0 a1 a2
 | CEq_Nleq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     ECtx P ->
     CEq P psi psi0 a1 a2
with GEq : econtext -> grade -> tm -> tm -> Prop :=    (* defn GEq *)
 | GEq_Var : forall (P:econtext) (psi:grade) (x:tmvar) (psi0:grade),
     ECtx P ->
      binds  x  ( psi0 ,e_Tm)  P  ->
      ( psi0  <=  psi )  ->
     GEq P psi (a_Var_f x) (a_Var_f x)
 | GEq_Type : forall (P:econtext) (psi:grade),
     ECtx P ->
     GEq P psi a_Star a_Star
 | GEq_Pi : forall (L:vars) (P:econtext) (psi psi0:grade) (A1 B1 A2 B2:tm),
     GEq P psi A1 A2 ->
      ( forall x , x \notin  L  -> GEq  (( x  ~ ( psi ,e_Tm)) ++  P )  psi  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  )  ->
     GEq P psi (a_Pi psi0 A1 B1) (a_Pi psi0 A2 B2)
 | GEq_Abs : forall (L:vars) (P:econtext) (psi psi0:grade) (b1 b2:tm),
      ( forall x , x \notin  L  -> GEq  (( x  ~ ( psi0 ,e_Tm)) ++  P )  psi  ( open_tm_wrt_tm b1 (a_Var_f x) )   ( open_tm_wrt_tm b2 (a_Var_f x) )  )  ->
     GEq P psi (a_UAbs psi0 b1) (a_UAbs psi0 b2)
 | GEq_App : forall (P:econtext) (psi:grade) (b1:tm) (psi0:grade) (a1 b2 a2:tm),
     GEq P psi b1 b2 ->
     CEq P psi psi0 a1 a2 ->
     GEq P psi (a_App b1 psi0 a1) (a_App b2 psi0 a2)
 | GEq_CPi : forall (L:vars) (P:econtext) (psi psi0:grade) (phi1:constraint) (B1:tm) (phi2:constraint) (B2:tm),
     CoGEq P psi phi1 phi2 ->
      ( forall c , c \notin  L  -> GEq  (( c  ~ ( psi ,e_Co)) ++  P )  psi  ( open_tm_wrt_co B1 (g_Var_f c) )   ( open_tm_wrt_co B2 (g_Var_f c) )  )  ->
     GEq P psi (a_CPi psi0 phi1 B1) (a_CPi psi0 phi2 B2)
 | GEq_CAbs : forall (L:vars) (P:econtext) (psi psi0:grade) (b1 b2:tm),
      ( forall c , c \notin  L  -> GEq  (( c  ~ ( psi0 ,e_Co)) ++  P )  psi  ( open_tm_wrt_co b1 (g_Var_f c) )   ( open_tm_wrt_co b2 (g_Var_f c) )  )  ->
     GEq P psi (a_UCAbs psi0 b1) (a_UCAbs psi0 b2)
 | GEq_CApp : forall (P:econtext) (psi:grade) (b1 b2:tm),
     GEq P psi b1 b2 ->
     GEq P psi (a_CApp b1 g_Triv) (a_CApp b2 g_Triv)
 | GEq_Fam : forall (P:econtext) (psi:grade) (F:tyfam) (a:tm) (psi0:grade) (A:tm),
      binds  F  ( psi0 , (Ax  a A ))   toplevel   ->
      ( psi0  <=  psi )  ->
      ( Grade  nil   q_C  A )  ->
     ECtx P ->
     GEq P psi (a_Fam F) a.

(* defns Jpar *)
Inductive CParProp : econtext -> grade -> grade -> constraint -> constraint -> Prop :=    (* defn CParProp *)
 | CParProp_Leq : forall (P:econtext) (psi psi0:grade) (phi1 phi2:constraint),
      ( psi0  <=  psi )  ->
     ParProp P psi phi1 phi2 ->
     CParProp P psi psi0 phi1 phi2
 | CParProp_Nleq : forall (P:econtext) (psi psi0:grade) (phi1 phi2:constraint),
     lc_constraint phi1 ->
     lc_constraint phi2 ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     ECtx P ->
     CParProp P psi psi0 phi1 phi2
with CPar : econtext -> grade -> grade -> tm -> tm -> Prop :=    (* defn CPar *)
 | CPar_Leq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
      ( psi0  <=  psi )  ->
     Par P psi a1 a2 ->
     CPar P psi psi0 a1 a2
 | CPar_Nleq : forall (P:econtext) (psi psi0:grade) (a1 a2:tm),
     lc_tm a1 ->
     lc_tm a2 ->
      not (  (  ( psi0  <=  psi )  )  )  ->
     ECtx P ->
     CPar P psi psi0 a1 a2
with ParProp : econtext -> grade -> constraint -> constraint -> Prop :=    (* defn ParProp *)
 | ParProp_Eq : forall (P:econtext) (psi:grade) (a b A a' b' A':tm),
     Par P psi a a' ->
     Par P psi b b' ->
     Par P psi A A' ->
     ParProp P psi (Eq a b A) (Eq a' b' A')
 | ParProp_Impl : forall (P:econtext) (psi:grade) (phi1 phi2 phi1' phi2':constraint),
     ParProp P psi phi1 phi1' ->
     ParProp P psi phi2 phi2' ->
     ParProp P psi (Impl phi1 phi2) (Impl phi1' phi2')
with Par : econtext -> grade -> tm -> tm -> Prop :=    (* defn Par *)
 | Par_Refl : forall (P:econtext) (psi:grade) (a:tm),
     Grade P psi a ->
     Par P psi a a
 | Par_Beta : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b a' b':tm),
     Par P psi a  ( (a_UAbs psi0 a') )  ->
     CPar P psi psi0 b b' ->
     Par P psi (a_App a psi0 b)  (open_tm_wrt_tm  a'   b' ) 
 | Par_App : forall (P:econtext) (psi:grade) (a:tm) (psi0:grade) (b a' b':tm),
     Par P psi a a' ->
     CPar P psi psi0 b b' ->
     Par P psi (a_App a psi0 b) (a_App a' psi0 b')
 | Par_CBeta : forall (P:econtext) (psi:grade) (a a':tm) (psi0:grade),
     Par P psi a  ( (a_UCAbs psi0 a') )  ->
     Par P psi (a_CApp a g_Triv)  (open_tm_wrt_co  a'   g_Triv ) 
 | Par_CApp : forall (P:econtext) (psi:grade) (a a':tm),
     Par P psi a a' ->
     Par P psi (a_CApp a g_Triv) (a_CApp a' g_Triv)
 | Par_Abs : forall (L:vars) (P:econtext) (psi psi0:grade) (a a':tm),
      ( forall x , x \notin  L  -> Par  (( x  ~ ( psi0 ,e_Tm)) ++  P )  psi  ( open_tm_wrt_tm a (a_Var_f x) )   ( open_tm_wrt_tm a' (a_Var_f x) )  )  ->
     Par P psi (a_UAbs psi0 a) (a_UAbs psi0 a')
 | Par_Pi : forall (L:vars) (P:econtext) (psi psi0:grade) (A B A' B':tm),
     Par P psi A A' ->
      ( forall x , x \notin  L  -> Par  (( x  ~ ( psi ,e_Tm)) ++  P )  psi  ( open_tm_wrt_tm B (a_Var_f x) )   ( open_tm_wrt_tm B' (a_Var_f x) )  )  ->
     Par P psi (a_Pi psi0 A B) (a_Pi psi0 A' B')
 | Par_CAbs : forall (L:vars) (P:econtext) (psi psi0:grade) (a a':tm),
      ( forall c , c \notin  L  -> Par  (( c  ~ ( psi0 ,e_Co)) ++  P )  psi  ( open_tm_wrt_co a (g_Var_f c) )   ( open_tm_wrt_co a' (g_Var_f c) )  )  ->
     Par P psi (a_UCAbs psi0 a) (a_UCAbs psi0 a')
 | Par_CPi : forall (L:vars) (P:econtext) (psi psi0:grade) (phi:constraint) (a:tm) (phi':constraint) (a':tm),
      ( forall c , c \notin  L  -> Par  (( c  ~ ( psi ,e_Co)) ++  P )  psi  ( open_tm_wrt_co a (g_Var_f c) )   ( open_tm_wrt_co a' (g_Var_f c) )  )  ->
     ParProp P psi phi phi' ->
     Par P psi (a_CPi psi0 phi a) (a_CPi psi0 phi' a')
 | Par_Axiom : forall (P:econtext) (psi:grade) (F:tyfam) (a:tm) (psi0:grade) (A:tm),
      ( psi0  <=  psi )  ->
      binds  F  ( psi0 , (Ax  a A ))   toplevel   ->
     ECtx P ->
     Par P psi (a_Fam F) a
 | Par_Eta : forall (L:vars) (P:econtext) (psi psi0:grade) (a b' b:tm),
     Par P psi b b' ->
      ( forall x , x \notin  L  ->  (  ( open_tm_wrt_tm a (a_Var_f x) )   =  (a_App b psi0 (a_Var_f x)) )  )  ->
     Par P psi (a_UAbs psi0 a) b'
 | Par_EtaC : forall (L:vars) (P:econtext) (psi psi0:grade) (a b' b:tm),
     Par P psi b b' ->
      ( forall c , c \notin  L  ->  (  ( open_tm_wrt_co a (g_Var_f c) )   =  (a_CApp b g_Triv) )  )  ->
     Par P psi (a_UCAbs psi0 a) b'.

(* defns Jmultipar *)
Inductive multipar : econtext -> grade -> tm -> tm -> Prop :=    (* defn multipar *)
 | mp_refl : forall (P:econtext) (psi:grade) (a:tm),
     lc_tm a ->
     ECtx P ->
     multipar P psi a a
 | mp_step : forall (P:econtext) (psi:grade) (a a' b:tm),
     Par P psi a b ->
     multipar P psi b a' ->
     multipar P psi a a'
with multipar_prop : econtext -> grade -> constraint -> constraint -> Prop :=    (* defn multipar_prop *)
 | mpprop_refl : forall (P:econtext) (psi:grade) (phi:constraint),
     lc_constraint phi ->
     ECtx P ->
     multipar_prop P psi phi phi
 | mpprop_step : forall (P:econtext) (psi:grade) (phi1 phi3 phi2:constraint),
     ParProp P psi phi1 phi2 ->
     multipar_prop P psi phi2 phi3 ->
     multipar_prop P psi phi1 phi3.

(* defns Jbeta *)
Inductive Beta : tm -> tm -> Prop :=    (* defn Beta *)
 | Beta_AppAbs : forall (psi:grade) (v b:tm),
     lc_tm (a_UAbs psi v) ->
     lc_tm b ->
     Beta (a_App  ( (a_UAbs psi v) )  psi b)  (open_tm_wrt_tm  v   b ) 
 | Beta_CAppCAbs : forall (psi:grade) (a':tm),
     lc_tm (a_UCAbs psi a') ->
     Beta (a_CApp  ( (a_UCAbs psi a') )  g_Triv)  (open_tm_wrt_co  a'   g_Triv ) 
 | Beta_Axiom : forall (F:tyfam) (a:tm) (psi0:grade) (A:tm),
      binds  F  ( psi0 , (Ax  a A ))   toplevel   ->
     Beta (a_Fam F) a
with reduction_in_one : tm -> tm -> Prop :=    (* defn reduction_in_one *)
 | E_AppLeft : forall (a:tm) (psi:grade) (b a':tm),
     lc_tm b ->
     reduction_in_one a a' ->
     reduction_in_one (a_App a psi b) (a_App a' psi b)
 | E_CAppLeft : forall (a a':tm),
     reduction_in_one a a' ->
     reduction_in_one (a_CApp a g_Triv) (a_CApp a' g_Triv)
 | E_AppAbs : forall (psi:grade) (v a:tm),
     lc_tm (a_UAbs psi v) ->
     lc_tm a ->
     reduction_in_one (a_App  ( (a_UAbs psi v) )  psi a)  (open_tm_wrt_tm  v   a ) 
 | E_CAppCAbs : forall (psi:grade) (b:tm),
     lc_tm (a_UCAbs psi b) ->
     reduction_in_one (a_CApp  ( (a_UCAbs psi b) )  g_Triv)  (open_tm_wrt_co  b   g_Triv ) 
 | E_Axiom : forall (F:tyfam) (a:tm) (psi0:grade) (A:tm),
      binds  F  ( psi0 , (Ax  a A ))   toplevel   ->
     reduction_in_one (a_Fam F) a
with reduction : tm -> tm -> Prop :=    (* defn reduction *)
 | Equal : forall (a:tm),
     lc_tm a ->
     reduction a a
 | Step : forall (a a' b:tm),
     reduction_in_one a b ->
     reduction b a' ->
     reduction a a'.

(* defns Jett *)
Inductive PropWff : context -> grade -> constraint -> Prop :=    (* defn PropWff *)
 | E_WffEq : forall (G:context) (psi:grade) (a b A:tm),
     Typing G psi a A ->
     Typing G psi b A ->
      ( Typing G psi A a_Star )  ->
     PropWff G psi (Eq a b A)
 | E_WffImpl : forall (G:context) (psi:grade) (phi1 phi2:constraint),
     PropWff G psi phi1 ->
     PropWff G psi phi2 ->
     PropWff G psi (Impl phi1 phi2)
with Typing : context -> grade -> tm -> tm -> Prop :=    (* defn Typing *)
 | E_Star : forall (G:context) (psi:grade),
     Ctx G ->
      ( psi  <=   q_C  )  ->
     Typing G psi a_Star a_Star
 | E_Var : forall (G:context) (psi:grade) (x:tmvar) (A:tm) (psi0:grade),
     Ctx G ->
      ( psi0  <=  psi )  ->
      ( psi  <=   q_C  )  ->
      binds  x  ( psi0 , (Tm  A ))  G  ->
     Typing G psi (a_Var_f x) A
 | E_Pi : forall (L:vars) (G:context) (psi psi0:grade) (A B:tm),
      ( forall x , x \notin  L  -> Typing  (( x ~ ( psi , Tm  A )) ++  G )  psi  ( open_tm_wrt_tm B (a_Var_f x) )  a_Star )  ->
      ( Typing G psi A a_Star )  ->
     Typing G psi (a_Pi psi0 A B) a_Star
 | E_Abs : forall (L:vars) (G:context) (psi psi0:grade) (a A B:tm),
      ( forall x , x \notin  L  -> Typing  (( x ~ (  (q_join  psi0   psi )  , Tm  A )) ++  G )  psi  ( open_tm_wrt_tm a (a_Var_f x) )   ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
      ( Typing  (meet_ctx_l   q_C    G )   q_C  A a_Star )  ->
     Typing G psi (a_UAbs psi0 a) (a_Pi psi0 A B)
 | E_App : forall (G:context) (psi:grade) (b:tm) (psi0:grade) (a B A:tm),
     Typing G psi b (a_Pi psi0 A B) ->
     Typing G  (q_join  psi0   psi )  a A ->
      ( psi0  <=   q_C  )  ->
     Typing G psi (a_App b psi0 a)  (open_tm_wrt_tm  B   a ) 
 | E_AppIrrel : forall (G:context) (psi:grade) (b:tm) (psi0:grade) (a B A:tm),
     Typing G psi b (a_Pi psi0 A B) ->
     Typing  (meet_ctx_l   q_C    G )   q_C  a A ->
      (  q_C   <  psi0 )  ->
     Typing G psi (a_App b psi0 a)  (open_tm_wrt_tm  B   a ) 
 | E_Conv : forall (G:context) (psi:grade) (a B A:tm),
     Typing G psi a A ->
     DefEq  (meet_ctx_l   q_C    G )   q_C  (Eq A B a_Star) ->
      ( Typing  (meet_ctx_l   q_C    G )   q_C  B a_Star )  ->
     Typing G psi a B
 | E_CPi : forall (L:vars) (G:context) (psi psi0:grade) (phi:constraint) (B:tm),
      ( forall c , c \notin  L  -> Typing  (( c ~ ( psi , Co  phi )) ++  G )  psi  ( open_tm_wrt_co B (g_Var_f c) )  a_Star )  ->
      ( PropWff G psi phi )  ->
     Typing G psi (a_CPi psi0 phi B) a_Star
 | E_CAbs : forall (L:vars) (G:context) (psi psi0:grade) (a:tm) (phi:constraint) (B:tm),
      ( forall c , c \notin  L  -> Typing  (( c ~ (  (q_join  psi0   psi )  , Co  phi )) ++  G )  psi  ( open_tm_wrt_co a (g_Var_f c) )   ( open_tm_wrt_co B (g_Var_f c) )  )  ->
      ( PropWff  (meet_ctx_l   q_C    G )   q_C  phi )  ->
     Typing G psi (a_UCAbs psi0 a) (a_CPi psi0 phi B)
 | E_CApp : forall (G:context) (psi:grade) (a1 B1:tm) (phi:constraint),
     Typing G psi a1 (a_CPi  q_Top  phi B1) ->
     DefEq  (meet_ctx_l   q_C    G )   q_C  phi ->
     Typing G psi (a_CApp a1 g_Triv)  (open_tm_wrt_co  B1   g_Triv ) 
 | E_Fam : forall (G:context) (psi:grade) (F:tyfam) (A:tm) (psi0:grade) (P:econtext) (a:tm),
      ( Typing  nil   q_C  A a_Star )  ->
      ( psi0  <=  psi )  ->
     ECtx P ->
      binds  F  ( psi0 , (Ax  a A ))   toplevel   ->
     Typing G psi (a_Fam F) A
with Iso : context -> grade -> constraint -> constraint -> Prop :=    (* defn Iso *)
 | E_PropCong : forall (G:context) (psi:grade) (A1 B1 A A2 B2:tm),
     DefEq G psi (Eq A1 A2 A) ->
     DefEq G psi (Eq B1 B2 A) ->
     Iso G psi (Eq A1 B1 A) (Eq A2 B2 A)
 | E_IsoConv : forall (G:context) (psi:grade) (A1 A2 A B:tm),
     DefEq G psi (Eq A B a_Star) ->
     PropWff G psi (Eq A1 A2 A) ->
     PropWff G psi (Eq A1 A2 B) ->
     Iso G psi (Eq A1 A2 A) (Eq A1 A2 B)
 | E_CPiFst : forall (G:context) (psi:grade) (phi1 phi2:constraint) (psi0:grade) (B1 B2:tm),
     DefEq G psi (Eq (a_CPi psi0 phi1 B1) (a_CPi psi0 phi2 B2) a_Star) ->
     Iso G psi phi1 phi2
 | E_ImplCong : forall (G:context) (psi:grade) (phi1 phi3 phi2 phi4:constraint),
     Iso G psi phi1 phi2 ->
     Iso G psi phi3 phi4 ->
     Iso G psi (Impl phi1 phi3) (Impl phi2 phi4)
with CDefEq : context -> grade -> grade -> tm -> tm -> tm -> Prop :=    (* defn CDefEq *)
 | CDefEq_Leq : forall (G:context) (psi psi0:grade) (a b A:tm),
      ( psi0  <=  psi )  ->
     DefEq G psi (Eq a b A) ->
     CDefEq G psi psi0 a b A
 | CDefEq_Nleq : forall (G:context) (psi psi0:grade) (a b A:tm),
      not (  (  ( psi0  <=  psi )  )  )  ->
     Ctx G ->
      ( psi0  <=   q_C  )  ->
     Typing G  (q_join  psi0   psi )  a A ->
     Typing G  (q_join  psi0   psi )  b A ->
     CDefEq G psi psi0 a b A
 | CDefEq_NleqIrrel : forall (G:context) (psi psi0:grade) (a b A:tm),
      not (  (  ( psi0  <=  psi )  )  )  ->
     Ctx G ->
      (  q_C   <  psi0 )  ->
      ( psi  <=   q_C  )  ->
     Typing  (meet_ctx_l   q_C    G )   q_C  a A ->
     Typing  (meet_ctx_l   q_C    G )   q_C  b A ->
     CDefEq G psi psi0 a b A
with DefEq : context -> grade -> constraint -> Prop :=    (* defn DefEq *)
 | E_Assn : forall (G:context) (psi:grade) (phi:constraint) (psi0:grade) (c:covar),
     Ctx G ->
      ( psi0  <=  psi )  ->
      ( psi  <=   q_C  )  ->
      binds  c  ( psi0 , (Co  phi ))  G  ->
     DefEq G psi phi
 | E_Refl : forall (G:context) (psi:grade) (a A:tm),
     Typing G psi a A ->
     DefEq G psi (Eq a a A)
 | E_Sym : forall (G:context) (psi:grade) (a b A:tm),
     DefEq G psi (Eq b a A) ->
     DefEq G psi (Eq a b A)
 | E_Trans : forall (G:context) (psi:grade) (a b A a1:tm),
     DefEq G psi (Eq a a1 A) ->
     DefEq G psi (Eq a1 b A) ->
     DefEq G psi (Eq a b A)
 | E_Beta : forall (G:context) (psi:grade) (a1 a2 B:tm),
     Typing G psi a1 B ->
      ( Typing G psi a2 B )  ->
     Beta a1 a2 ->
     DefEq G psi (Eq a1 a2 B)
 | E_PiCong : forall (L:vars) (G:context) (psi psi0:grade) (A1 B1 A2 B2:tm),
     DefEq G psi (Eq A1 A2 a_Star) ->
      ( forall x , x \notin  L  -> DefEq  (( x ~ ( psi , Tm  A1 )) ++  G )  psi (Eq  ( open_tm_wrt_tm B1 (a_Var_f x) )   ( open_tm_wrt_tm B2 (a_Var_f x) )  a_Star) )  ->
      ( Typing G psi A1 a_Star )  ->
      ( Typing G psi (a_Pi psi0 A1 B1) a_Star )  ->
      ( Typing G psi (a_Pi psi0 A2 B2) a_Star )  ->
     DefEq G psi (Eq  ( (a_Pi psi0 A1 B1) )   ( (a_Pi psi0 A2 B2) )  a_Star)
 | E_AbsCong : forall (L:vars) (G:context) (psi psi0:grade) (b1 b2 A1 B:tm),
      ( forall x , x \notin  L  -> DefEq  (( x ~ (  (q_join  psi0   psi )  , Tm  A1 )) ++  G )  psi (Eq  ( open_tm_wrt_tm b1 (a_Var_f x) )   ( open_tm_wrt_tm b2 (a_Var_f x) )   ( open_tm_wrt_tm B (a_Var_f x) ) ) )  ->
      ( Typing  (meet_ctx_l   q_C    G )   q_C  A1 a_Star )  ->
     DefEq G psi (Eq  ( (a_UAbs psi0 b1) )   ( (a_UAbs psi0 b2) )  (a_Pi psi0 A1 B))
 | E_AppCong : forall (G:context) (psi:grade) (a1:tm) (psi0:grade) (a2 b1 b2 B A:tm),
     DefEq G psi (Eq a1 b1 (a_Pi psi0 A B)) ->
     CDefEq G psi psi0 a2 b2 A ->
     DefEq G psi (Eq (a_App a1 psi0 a2) (a_App b1 psi0 b2)  (  (open_tm_wrt_tm  B   a2 )  ) )
 | E_PiFst : forall (G:context) (psi:grade) (A1 A2:tm) (psi0:grade) (B1 B2:tm),
     DefEq G psi (Eq (a_Pi psi0 A1 B1) (a_Pi psi0 A2 B2) a_Star) ->
     DefEq G psi (Eq A1 A2 a_Star)
 | E_PiSnd : forall (G:context) (psi:grade) (B1 a1 B2 a2:tm) (psi0:grade) (A1 A2:tm),
     DefEq G psi (Eq (a_Pi psi0 A1 B1) (a_Pi psi0 A2 B2) a_Star) ->
     DefEq G psi (Eq a1 a2 A1) ->
     DefEq G psi (Eq  (open_tm_wrt_tm  B1   a1 )   (open_tm_wrt_tm  B2   a2 )  a_Star)
 | E_CPiCong : forall (L:vars) (G:context) (psi:grade) (phi1:constraint) (A:tm) (phi2:constraint) (B:tm),
     Iso G psi phi1 phi2 ->
      ( forall c , c \notin  L  -> DefEq  (( c ~ (  q_Top  , Co  phi1 )) ++  G )  psi (Eq  ( open_tm_wrt_co A (g_Var_f c) )   ( open_tm_wrt_co B (g_Var_f c) )  a_Star) )  ->
      ( PropWff G psi phi1 )  ->
      ( Typing G psi (a_CPi  q_Top  phi1 A) a_Star )  ->
      ( Typing G psi (a_CPi  q_Top  phi2 B) a_Star )  ->
     DefEq G psi (Eq (a_CPi  q_Top  phi1 A) (a_CPi  q_Top  phi2 B) a_Star)
 | E_CAbsCong : forall (L:vars) (G:context) (psi:grade) (a b:tm) (phi1:constraint) (B:tm),
      ( forall c , c \notin  L  -> DefEq  (( c ~ (  q_Top  , Co  phi1 )) ++  G )  psi (Eq  ( open_tm_wrt_co a (g_Var_f c) )   ( open_tm_wrt_co b (g_Var_f c) )   ( open_tm_wrt_co B (g_Var_f c) ) ) )  ->
      ( PropWff  (meet_ctx_l   q_C    G )   q_C  phi1 )  ->
     DefEq G psi (Eq  ( (a_UCAbs  q_Top  a) )   ( (a_UCAbs  q_Top  b) )  (a_CPi  q_Top  phi1 B))
 | E_CAppCong : forall (G:context) (psi:grade) (a1 b1 B:tm) (phi:constraint),
     DefEq G psi (Eq a1 b1 (a_CPi  q_Top  phi B)) ->
     DefEq  (meet_ctx_l   q_C    G )   q_C  phi ->
     DefEq G psi (Eq (a_CApp a1 g_Triv) (a_CApp b1 g_Triv)  (open_tm_wrt_co  B   g_Triv ) )
 | E_CPiSnd : forall (G:context) (psi:grade) (B1 B2:tm) (psi0:grade) (phi1 phi2:constraint),
     DefEq G psi (Eq (a_CPi psi0 phi1 B1) (a_CPi psi0 phi2 B2) a_Star) ->
     DefEq  (meet_ctx_l   q_C    G )   q_C  phi1 ->
     DefEq  (meet_ctx_l   q_C    G )   q_C  phi2 ->
     DefEq G psi (Eq  (open_tm_wrt_co  B1   g_Triv )   (open_tm_wrt_co  B2   g_Triv )  a_Star)
 | E_Cast : forall (G:context) (psi:grade) (phi2 phi1:constraint),
     DefEq G psi phi1 ->
     Iso G psi phi1 phi2 ->
     DefEq G psi phi2
 | E_EqConv : forall (G:context) (psi:grade) (a b B A:tm),
     DefEq G psi (Eq a b A) ->
     DefEq  (meet_ctx_l   q_C    G )  psi (Eq A B a_Star) ->
     DefEq G psi (Eq a b B)
 | E_IsoSnd : forall (G:context) (psi:grade) (A A' a b a' b':tm),
     Iso G psi (Eq a b A) (Eq a' b' A') ->
     DefEq G psi (Eq A A' a_Star)
 | E_EtaRel : forall (L:vars) (G:context) (psi psi0:grade) (a b A B:tm),
     Typing G psi b (a_Pi psi0 A B) ->
      ( forall x , x \notin  L  ->  (  ( open_tm_wrt_tm a (a_Var_f x) )   =  (a_App b psi0 (a_Var_f x)) )  )  ->
     DefEq G psi (Eq (a_UAbs psi0 a) b (a_Pi psi0 A B))
 | E_EtaC : forall (L:vars) (G:context) (psi:grade) (a b:tm) (phi:constraint) (B:tm),
     Typing G psi b (a_CPi  q_Top  phi B) ->
      ( forall c , c \notin  L  ->  (  ( open_tm_wrt_co a (g_Var_f c) )   =  (a_CApp b g_Triv) )  )  ->
     DefEq G psi (Eq (a_UCAbs  q_Top  a) b (a_CPi  q_Top  phi B))
 | E_ImplApp : forall (G:context) (psi:grade) (phi2 phi1:constraint),
     DefEq G psi (Impl phi1 phi2) ->
     DefEq G psi phi1 ->
     DefEq G psi phi2
 | E_ImplAbs : forall (G:context) (psi:grade) (phi1 phi2:constraint) (c:covar),
     DefEq  (( c ~ ( psi , Co  phi1 )) ++  G )  psi phi2 ->
      ( PropWff  (meet_ctx_l   q_C    G )   q_C  phi1 )  ->
     DefEq G psi (Impl phi1 phi2)
with Ctx : context -> Prop :=    (* defn Ctx *)
 | E_Empty : 
     Ctx  nil 
 | E_ConsTm : forall (G:context) (x:tmvar) (psi:grade) (A:tm),
     Ctx G ->
     Typing  (meet_ctx_l   q_C    G )   q_C  A a_Star ->
      ~ AtomSetImpl.In  x  (dom  G )  ->
     Ctx  (( x ~ ( psi , Tm  A )) ++  G ) 
 | E_ConsCo : forall (G:context) (c:covar) (psi:grade) (phi:constraint),
     Ctx G ->
     PropWff  (meet_ctx_l   q_C    G )   q_C  phi ->
      ~ AtomSetImpl.In  c  (dom  G )  ->
     Ctx  (( c ~ ( psi , Co  phi )) ++  G ) .

(* defns Jsig *)
Inductive Sig : sig -> Prop :=    (* defn Sig *)
 | Sig_Empty : 
     Sig  nil 
 | Sig_ConsAx : forall (S:sig) (F:tyfam) (a:tm) (psi0:grade) (A:tm),
     Sig S ->
     Typing  nil   q_C  A a_Star ->
     Typing  nil  psi0 a A ->
      ~ AtomSetImpl.In  F  (dom  S )  ->
     Sig  (( F ~ ( psi0 , Ax a A ))++ S ) .

(* defns Jann *)
Inductive AnnPropWff : context -> grade -> constraint -> Prop :=    (* defn AnnPropWff *)
 | An_Wff : forall (G:context) (psi:grade) (a b A B:tm),
     AnnTyping G psi a A ->
     AnnTyping G psi b B ->
      (  (erase_tm  A )   =   (erase_tm  B )  )  ->
     AnnPropWff G psi (Eq a b A)
with AnnTyping : context -> grade -> tm -> tm -> Prop :=    (* defn AnnTyping *)
 | An_Star : forall (G:context) (psi:grade),
     AnnCtx G ->
     AnnTyping G psi a_Star a_Star
 | An_Var : forall (G:context) (psi:grade) (x:tmvar) (A:tm) (psi0:grade),
     AnnCtx G ->
      binds  x  ( psi0 , (Tm  A ))  G  ->
      ( psi0  <=  psi )  ->
     AnnTyping G psi (a_Var_f x) A
 | An_Pi : forall (L:vars) (G:context) (psi psi0:grade) (A B:tm),
      ( forall x , x \notin  L  -> AnnTyping  (( x ~ ( psi , Tm  A )) ++  G )  psi  ( open_tm_wrt_tm B (a_Var_f x) )  a_Star )  ->
      ( AnnTyping G psi A a_Star )  ->
     AnnTyping G psi (a_Pi psi0 A B) a_Star
 | An_Abs : forall (L:vars) (G:context) (psi psi0:grade) (A a B:tm),
      ( AnnTyping  (meet_ctx_l   q_C    G )   q_C  A a_Star )  ->
      ( forall x , x \notin  L  -> AnnTyping  (( x ~ (  (q_join  psi0   psi )  , Tm  A )) ++  G )  psi  ( open_tm_wrt_tm a (a_Var_f x) )   ( open_tm_wrt_tm B (a_Var_f x) )  )  ->
     AnnTyping G psi (a_Abs psi0 A a) (a_Pi psi0 A B)
 | An_App : forall (G:context) (psi:grade) (b:tm) (psi0:grade) (a B A:tm),
     AnnTyping G psi b (a_Pi psi0 A B) ->
     AnnTyping G  (q_join  psi0   psi )  a A ->
      ( psi0  <=   q_C  )  ->
     AnnTyping G psi (a_App b psi0 a)  (open_tm_wrt_tm  B   a ) 
 | An_AppIrrel : forall (G:context) (psi:grade) (b:tm) (psi0:grade) (a B A:tm),
     AnnTyping G psi b (a_Pi psi0 A B) ->
     AnnTyping  (meet_ctx_l   q_C    G )   q_C  a A ->
      (  q_C   <  psi0 )  ->
     AnnTyping G psi (a_App b psi0 a)  (open_tm_wrt_tm  B   a ) 
 | An_Conv : forall (G:context) (psi:grade) (a:tm) (g:co) (B A:tm),
     AnnTyping G psi a A ->
     AnnDefEq  (meet_ctx_l   q_C    G )   q_C  g A B ->
     AnnTyping  (meet_ctx_l   q_C    G )   q_C  B a_Star ->
     AnnTyping G psi (a_Conv a g) B
 | An_CPi : forall (L:vars) (G:context) (psi psi0:grade) (phi:constraint) (B:tm),
      ( AnnPropWff G psi phi )  ->
      ( forall c , c \notin  L  -> AnnTyping  (( c ~ ( psi , Co  phi )) ++  G )  psi  ( open_tm_wrt_co B (g_Var_f c) )  a_Star )  ->
     AnnTyping G psi (a_CPi psi0 phi B) a_Star
 | An_CAbs : forall (L:vars) (G:context) (psi psi0:grade) (phi:constraint) (a B:tm),
      ( AnnPropWff  (meet_ctx_l   q_C    G )   q_C  phi )  ->
      ( forall c , c \notin  L  -> AnnTyping  (( c ~ (  (q_join  psi0   psi )  , Co  phi )) ++  G )  psi  ( open_tm_wrt_co a (g_Var_f c) )   ( open_tm_wrt_co B (g_Var_f c) )  )  ->
     AnnTyping G psi (a_CAbs psi0 phi a) (a_CPi psi0 phi B)
 | An_CApp : forall (G:context) (psi:grade) (a1:tm) (g:co) (B a b A1:tm),
     AnnTyping G psi a1 (a_CPi  q_Top  (Eq a b A1) B) ->
     AnnDefEq  (meet_ctx_l   q_C    G )   q_C  g a b ->
     AnnTyping G psi (a_CApp a1 g)  (open_tm_wrt_co  B   g ) 
 | An_Fam : forall (G:context) (psi:grade) (F:tyfam) (A:tm) (psi0:grade) (a:tm),
     AnnCtx G ->
      ( psi0  <=  psi )  ->
      ( psi  <=   q_C  )  ->
      binds  F  ( psi0 , (Ax  a A ))   an_toplevel   ->
      ( AnnTyping  nil   q_C  A a_Star )  ->
     AnnTyping G psi (a_Fam F) A
with AnnIso : context -> grade -> co -> constraint -> constraint -> Prop :=    (* defn AnnIso *)
 | An_PropCong : forall (G:context) (psi:grade) (g1:co) (A:tm) (g2:co) (A1 B1 A2 B2:tm),
     AnnDefEq G psi g1 A1 A2 ->
     AnnDefEq G psi g2 B1 B2 ->
     AnnPropWff G psi (Eq A1 B1 A) ->
     AnnPropWff G psi (Eq A2 B2 A) ->
     AnnIso G psi  ( (g_EqCong g1 A g2) )   ( (Eq A1 B1 A) )   ( (Eq A2 B2 A) ) 
 | An_CPiFst : forall (G:context) (psi:grade) (g:co) (phi1 phi2:constraint) (psi0:grade) (A2 B2:tm),
     AnnDefEq G psi g (a_CPi psi0 phi1 A2) (a_CPi psi0 phi2 B2) ->
     AnnIso G psi (g_CPiFst g) phi1 phi2
 | An_IsoSym : forall (G:context) (psi:grade) (g:co) (phi2 phi1:constraint),
     AnnIso G psi g phi1 phi2 ->
     AnnIso G psi (g_Sym g) phi2 phi1
 | An_IsoConv : forall (G:context) (psi:grade) (a1 a2 A a1' a2' B:tm) (g:co),
     AnnDefEq G psi g A B ->
     AnnPropWff  (meet_ctx_l   q_C    G )   q_C  (Eq a1 a2 A) ->
     AnnPropWff  (meet_ctx_l   q_C    G )   q_C  (Eq a1' a2' B) ->
      (  (erase_tm  a1 )   =   (erase_tm  a1' )  )  ->
      (  (erase_tm  a2 )   =   (erase_tm  a2' )  )  ->
     AnnIso G psi (g_IsoConv  ( (Eq a1 a2 A) )   ( (Eq a1' a2' B) )  g)  ( (Eq a1 a2 A) )   ( (Eq a1' a2' B) ) 
with AnnDefCEq : context -> grade -> grade -> co -> tm -> tm -> Prop :=    (* defn AnnDefCEq *)
with AnnDefEq : context -> grade -> co -> tm -> tm -> Prop :=    (* defn AnnDefEq *)
 | An_Assn : forall (G:context) (psi:grade) (c:covar) (a b:tm) (psi0:grade) (A:tm),
     AnnCtx G ->
      ( psi0  <=  psi )  ->
      binds  c  ( psi0 , (Co  (Eq a b A) ))  G  ->
     AnnDefEq G psi (g_Var_f c) a b
 | An_Refl : forall (G:context) (psi:grade) (a A:tm),
     AnnTyping G psi a A ->
     AnnDefEq G psi (g_Refl a) a a
 | An_EraseEq : forall (G:context) (psi:grade) (a b:tm) (g:co) (A B:tm),
     AnnTyping G psi a A ->
     AnnTyping G psi b B ->
      (  (erase_tm  a )   =   (erase_tm  b )  )  ->
     AnnDefEq  (meet_ctx_l   q_C    G )   q_C  g A B ->
     AnnDefEq G psi (g_Refl2 a b g) a b
 | An_Sym : forall (G:context) (psi:grade) (g:co) (a b B A:tm) (g1:co),
     AnnTyping G psi b B ->
     AnnTyping G psi a A ->
      ( AnnDefEq  (meet_ctx_l   q_C    G )   q_C  g1 B A )  ->
     AnnDefEq G psi g b a ->
     AnnDefEq G psi (g_Sym g) a b
 | An_Trans : forall (G:context) (psi:grade) (g1 g2:co) (a b a1 A A1:tm) (g3:co),
     AnnDefEq G psi g1 a a1 ->
     AnnDefEq G psi g2 a1 b ->
      ( AnnTyping G psi a A )  ->
      ( AnnTyping G psi a1 A1 )  ->
      ( AnnDefEq  (meet_ctx_l   q_C    G )   q_C  g3 A A1 )  ->
     AnnDefEq G psi  ( (g_Trans g1 g2) )  a b
 | An_Beta : forall (G:context) (psi:grade) (a1 a2 B0 B1:tm),
     AnnTyping G psi a1 B0 ->
     AnnTyping G psi a2 B1 ->
      (  (erase_tm  B0 )   =   (erase_tm  B1 )  )  ->
     Beta  (erase_tm  a1 )   (erase_tm  a2 )  ->
     AnnDefEq G psi (g_Beta a1 a2) a1 a2
 | An_PiCong : forall (L:vars) (G:context) (psi psi0:grade) (g1 g2:co) (A1 B1 A2 B3 B2:tm),
     AnnDefEq G psi g1 A1 A2 ->
      ( forall x , x \notin  L  -> AnnDefEq  (( x ~ ( psi , Tm  A1 )) ++  G )  psi  ( open_co_wrt_tm g2 (a_Var_f x) )   ( open_tm_wrt_tm B1 (a_Var_f x) )    (open_tm_wrt_tm  B2   (a_Var_f x) )   )  ->
      ( forall x , x \notin  L  ->  (  ( open_tm_wrt_tm B3 (a_Var_f x) )   =   (open_tm_wrt_tm  B2   (a_Conv (a_Var_f x) (g_Sym g1)) )  )  )  ->
     AnnTyping G psi (a_Pi psi0 A1 B1) a_Star ->
     AnnTyping G psi (a_Pi psi0 A2 B3) a_Star ->
     AnnTyping G psi  ( (a_Pi psi0 A1 B2) )  a_Star ->
     AnnDefEq G psi (g_PiCong psi0 g1 g2)  ( (a_Pi psi0 A1 B1) )   ( (a_Pi psi0 A2 B3) ) 
 | An_AbsCong : forall (L:vars) (G:context) (psi psi0:grade) (g1 g2:co) (A1 b1 A2 b3 b2 B:tm),
     AnnDefEq  (meet_ctx_l   q_C    G )   q_C  g1 A1 A2 ->
      ( forall x , x \notin  L  -> AnnDefEq  (( x ~ ( psi0 , Tm  A1 )) ++  G )  psi  ( open_co_wrt_tm g2 (a_Var_f x) )   ( open_tm_wrt_tm b1 (a_Var_f x) )    (open_tm_wrt_tm  b2   (a_Var_f x) )   )  ->
      ( forall x , x \notin  L  ->  (  ( open_tm_wrt_tm b3 (a_Var_f x) )   =   (open_tm_wrt_tm  b2   (a_Conv (a_Var_f x) (g_Sym g1)) )  )  )  ->
      ( AnnTyping  (meet_ctx_l   q_C    G )   q_C  A1 a_Star )  ->
     AnnTyping  (meet_ctx_l   q_C    G )   q_C  A2 a_Star ->
      ( AnnTyping G psi (a_Abs psi0 A1 b2) B )  ->
     AnnDefEq G psi  ( (g_AbsCong psi0 g1 g2) )   ( (a_Abs psi0 A1 b1) )   ( (a_Abs psi0 A2 b3) ) 
 | An_AppCong : forall (G:context) (psi:grade) (g1:co) (psi0:grade) (g2:co) (a1 a2 b1 b2 A B:tm) (g3:co),
     AnnDefEq G psi g1 a1 b1 ->
     AnnDefCEq G psi psi0 g2 a2 b2 ->
     AnnTyping G psi (a_App a1 psi0 a2) A ->
     AnnTyping G psi (a_App b1 psi0 b2) B ->
      ( AnnDefEq  (meet_ctx_l   q_C    G )   q_C  g3 A B )  ->
     AnnDefEq G psi (g_AppCong g1 psi0 g2) (a_App a1 psi0 a2) (a_App b1 psi0 b2)
 | An_PiFst : forall (G:context) (psi:grade) (g:co) (A1 A2:tm) (psi0:grade) (B1 B2:tm),
     AnnDefEq G psi g (a_Pi psi0 A1 B1) (a_Pi psi0 A2 B2) ->
     AnnDefEq G psi (g_PiFst g) A1 A2
 | An_PiSnd : forall (G:context) (psi:grade) (g1 g2:co) (B1 a1 B2 a2:tm) (psi0:grade) (A1 A2:tm),
     AnnDefEq G psi g1 (a_Pi psi0 A1 B1) (a_Pi psi0 A2 B2) ->
     AnnDefEq G psi g2 a1 a2 ->
     AnnTyping G psi a1 A1 ->
     AnnTyping G psi a2 A2 ->
     AnnDefEq G psi (g_PiSnd g1 g2)   (open_tm_wrt_tm  B1   a1 )     (open_tm_wrt_tm  B2   a2 )  
 | An_CPiCong : forall (L:vars) (G:context) (psi:grade) (g1 g3:co) (psi0:grade) (phi1:constraint) (B1:tm) (phi2:constraint) (B3 B2:tm),
     AnnIso G psi g1 phi1 phi2 ->
      ( forall c , c \notin  L  -> AnnDefEq  (( c ~ ( psi , Co  phi1 )) ++  G )  psi  ( open_co_wrt_co g3 (g_Var_f c) )   ( open_tm_wrt_co B1 (g_Var_f c) )    (open_tm_wrt_co  B2   (g_Var_f c) )   )  ->
      ( forall c , c \notin  L  ->  (  ( open_tm_wrt_co B3 (g_Var_f c) )   =   (open_tm_wrt_co  B2   (g_Cast (g_Var_f c) (g_Sym g1)) )  )  )  ->
     AnnTyping G psi (a_CPi psi0 phi1 B1) a_Star ->
      ( AnnTyping G psi (a_CPi psi0 phi2 B3) a_Star )  ->
     AnnTyping G psi (a_CPi psi0 phi1 B2) a_Star ->
     AnnDefEq G psi  ( (g_CPiCong g1 g3) )   ( (a_CPi psi0 phi1 B1) )   ( (a_CPi psi0 phi2 B3) ) 
 | An_CAbsCong : forall (L:vars) (G:context) (psi psi0:grade) (g1 g3 g4:co) (phi1:constraint) (a1:tm) (phi2:constraint) (a3 a2 B1 B2 B:tm),
     AnnIso G psi g1 phi1 phi2 ->
      ( forall c , c \notin  L  -> AnnDefEq  (( c ~ (  (q_join  psi0   psi )  , Co  phi1 )) ++  G )  psi  ( open_co_wrt_co g3 (g_Var_f c) )   ( open_tm_wrt_co a1 (g_Var_f c) )    (open_tm_wrt_co  a2   (g_Var_f c) )   )  ->
      ( forall c , c \notin  L  ->  (  ( open_tm_wrt_co a3 (g_Var_f c) )   =   (open_tm_wrt_co  a2   (g_Cast (g_Var_f c) (g_Sym g1)) )  )  )  ->
     AnnTyping G psi  ( (a_CAbs psi0 phi1 a1) )  (a_CPi psi0 phi1 B1) ->
     AnnTyping G psi  ( (a_CAbs psi0 phi2 a3) )  (a_CPi psi0 phi2 B2) ->
     AnnTyping G psi  ( (a_CAbs psi0 phi1 a2) )  B ->
     AnnDefEq  (meet_ctx_l   q_C    G )  psi g4 (a_CPi psi0 phi1 B1) (a_CPi psi0 phi2 B2) ->
     AnnDefEq G psi  ( (g_CAbsCong psi0 g1 g3 g4) )   ( (a_CAbs psi0 phi1 a1) )   ( (a_CAbs psi0 phi2 a3) ) 
 | An_CAppCong : forall (G:context) (psi:grade) (g1 g2 g3:co) (a1 b1 a2 b2 a3 b3 A B:tm) (g4:co),
     AnnDefEq G psi g1 a1 b1 ->
     AnnDefEq  (meet_ctx_l   q_C    G )   q_C  g2 a2 b2 ->
     AnnDefEq  (meet_ctx_l   q_C    G )   q_C  g3 a3 b3 ->
     AnnTyping G psi (a_CApp a1 g2) A ->
     AnnTyping G psi (a_CApp b1 g3) B ->
      ( AnnDefEq  (meet_ctx_l   q_C    G )   q_C  g4 A B )  ->
     AnnDefEq G psi (g_CAppCong g1 g2 g3) (a_CApp a1 g2) (a_CApp b1 g3)
 | An_CPiSnd : forall (G:context) (psi:grade) (g1 g2 g3:co) (B1 B2:tm) (psi0:grade) (a a' A b b' B:tm),
     AnnDefEq G psi g1  ( (a_CPi psi0 (Eq a a' A) B1) )   ( (a_CPi psi0 (Eq b b' B) B2) )  ->
     AnnDefEq  (meet_ctx_l   q_C    G )   q_C  g2 a a' ->
     AnnDefEq  (meet_ctx_l   q_C    G )   q_C  g3 b b' ->
     AnnDefEq G psi (g_CPiSnd g1 g2 g3)  (open_tm_wrt_co  B1   g2 )   (open_tm_wrt_co  B2   g3 ) 
 | An_Cast : forall (G:context) (psi:grade) (g1 g2:co) (b b' a a' A B:tm),
     AnnDefEq G psi g1 a a' ->
     AnnIso G psi g2 (Eq a a' A) (Eq b b' B) ->
     AnnDefEq G psi (g_Cast g1 g2) b b'
 | An_IsoSnd : forall (G:context) (psi:grade) (g:co) (A B a a' b b':tm),
     AnnIso G psi g  ( (Eq a a' A) )   ( (Eq b b' B) )  ->
     AnnDefEq G psi (g_IsoSnd g) A B
 | An_Eta : forall (L:vars) (G:context) (psi:grade) (b:tm) (psi0:grade) (A a B:tm),
     AnnTyping G psi b (a_Pi psi0 A B) ->
      ( forall x , x \notin  L  ->  (  ( open_tm_wrt_tm a (a_Var_f x) )   =  (a_App b psi0 (a_Var_f x)) )  )  ->
     AnnDefEq G psi (g_Eta b)  ( (a_Abs psi0 A a) )  b
 | An_EtaC : forall (L:vars) (G:context) (psi:grade) (b:tm) (psi0:grade) (phi:constraint) (a B:tm),
     AnnTyping G psi b (a_CPi psi0 phi B) ->
      ( forall c , c \notin  L  ->  (  ( open_tm_wrt_co a (g_Var_f c) )   =  (a_CApp b (g_Var_f c)) )  )  ->
     AnnDefEq G psi (g_Eta b)  ( (a_CAbs psi0 phi a) )  b
with AnnCtx : context -> Prop :=    (* defn AnnCtx *)
 | An_Empty : 
     AnnCtx  nil 
 | An_ConsTm : forall (G:context) (x:tmvar) (psi0:grade) (A:tm),
     AnnCtx G ->
     AnnTyping  (meet_ctx_l   q_C    G )   q_C  A a_Star ->
      ~ AtomSetImpl.In  x  (dom  G )  ->
     AnnCtx  (( x ~ ( psi0 , Tm  A )) ++  G ) 
 | An_ConsCo : forall (G:context) (c:covar) (psi0:grade) (phi:constraint),
     AnnCtx G ->
     AnnPropWff  (meet_ctx_l   q_C    G )   q_C  phi ->
      ~ AtomSetImpl.In  c  (dom  G )  ->
     AnnCtx  (( c ~ ( psi0 , Co  phi )) ++  G ) 
with AnnSig : sig -> Prop :=    (* defn AnnSig *)
 | An_Sig_Empty : 
     AnnSig  nil 
 | An_Sig_ConsAx : forall (S:sig) (F:tyfam) (a:tm) (psi0:grade) (A:tm),
     AnnSig S ->
     AnnTyping  nil   q_C  A a_Star ->
     AnnTyping  nil  psi0 a A ->
      ~ AtomSetImpl.In  F  (dom  S )  ->
     AnnSig  (( F ~ ( psi0 , Ax a A ))++ S ) .

(* defns Jred *)
Inductive head_reduction : context -> tm -> tm -> Prop :=    (* defn head_reduction *)
 | An_AppLeft : forall (G:context) (a:tm) (psi0:grade) (b a':tm),
     lc_tm b ->
     head_reduction G a a' ->
     head_reduction G (a_App a psi0 b) (a_App a' psi0 b)
 | An_AppAbs : forall (G:context) (psi0:grade) (A w a:tm),
     lc_tm a ->
     Value  ( (a_Abs psi0 A w) )  ->
     head_reduction G (a_App  ( (a_Abs psi0 A w) )  psi0 a)  (open_tm_wrt_tm  w   a ) 
 | An_CAppLeft : forall (G:context) (a:tm) (g:co) (a':tm),
     lc_co g ->
     head_reduction G a a' ->
     head_reduction G (a_CApp a g) (a_CApp a' g)
 | An_CAppCAbs : forall (G:context) (psi0:grade) (phi:constraint) (b:tm) (g:co),
     lc_constraint phi ->
     lc_tm (a_CAbs psi0 phi b) ->
     lc_co g ->
     head_reduction G (a_CApp  ( (a_CAbs psi0 phi b) )  g)  (open_tm_wrt_co  b   g ) 
 | An_Axiom : forall (G:context) (F:tyfam) (a:tm) (psi0:grade) (A:tm),
      binds  F  ( psi0 , (Ax  a A ))   an_toplevel   ->
     head_reduction G (a_Fam F) a
 | An_ConvTerm : forall (G:context) (a:tm) (g:co) (a':tm),
     lc_co g ->
     head_reduction G a a' ->
     head_reduction G (a_Conv a g) (a_Conv a' g)
 | An_Combine : forall (G:context) (v:tm) (g1 g2:co),
     lc_co g1 ->
     lc_co g2 ->
     Value v ->
     head_reduction G (a_Conv  ( (a_Conv v g1) )  g2) (a_Conv v  ( (g_Trans g1 g2) ) )
 | An_Push : forall (G:context) (v:tm) (g:co) (psi0:grade) (b b':tm) (g':co) (psi:grade) (A1 B1 A2 B2:tm),
     Value v ->
     AnnDefEq  (meet_ctx_l   q_C    G )  psi g (a_Pi psi0 A1 B1) (a_Pi psi0 A2 B2) ->
      ( b'  =  (a_Conv b (g_Sym  ( (g_PiFst g) ) )) )  ->
      ( g'  =  (g_PiSnd g (g_Refl2 b' b  ( (g_PiFst g) ) )) )  ->
     head_reduction G (a_App  ( (a_Conv v g) )  psi0 b) (a_Conv  ( (a_App v psi0 b') )  g')
 | An_CPush : forall (G:context) (v:tm) (g g1 g1' g':co) (psi psi0:grade) (phi1:constraint) (A1:tm) (phi2:constraint) (A2:tm),
     Value v ->
     AnnDefEq  (meet_ctx_l   q_C    G )  psi g (a_CPi psi0 phi1 A1) (a_CPi psi0 phi2 A2) ->
      ( g1'  =  (g_Cast g1 (g_Sym  ( (g_CPiFst g) ) )) )  ->
      ( g'  =  (g_CPiSnd g g1' g1) )  ->
     head_reduction G (a_CApp  ( (a_Conv v g) )  g1) (a_Conv  ( (a_CApp v g1') )  g').


(** infrastructure *)
Hint Constructors CoercedValue Value value_type consistent erased_constraint erased_tm P_sub ctx_sub ECtx CoGrade CGrade Grade CoGEq CEq GEq CParProp CPar ParProp Par multipar multipar_prop Beta reduction_in_one reduction PropWff Typing Iso CDefEq DefEq Ctx Sig AnnPropWff AnnTyping AnnIso AnnDefCEq AnnDefEq AnnCtx AnnSig head_reduction lc_co lc_brs lc_tm lc_constraint lc_sort lc_sig_sort : core.


