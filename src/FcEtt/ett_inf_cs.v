(* Completing the infrastructure of ett

   Current additions:
   - polymorphic functions (via canonical structures)
*)

Require Import FcEtt.ett_inf.
Require Import FcEtt.imports.

(**** Operators on syntactic sorts ****)

Module Operators.

  Module Close.

    Record class1 (ssort : Type) (vartype : Type) :=  Class1 {close_ : vartype -> ssort -> ssort; close_rec_ : nat -> vartype -> ssort -> ssort}.

    Record class (ssort : Type) := Class {class_tm : class1 ssort tmvar; class_co : class1 ssort covar}.

    Arguments Class {ssort} class_tm class_co.
    Arguments Class1 {ssort vartype} close_ close_rec_.

  End Close.


  Module Erase.

    Record class (ssort : Type) := Class {erase_ssort : ssort -> role -> ssort}.

    Arguments Class {ssort} erase_ssort.

  End Erase.


  Module FV.

    Record class (ssort : Type) := Class {fv_tm : ssort -> atoms; fv_co : ssort -> atoms}.

    Arguments Class {ssort} fv_tm fv_co.

  End FV.

  Structure type := Pack {stxsort : Type; class_close : Close.class stxsort; class_Erase : Erase.class stxsort; class_Fv : FV.class stxsort}.

End Operators.

(* Export Operators.Theory. *)

Definition tm_Closecl         : Operators.Close.class tm         := Operators.Close.Class (Operators.Close.Class1 close_tm_wrt_tm close_tm_wrt_tm_rec)                 (Operators.Close.Class1 close_tm_wrt_co close_tm_wrt_co_rec).
Definition co_Closecl         : Operators.Close.class co         := Operators.Close.Class (Operators.Close.Class1 close_co_wrt_tm close_co_wrt_tm_rec)                 (Operators.Close.Class1 close_co_wrt_co close_co_wrt_co_rec).
Definition brs_Closecl        : Operators.Close.class brs        := Operators.Close.Class (Operators.Close.Class1 close_brs_wrt_tm close_brs_wrt_tm_rec)               (Operators.Close.Class1 close_brs_wrt_co close_brs_wrt_co_rec).
Definition constraint_Closecl : Operators.Close.class constraint := Operators.Close.Class (Operators.Close.Class1 close_constraint_wrt_tm close_constraint_wrt_tm_rec) (Operators.Close.Class1 close_constraint_wrt_co close_constraint_wrt_co_rec).

Definition erase_co (_ : co) (_ : role) := g_Triv.

Definition tm_Erasecl         : Operators.Erase.class tm         := Operators.Erase.Class erase_tm.
Definition co_Erasecl         : Operators.Erase.class co         := Operators.Erase.Class erase_co.
Definition brs_Erasecl        : Operators.Erase.class brs        := Operators.Erase.Class erase_brs.
Definition constraint_Erasecl : Operators.Erase.class constraint := Operators.Erase.Class erase_constraint.

Definition tm_FVcl         : Operators.FV.class tm         := Operators.FV.Class fv_tm_tm_tm         fv_co_co_tm.
Definition co_FVcl         : Operators.FV.class co         := Operators.FV.Class fv_tm_tm_co         fv_co_co_co.
Definition brs_FVcl        : Operators.FV.class brs        := Operators.FV.Class fv_tm_tm_brs        fv_co_co_brs.
Definition constraint_FVcl : Operators.FV.class constraint := Operators.FV.Class fv_tm_tm_constraint fv_co_co_constraint.

Canonical Structure tm_OpsTy         : Operators.type := Operators.Pack tm_Closecl         tm_Erasecl         tm_FVcl.
Canonical Structure co_OpsTy         : Operators.type := Operators.Pack co_Closecl         co_Erasecl         co_FVcl.
Canonical Structure brs_OpsTy        : Operators.type := Operators.Pack brs_Closecl        brs_Erasecl        brs_FVcl.
Canonical Structure constraint_OpsTy : Operators.type := Operators.Pack constraint_Closecl constraint_Erasecl constraint_FVcl.
