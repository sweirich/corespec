Require Import FcEtt.imports.

(* Simple auxiliary functions *)

Definition zip : `{list A → list B → list (A * B)} := 
  fix zip _ _ a b := 
    match a, b with
      | nil, _ => nil
      | _, nil => nil
      | x :: xs, y :: ys => (x, y) :: zip _ _ xs ys
    end.
