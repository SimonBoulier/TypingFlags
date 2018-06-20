From TypingFlags Require Import Loader.

Fail Definition T := let T := Type in (T : T).

Set Type In Type.

Print Typing Flags.

Definition T := let T := Type in (T : T).




Section t.

  Unset Guard Checking.

  Variable b : bool.

  Fixpoint f (n : nat) {struct n} : True :=
    match n with
    | O => I
    | S _ => if b then f n else I
    end.

  Print Typing Flags.
End t.


Fail Definition g := Eval lazy in (f true).

Unset Guard Checking.
Definition g := Eval lazy in (f true).

(* SetGuardChecking. *)
Inductive T2 :=
  l : (T2 -> False) -> T2.

Goal False.
  assert T2.
  constructor. intro.
  remember H.
  destruct H. auto.
  remember H.
  destruct H. auto.
(* Defined. (* Does not terminate? *) *)  
Qed.

Check g.

Compute (f false 12).

Unset Type In Type.
Set Guard Checking.
Definition ff := f.
Print Assumptions ff.
