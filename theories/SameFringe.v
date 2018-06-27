(** Author: Ralph Matthes (IRIT - CNRS and Univ. of Toulouse) *)

(** * Same Fringe problem solved with non-strictly positive inductive types *)

(** The ideas for the following program have been communicated to me by Olivier Danvy on March 14, 2002.
    This was by way of an SML program. *)

From TypingFlags Require Import Loader.
Require Import Init.Nat.

(** binary trees with only leaf labels *)
Inductive tree :=
| leaf : nat -> tree
| node : tree -> tree -> tree.

Unset Guard Checking.
Inductive Cor :=
| Over : Cor
| Next : nat -> ((Cor -> bool) -> bool) -> Cor.
Set Guard Checking.

Unset Guard Checking.
Fixpoint skim (c1 c2: Cor) {struct c1}: bool :=
  match c1, c2 with
  | Over, Over => true
  | Over, Next n f => false
  | Next n f, Over => false
  | Next n1 f1, Next n2 f2 => if (negb (eqb n1 n2)) then false else f1 (fun c => f2 (skim c))
  end.
Set Guard Checking.

Fixpoint walk (t: tree)(k: Cor -> bool)(f: (Cor -> bool) -> bool): bool:=
  match t with
  | leaf n => k (Next n f)
  | node l r => walk l k (fun k1 => walk r k1 f)
  end.

Definition canf: (Cor -> bool) -> bool := fun k => k Over.

Definition init (t: tree)(k: Cor -> bool): bool := walk t k canf.

Definition smf (t1 t2: tree): bool := init t1 (fun c1 => init t2 (skim c1)).


Definition ex1 := smf (node (leaf 1) (node (leaf 2) (leaf 3)))
                      (node (node (leaf 1) (leaf 2)) (leaf 3)).
Definition ex2 := smf (node (leaf 1) (node (leaf 2) (leaf 3)))
                      (node (node (leaf 1) (leaf 2)) (leaf 4)).
Definition ex3 := smf (node (leaf 1) (node (leaf 0) (leaf 3)))
                      (node (node (leaf 1) (leaf 2)) (leaf 3)).
Definition ex4 := smf (node (leaf 1) (node (leaf 2) (leaf 3)))
                      (node (leaf 1) (node (leaf 2) (leaf 4))).


Compute ex1. (* true *)
Compute ex2. (* false *)
Compute ex3. (* false *)
Compute ex4. (* false *)

Print Assumptions smf.
