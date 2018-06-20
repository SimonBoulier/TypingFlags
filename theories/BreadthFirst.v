From TypingFlags Require Import Loader.


Inductive tree :=
| leaf : nat -> tree
| node : tree -> nat -> tree -> tree.

Definition ex1 : tree.
Proof.
  refine (node _ 1 (leaf 3)).
  refine (node _ 2 _).
  - exact (node (leaf 6) 4 (leaf 7)).
  - refine (node _ 5 (leaf 9)).
    exact (node (leaf 10) 8 (leaf 11)).
Defined.

Require Import List.
Import ListNotations.

Fixpoint zip (l1 l2 : list (list nat)) : list (list nat) :=
  match l1, l2 with
  | [], l => l
  | l, [] => l
  | x :: l, x' :: l' => (x ++ x') :: (zip l l')
  end.

Fixpoint niveaux (t : tree) : list (list nat) :=
  match t with
  | leaf x => [[x]]
  | node t1 x t2 => [x] :: (zip (niveaux t1) (niveaux t2))
  end.

Definition breadthfirst t := concat (niveaux t).

Compute (niveaux ex1).
Compute (breadthfirst ex1).

Unset Guard Checking.
Inductive Cor :=
| Over : Cor
| Next : ((Cor -> list nat) -> list nat) -> Cor.
Set Guard Checking.

Definition apply (c : Cor) (k : Cor -> list nat) : list nat :=
  match c with
  | Over => k Over
  | Next f => f k
  end.

Fixpoint breadth (t : tree) (c : Cor) : Cor :=
  match t with
  | leaf n => Next (fun k => n :: apply c k)
  | node l n r => Next (fun k => n :: apply c (fun c1 => k (breadth l (breadth r c1))))
  end.

Unset Guard Checking.
Fixpoint ex (c : Cor) : list nat :=
  match c with
  | Over => []
  | Next f => f ex
  end.
Set Guard Checking.

Definition breadthfirst' t := ex (breadth t Over).

Compute (breadth (leaf 3) Over).
Compute (breadth (leaf 2) (breadth (leaf 3) Over)).
Compute (breadthfirst' ex1).
Print Assumptions breadthfirst'.
