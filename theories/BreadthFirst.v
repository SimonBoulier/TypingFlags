(** Authors:
Simon Boulier (INRIA) for the part before the def. of γ (without the simple lemmas)
Ralph Matthes (IRIT - CNRS and Univ. of Toulouse) for the three different methods of verification, all suggested in 1995
*)

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

Lemma zip_with_nil (l: list (list nat)): zip l [] = l.
Proof.
  destruct l; reflexivity.
Qed.

Lemma zip_assoc (l1 l2 l3: list (list nat)):
  zip l1 (zip l2 l3) = zip (zip l1 l2) l3.
Proof.
  revert l2 l3.
  induction l1.
  - reflexivity.
  - destruct l2.
    + reflexivity.
    + destruct l3.
      * reflexivity.
      * simpl.
        rewrite app_assoc.
        f_equal.
        apply IHl1.
Qed.

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

(** ** Verification of the algorithm in Martin Hofmann's own style *)

Fixpoint γ (ll:list (list nat))(c: Cor): Cor :=
  match ll with
  | [] => c
(*  | [l] => Next ( fun k => l ++ apply c k ) *)
  | l :: ll1 => Next (fun k => l ++ apply c (fun c1 => k (γ ll1 c1)))end.

Lemma MH_LemmaA (ll:list (list nat)): ex(γ ll Over) = concat ll.
Proof.
  induction ll.
  - reflexivity.
  - simpl.
    f_equal.
    exact IHll.
Qed.

(** the following is required to get the proofs with Coq through although
    a pencil-and-paper proof is possible that all these equations hold
     w.r.t. convertibility for all input lists *)
Require Import Logic.FunctionalExtensionality.

Lemma MH_LemmaB (ll ll':list (list nat))(c: Cor): γ ll (γ ll' c) = γ (zip ll ll') c.
Proof.
  revert ll' c.
  induction ll.
  - simpl. reflexivity.
  - induction ll'.
    + simpl. reflexivity.
    + simpl.
      intro c.
      f_equal.
      apply functional_extensionality; intro k.
      rewrite app_assoc.
      f_equal.
      f_equal.
      clear c IHll'.
      apply functional_extensionality; intro c.
      f_equal.
      apply IHll.
Qed.

Lemma MH_LemmaC (t: tree)(c: Cor): breadth t c = γ (niveaux t) c.
Proof.
  revert c.
  induction t.
  - simpl. reflexivity. (* thanks to eta-equality *)
  - simpl.
    assert( aux : forall (c: Cor), breadth t1 (breadth t2 c) = γ (zip (niveaux t1) (niveaux t2)) c).
    { intro c.
      rewrite IHt2.
      rewrite IHt1.
      apply MH_LemmaB.
    }
    intro c.
    f_equal.
    apply functional_extensionality; intro k.
    f_equal.
    f_equal.
    clear c.
    apply functional_extensionality; intro c.
    f_equal.
    apply aux.
Qed.

Theorem MH_Verif (t: tree): breadthfirst' t = breadthfirst t.
Proof.
  unfold breadthfirst', breadthfirst.
  rewrite MH_LemmaC.
  apply MH_LemmaA.
Qed.

Print Assumptions MH_Verif.


(** ** Verification of the algorithm in the style of Ulrich Berger *)
(** It does not need functional extensionality even in the Coq proof. *)

Unset Guard Checking.
Inductive rep: Cor -> list (list nat) -> Prop :=
| over: rep Over []
| next: forall (f: (Cor -> list nat) -> list nat)(l: list nat)(ll: list(list nat)), (forall (k: Cor -> list nat)(ll': list(list nat)), (forall (c: Cor)(ll1: list(list nat)), rep c ll1 -> k c = concat(zip ll' ll1)) -> f k = l ++ concat(zip ll' ll)) -> rep (Next f) (l::ll).
(** is a non-strictly positive inductive proposition - could equivalently be defined impredicatively thanks to impredicativity of Prop *)

Fixpoint rep_ind (R : Cor -> list (list nat) -> Prop)(HypO: R Over [])
         (HypN: forall (f: (Cor -> list nat) -> list nat)(l: list nat)(ll: list(list nat)), (forall (k: Cor -> list nat)(ll': list(list nat)), (forall (c: Cor)(ll1: list(list nat)), R c ll1 -> k c = concat(zip ll' ll1)) -> f k = l ++ concat(zip ll' ll)) -> R (Next f) (l::ll)) (c : Cor) (l : list (list nat))(Hyp: rep c l) {struct Hyp}: R c l :=
  match Hyp in (rep c0 l0) return (R c0 l0) with
  | over => HypO
  | next f0 l0 ll0 Hyp0 =>
    HypN _ _ _ (fun k ll' HypR => Hyp0 _ _ (fun c0 ll1 Hyp1 => HypR _ _ (rep_ind R HypO HypN c0 ll1 Hyp1)))
  end.
(* interactively:
Proof.
  refine (match Hyp in (rep c0 l0) return (R c0 l0) with
| over => HypO
| next f0 l0 ll0 Hyp0 => _
          end).
apply HypN.
intros k ll' HypR.
apply Hyp0.
intros c0 ll1 Hyp1.
apply HypR.
apply (rep_ind R HypO HypN c0 ll1 Hyp1).
Defined.
*)
Set Guard Checking.

Definition isextractor (R: Cor -> list (list nat) -> Prop)(ll: list(list nat))(k:Cor -> list nat): Prop :=
  forall (c: Cor)(ll1: list(list nat)), R c ll1 -> k c = concat(zip ll ll1).

Check (next: forall (f: (Cor -> list nat) -> list nat)(l: list nat)(ll: list(list nat)), (forall (k: Cor -> list nat)(ll': list(list nat)), isextractor rep ll' k -> f k = l ++ concat(zip ll' ll)) -> rep (Next f) (l::ll)).

Lemma UB_Lemma1: isextractor rep [] ex.
Proof.
  red.
  intros ? ? Hyp.
  induction Hyp.
  - reflexivity.
  - simpl.
    change ll with (zip [] ll).
    apply H.
    intros ? ? Hyp.
    exact Hyp.
Qed.

Lemma UB_Lemma2 (t: tree)(c: Cor)(ll: list(list nat)):
  rep c ll -> rep (breadth t c) (zip (niveaux t) ll).
Proof.
  revert c ll.
  induction t.
  - intros ? ?. intro Hyp; destruct Hyp.
    + simpl.
      apply next.
      intros ? ? Hyp1.
      simpl.
      f_equal.
      apply Hyp1.
      apply over.
    + simpl.
      apply next.
      intros ? ? Hyp1.
      simpl.
      f_equal.
      apply H.
      intros ? ? .
      apply Hyp1.
  - intros ? ?; intro Hyp; destruct Hyp.
    + simpl.
      apply next.
      intros ? ? Hyp1.
      simpl.
      f_equal.
      apply Hyp1.
      apply IHt1.
      replace (niveaux t2) with (zip (niveaux t2) []) by (apply zip_with_nil).
      apply IHt2.
      apply over.
    + simpl.
      apply next.
      intros ? ? Hyp1.
      simpl.
      f_equal.
      set (k0 := fun c1 : Cor => k (breadth t1 (breadth t2 c1))).
      assert (aux: isextractor rep (zip ll'(zip (niveaux t1) (niveaux t2))) k0).
      { red.
        intros ? ? Hyp2.
        unfold k0.
        set (aux2 := Hyp1 _ _ (IHt1 _ _ (IHt2 _ _ Hyp2))).
        rewrite aux2.
        f_equal.
        do 3 rewrite zip_assoc.
        reflexivity.
      }
      do 2 rewrite zip_assoc.
      apply H.
      intros ? ? Hyp2.
      red in aux.
      rewrite (aux _ _ Hyp2).
      f_equal.
      rewrite zip_assoc.
      reflexivity.
Qed.

Theorem UB_Verif (t: tree): breadthfirst' t = breadthfirst t.
Proof.
  unfold breadthfirst', breadthfirst.
  set (aux := UB_Lemma2 t _ _ over).
  rewrite (UB_Lemma1 _ _ aux).
  rewrite zip_with_nil.
  reflexivity.
Qed.

Print Assumptions UB_Verif.

(** ** Verification of the algorithm in the style of Anton Setzer *)

Definition Cor' := list( list nat -> list nat).

Fixpoint ϕ (c: Cor'): Cor :=
  match c with
  | [] => Over
  | g::ll => Next(fun k: Cor -> list nat => g(k(ϕ ll)))
  end.

(** "predicative" version of [breadth] *)
Fixpoint breadthp (t: tree)(c: Cor'): Cor' :=
  match t, c with
  | leaf n, [] => [cons n]
  | leaf n, g::l1 => (fun l:list nat => n::g l)::l1
  | node l n r, [] => (cons n) :: breadthp l (breadthp r [])
  | node l n r, g::l1 => (fun l:list nat => n::g l) :: breadthp l (breadthp r l1)
  end.

Lemma AS_Lemma1 (t: tree)(c: Cor'): breadth t (ϕ c) = ϕ(breadthp t c).
Proof.
  revert c.
  induction t; destruct c.
  - reflexivity.
  - reflexivity.
  - simpl.
    f_equal.
    apply functional_extensionality; intro k.
    do 2 f_equal.
    change Over with (ϕ []).
    rewrite (IHt2 []).
    apply IHt1.
  - simpl.
    f_equal.
    apply functional_extensionality; intro k.
    do 3 f_equal.
    rewrite IHt2.
    apply IHt1.
Qed.

Definition ψ (l: list nat): (list nat -> list nat) := fun l' => l ++ l'.
Definition ψ': list(list nat) -> Cor' := map ψ.

(** second refinement step for [breadthp] *)

Fixpoint breadthp' (t: tree)(ll: list(list nat)): list(list nat) :=
  match t, ll with
  | leaf n, [] => [[n]]
  | leaf n, l::ll => (n::l)::ll
  | node l n r, [] => [n] :: breadthp' l (breadthp' r [])
  | node l n r, l1::ll => (n::l1) :: breadthp' l (breadthp' r ll)
  end.

Lemma AS_Lemma2 (t: tree)(ll: list(list nat)): breadthp t (ψ' ll) = ψ'(breadthp' t ll).
Proof.
  revert ll.
  induction t; destruct ll.
  - reflexivity.
  - reflexivity.
  - simpl.
    f_equal. (* thanks to eta-equality *)
    change (@nil (forall _ : list nat, list nat)) with (ψ' []).
    rewrite (IHt2 []).
    apply IHt1.
  - simpl.
    f_equal. (* thanks to eta-equality *)
    rewrite IHt2.
    apply IHt1.
Qed.

Lemma AS_Lemma3 (t: tree)(ll: list(list nat)): breadthp' t ll = zip (niveaux t) ll.
Proof.
  revert ll.
  induction t; destruct ll.
  - reflexivity.
  - reflexivity.
  - simpl.
    f_equal.
    rewrite IHt2.
    rewrite zip_with_nil.
    apply IHt1.
  - simpl.
    f_equal.
    rewrite IHt2.
    rewrite <- zip_assoc.
    apply IHt1.
Qed.

Lemma AS_Lemma4 (ll: list(list nat)): ex(ϕ(ψ' ll)) = concat ll.
Proof.
  induction ll.
  - reflexivity.
  - simpl.
    rewrite IHll.
    reflexivity.
Qed.

Theorem AS_Verif (t: tree): breadthfirst' t = breadthfirst t.
Proof.
  unfold breadthfirst', breadthfirst.
  change Over with (ϕ []).
  rewrite AS_Lemma1.
  change (@nil (forall _ : list nat, list nat)) with (ψ' []).
  rewrite AS_Lemma2.
  rewrite AS_Lemma3.
  rewrite zip_with_nil.
  apply AS_Lemma4.
Qed.

Print Assumptions AS_Verif.
