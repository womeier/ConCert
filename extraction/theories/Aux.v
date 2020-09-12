From Coq Require Import Arith.
From Coq Require Import Bool.
From Coq Require Import List.
From Equations Require Import Equations.
From MetaCoq Require Import utils.

Derive Signature for Alli.
Derive Signature for Forall.
Derive Signature for Forall2.
Derive Signature for OnOne2.

Ltac propify :=
  unfold is_true in *;
  repeat
    match goal with
    | [H: context[Nat.eqb _ _ = false] |- _] => rewrite Nat.eqb_neq in H
    | [H: context[Nat.eqb _ _ = true] |- _] => rewrite Nat.eqb_eq in H
    | [H: context[Nat.ltb _ _ = false] |- _] => rewrite Nat.ltb_ge in H
    | [H: context[Nat.ltb _ _ = true] |- _] => rewrite Nat.ltb_lt in H
    | [H: context[Nat.leb _ _ = false] |- _] => rewrite Nat.leb_gt in H
    | [H: context[Nat.leb _ _ = true] |- _] => rewrite Nat.leb_le in H
    | [H: context[andb _ _ = false] |- _] => rewrite Bool.andb_false_iff in H
    | [H: context[andb _ _ = true] |- _] => rewrite Bool.andb_true_iff in H
    | [H: context[negb _ = false] |- _] => rewrite Bool.negb_false_iff in H
    | [H: context[negb _ = true] |- _] => rewrite Bool.negb_true_iff in H
    | [H: context[orb _ _ = false] |- _] => rewrite Bool.orb_false_iff in H
    | [H: context[orb _ _ = true] |- _] => rewrite Bool.orb_true_iff in H
    | [|- context[Nat.eqb _ _ = false]] => rewrite Nat.eqb_neq
    | [|- context[Nat.eqb _ _ = true]] => rewrite Nat.eqb_eq
    | [|- context[Nat.ltb _ _ = false]] => rewrite Nat.ltb_ge
    | [|- context[Nat.ltb _ _ = true]] => rewrite Nat.ltb_lt
    | [|- context[Nat.leb _ _ = false]] => rewrite Nat.leb_gt
    | [|- context[Nat.leb _ _ = true]] => rewrite Nat.leb_le
    | [|- context[andb _ _ = false]] => rewrite Bool.andb_false_iff
    | [|- context[andb _ _ = true]] => rewrite Bool.andb_true_iff
    | [|- context[negb _ = false]] => rewrite Bool.negb_false_iff
    | [|- context[negb _ = true]] => rewrite Bool.negb_true_iff
    | [|- context[orb _ _ = false]] => rewrite Bool.orb_false_iff
    | [|- context[orb _ _ = true]] => rewrite Bool.orb_true_iff
    end.

Definition alli {X} (f : nat -> X -> bool) : nat -> list X -> bool :=
  fix alli (n : nat) (xs : list X) :=
    match xs with
    | [] => true
    | x :: xs => f n x && alli (S n) xs
    end.

Lemma alli_Alli {A} (f : nat -> A -> bool) (n : nat) (l : list A) :
  alli f n l -> Alli (fun n a => f n a) n l.
Proof.
  intros a.
  induction l in n, a |- *.
  - constructor.
  - cbn in *.
    propify.
    constructor; [easy|].
    now apply IHl.
Qed.

Lemma Alli_alli {A} (f : nat -> A -> bool) (n : nat) (l : list A) :
  Alli (fun n a => f n a) n l -> alli f n l.
Proof.
  intros a.
  induction l in n, a |- *.
  - easy.
  - depelim a.
    cbn.
    now rewrite i, IHl.
Qed.

Lemma Forall_snoc {A} (P : A -> Prop) (l : list A) (a : A) :
  Forall P (l ++ [a]) ->
  Forall P l /\ P a.
Proof.
  intros all.
  apply Forall_app in all.
  intuition.
  now inversion H0.
Qed.
