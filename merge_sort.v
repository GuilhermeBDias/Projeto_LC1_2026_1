(* begin hide *)
Require Import List.
Import ListNotations.
Require Import Recdef.
Require Import Arith.
Require Import Lia.
Require Import Sorted.
Require Import Permutation.
(* end hide *)

(** Neste trabalho formalizaremos a correção do algoritmo [mergesort]. Esta formalização envolve diversas etapas que incluem a definição de diferentes funções.  *)

(** O algoritmo [merge] a seguir recebe um par de listas ordenadas como argumento. A função [len] abaixo, define o tamanho de um par de listas: *)

Definition len (p:list nat * list nat) := length (fst p) + length (snd p).

Function merge (p: list nat * list nat) {measure len p}:=
  match p with
  | ([], l2) => l2
  | (l1, []) => l1
  | (h1::l1, h2::l2) =>
      if h1 <=? h2
      then h1::(merge (l1,h2::l2))
                else h2::(merge (h1::l1,l2))
                end.
Proof.
  - auto.
  - intros. unfold len. simpl. lia.
Qed.

(** A seguir apresentamos algumas definições e lemas que podem ser úteis. Eles podem ser modificados ou removidos de acordo com a sua estratégia de prova. Outros resultados auxiliares podem ser adicionados, se necessário. *)

Definition le_all x l := forall y, In y l -> x <= y.

(** Este lemma tem como objetivo mostrar que, se uma lista já está ordenada e 
um elemento "x" é menor ou igual a todos os elementos da lista,
 então adicionar "x" no início preserva a ordenação *)
 
Lemma le_all_sorted: forall l x, Sorted le l -> le_all x l -> Sorted le (x::l).
Proof.
  intros l x Hsorted Hall.
  constructor.
  - assumption.
  - destruct l as [|a l'].
    + constructor.
    + constructor.
    apply Hall.
    left.
    reflexivity.
Qed.
  
 
Lemma sorted_le_all: forall l x, Sorted le (x::l) -> le_all x l.
Proof.
  induction l. Admitted.

Lemma merge_permuta: forall (l1 l2: list nat), Permutation (l1 ++ l2) (merge(l1,l2)).
Proof.
  induction l1. Admitted.

Lemma merge_correto: forall l1 l2, Sorted le l1 -> Sorted le l2 -> Sorted le (merge (l1,l2)).
Proof.
  induction l1 as [ | h1 l1']. Admitted.

(** O algoritmo [mergesort] é definido como a seguir: *)

Function mergesort (l: list nat) {measure length l} :=
  match l with
  | [] => []
  | [h] => [h]
  | h1::h2::l' =>
      let l1_half := Nat.div2 (length l) in
      let l1 := firstn l1_half l in
      let l2 := skipn l1_half l in
      merge(mergesort l1 , mergesort l2)
  end.
Proof.
  - intros. rewrite length_skipn. apply Nat.sub_lt. apply Nat.le_div2_diag_l. simpl. apply Nat.lt_0_succ.
  - intros. rewrite length_firstn. apply Nat.le_lt_trans with (Nat.div2 (length (h1 :: h2 :: l'))).
    + lia.
    + apply Nat.lt_div2. simpl. lia.
Qed.

(** A correção do algoritmo [mergesort] é obtida com a prova do teorema abaixo: *)

Theorem mergesort_correto: forall l, Sorted le (mergesort l) /\ Permutation l (mergesort l).
Proof. Admitted.


(** Repositório: %\url{https://github.com/flaviodemoura/merge_sort}% *)
