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
  
 
 (** Este lema tem como objetivo mostrar que, se uma lista iniciada por "x" está ordenada, 
 então "x" é menor ou igual a todos os elementos do restante da lista. *)
 
Lemma sorted_le_all: forall l x, Sorted le (x::l) -> le_all x l.
Proof.
  induction l as [|a l' IH].
  - intros x Hsorted. 
    unfold le_all. 
    intros y Hy. 
    inversion Hy.
    
  - intros x Hsorted.
    inversion Hsorted.
    unfold le_all.
    intros y Hy.
    
    destruct Hy as [Hy | Hy].
    + inversion H2.
      subst.
      assumption.
      
    + specialize (IH a H1).
      unfold le_all in IH.
      specialize (IH y Hy).
      inversion H2.
      lia.
Qed.

(**Lema Auxiliar para o merge_permuta, opera diretamente no par "p"*)
Lemma merge_permuta_aux : forall p, Permutation (fst p ++ snd p) (merge p).
Proof.
  intros p.
  functional induction (merge p).
  - simpl. apply Permutation_refl.
  - simpl. rewrite app_nil_r. apply Permutation_refl.
  - simpl. constructor. assumption.
  - simpl.
    eapply Permutation_trans with (l' := h2 :: h1 :: l1 ++ l2).
    + apply Permutation_sym.
      change (Permutation (h2 :: (h1 :: l1) ++ l2) ((h1 :: l1) ++ h2 :: l2)).
      apply Permutation_middle.
    + constructor. assumption.
Qed.

(** Este lema mostra que a função "merge" preserva todos os elementos das listas de entrada.
Ou seja, o resultado de "merge" é apenas uma reorganização da lista.*)

Lemma merge_permuta: forall (l1 l2: list nat), Permutation (l1 ++ l2) (merge(l1,l2)).
Proof.
  intros l1 l2.
  apply (merge_permuta_aux (l1, l2)).
Qed.

(**Lema Auxiliar operando no par para a indução funcional não quebrar*)

Lemma merge_correto_aux: forall p, Sorted le (fst p) -> Sorted le (snd p) -> Sorted le (merge p).
Proof.
  intros p. functional induction (merge p).
  
  - (*Caso 1 : ([], l2) -> retorna l2 que já sabemos que está ordenado*)
    intros _ H_sort2. assumption.
    
    (*Caso 2 : (l1, []) -> retorna l1 que já sabemos que está ordenado*)
  - intros H_sort1 _. assumption.
  
    (*Caso 3 : (h1::l1, h2::l2) onde h1 <= h2*)
  - intros H_sort1 H_sort2.
    inversion H_sort1 as [| ? ? H_sorted_l1 H_hdrel]; subst.
    apply le_all_sorted.
    + apply IHl; assumption.
    + unfold le_all. intros y Hy.
    apply Nat.leb_le in e0.
    
    assert (Hin: In y (l1 ++ h2 :: l2)).
    { eapply Permutation_in. apply Permutation_sym.
      apply merge_permuta. exact Hy. }
    
    apply in_app_or in Hin. destruct Hin as [Hy_l1 | Hy_l2].
    * 
      assert (H_h1_y: h1 <= y).
      { apply (sorted_le_all l1 h1 H_sort1 y Hy_l1). }
      assumption.
      
    *
      destruct Hy_l2 as [Heq | H_in_l2].
      -- subst. lia.
      -- assert (H_h2_y: h2 <= y).
         { apply (sorted_le_all l2 h2 H_sort2 y H_in_l2). }
         lia.
         
    (*Caso 4 : (h1::l1, h2::l2) onde h1 > h2*)
  - intros H_sort1 H_sort2.
    
    inversion H_sort2 as [| ? ? H_sorted_l2 H_hdrel]; subst.
    apply le_all_sorted.
    
    + apply IHl; assumption.
    
    + unfold le_all. intros y Hy.
    
    apply Nat.leb_gt in e0.
    
    assert (Hin: In y ((h1 :: l1) ++ l2)).
    { eapply Permutation_in. apply Permutation_sym. 
    apply merge_permuta. exact Hy. }
    
    apply in_app_or in Hin. destruct Hin as [Hy_l1 | Hy_l2].
    *
      destruct Hy_l1 as [Heq | H_in_l1].
      -- subst. lia.
      -- assert (H_h2_y: h1 <= y).
      { apply (sorted_le_all l1 h1 H_sort1 y H_in_l1). }
      lia.
    *
      assert (H_h2_y: h2 <= y).
      {apply (sorted_le_all l2 h2 H_sort2 y Hy_l2). }
      assumption.
Qed.

Lemma merge_correto: forall l1 l2, Sorted le l1 -> Sorted le l2 -> Sorted le (merge (l1,l2)).
Proof.
  intros l1 l2.
  apply (merge_correto_aux (l1, l2)).
Qed.

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
Proof. 

  intros l.
  functional induction (mergesort l).
  - (*Caso 1: lista vazia []*)
    split.
    + constructor.
    + apply Permutation_refl.
    
  - (*Caso 2: lista com um único elemento [h]*)
    split.
    + constructor. constructor. constructor.
    + apply Permutation_refl.
    
  - (*Caso 3: lista com  h1::h2::l' *)
    destruct IHl0 as [Hsort1 Hperm1].
    destruct IHl1 as [Hsort2 Hperm2].
    
    split.
    
    + (*Objetivo 1: Provar Sorted*)
      apply merge_correto; assumption.
      
    + (*Objetivo 2: Provar Permutation*)
      (*Queremos provar que a lista original (h1::h2::l') é permutação do resultado do merge.
        Sabemos que "firstn n l ++ skipn n l = l". Então vamos reescrever a lista original como a concatenação
        de suas duas metades (l1 ++ l2) *)
      rewrite <- firstn_skipn with (n := Nat.div2 (length (h1 :: h2 :: l'))) (l := h1 :: h2 :: l') at 1.
      
      (* Agora o objetivo tem a forma Permutation (l1 ++ l2) (merge (mergesort l1, mergesort l2))*)
      eapply Permutation_trans.
      
      *(* Como l1 permuta com mergesort l1, e l2 permuta com mergesort l2, a concatenação preserva a permutação *)
        apply Permutation_app.
        -- exact Hperm1.
        -- exact Hperm2.
        
      * (*Aplicação direta do lema merge_permuta*)
        apply merge_permuta.
Qed.

(** Repositório: %\url{https://github.com/flaviodemoura/merge_sort}% *)
