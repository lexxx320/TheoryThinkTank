(*An attempt to formalize the result presented in: 
**"Complexity of and Algorithms for Borda Manipulation" - 
**http://www.cs.toronto.edu/~jdavies/daviesAAAI11.pdf*)

Require Export Coq.Sorting.Permutation. 
Require Export Omega.   
Require Export List. 
Export ListNotations. 

Definition optGTE (n:nat) (o:option nat) : Prop :=
  match o with
      |None => True
      |Some n' => n >= n'
  end. 

(*specifies that a list is monotonically increasing and adds up to (n*(n+1))*)
Inductive PermSumWF (n:nat) (i:nat) (k:option nat) : list nat -> Prop :=
|permSumNil : n * (S n) = i -> PermSumWF n i k nil
|permSumCons : forall hd tl, optGTE hd k -> PermSumWF n (hd+i) (Some hd) tl ->
                        PermSumWF n i k (hd::tl)
. 

(*specifies that sigma(i) + pi(i) = X__i*)
Inductive addUp : list nat -> list nat -> list nat -> Prop :=
|addUpNil : addUp nil nil nil
|addUpCons : forall hd1 hd2 hd3 tl1 tl2 tl3, 
               hd1+hd2 = hd3 -> addUp tl1 tl2 tl3 ->
               addUp (hd1::tl1) (hd2::tl2) (hd3::tl3). 

Definition PermSum l := exists sigma pi, PermSumWF (length l) 0 None l /\ Permutation sigma l /\ 
                                         Permutation pi l /\ addUp sigma pi l. 

(*Reduce a list of PermSum natural numbers to a set of non-manipulator votes*)
(*n is the number of candidates and C is some (arbitrary?) constant*)
(*

         --------------------- reduceMidNil
         reduceMid n C nil nil


         reduceMid n C l l'      
----------------------------------------- reduceMidCons
 reduceMid n C (x__i::l) (4+2*n-x__i+C::l')

*)
Inductive reduceMid (n:nat) (C:nat) : list nat -> list nat -> Prop :=
|reduceMidNil : reduceMid n C nil nil
|reduceMidCons : forall x__i l l', reduceMid n C l l' -> 
                            reduceMid n C (x__i::l) (4 + 2*n - x__i + C::l').

(*

  reduceMid (length l) C l l'     y <= C
 ---------------------------------------- reduce
     reduce l (C::l'++[2*(n+2) + C; y]

*)



Inductive reduce : list nat -> list nat -> Prop :=
|reduce_ : forall C y l l' n, y <= C -> n = length l -> reduceMid n C l l' ->
                         reduce l (C:: (l' ++ [4+2*n+C; y])).

Inductive allLTE (i:nat) : list nat -> Prop :=
|allLTENil : allLTE i nil
|allLTECons : forall hd tl, i >= hd -> allLTE i tl -> allLTE i (hd::tl).

Inductive firstCandidateWins : list nat -> Prop :=
|firstCandidateWins_ : forall hd tl, allLTE hd tl -> firstCandidateWins (hd::tl). 

Theorem lengthEqCons : forall (A:Type)(h1 h2 :A)t1 t2, length(h1::t1) = length (h2::t2) ->
                                                  length t1 = length t2. 
Proof. intros. simpl in H. inversion H. reflexivity. Qed. 

Theorem lengthsNeq : forall (A:Type) (h:A) t, length (h::t) = length (@nil A) -> False. 
Proof.
  intros. inversion H. Qed.

Theorem lengthsNeq' : forall (A:Type) (h:A) t, length (@nil A) = length (h::t) -> False. 
Proof.
  intros. inversion H. Qed.
 
Fixpoint addVecs (v1:list nat) (v2:list nat) : length v1 = length v2 -> list nat :=
  match v1 as v1', v2 as v2' with
    |h1::t1, h2::t2 => (fun prf : length (h1::t1) = length (h2::t2) => 
                         h1+h2::addVecs t1 t2 (lengthEqCons nat h1 h2 t1 t2 prf))
    |nil, nil => fun _ => nil
    |h::t, nil => fun prf : length (h::t)=length nil => 
                      match lengthsNeq nat h t prf with end
    |nil, h::t => fun prf : length nil=length (h::t) =>
                   match lengthsNeq' nat h t prf with end
  end. 

Inductive addThreeVectors : list nat -> list nat -> list nat -> list nat -> Prop :=
|vAddNil : addThreeVectors nil nil nil nil
|vAddCons : forall h1 h2 h3 t1 t2 t3 t4,
              addThreeVectors t1 t2 t3 t4 ->
              addThreeVectors (h1::t1) (h2::t2) (h3::t3) (h1+h2+h3::t4). 

Inductive twoManipulation (nonManipVotes : list nat) : Prop :=
|twoManipulation_ : forall v1 v2 newVotes, 
                      addThreeVectors v1 v2 nonManipVotes newVotes ->
                      firstCandidateWins newVotes -> twoManipulation nonManipVotes. 

Ltac inv H := inversion H; subst; clear H. 
Ltac invertHyp :=
  match goal with
      |H:exists x, ?P |- _ => inv H; try invertHyp
      |H:?P /\ ?Q |- _ => inv H; try invertHyp
  end. 
Ltac copy H := 
  match type of H with
      |?X => assert(X) by auto
  end. 

Theorem existsVecAdd : forall v1 v2 v3, length v1 = length v2 -> length v2 = length v3 ->
                                   exists v4, addThreeVectors v1 v2 v3 v4. 
Proof.
  induction v1; intros. 
  {destruct v2; destruct v3; simpl in *; try omega. exists nil. constructor. }
  {destruct v2; destruct v3; simpl in *; try omega. inv H. inv H0. 
   apply IHv1 in H1; auto. invertHyp. exists (a+n+n0::x). constructor. auto. }
Qed. 

Theorem reduceMidEqLengths : forall l C l' n, reduceMid n C l l' -> length l = length l'. 
Proof.
  intros. induction H; auto. simpl. rewrite IHreduceMid. auto. 
Qed. 


Theorem addVecsApp : forall l1 l1' l2 l2' l3 l3' l4,
                     length l1 = length l2 -> length l2 = length l3 ->
                     addThreeVectors (l1++l1') (l2++l2') (l3++l3') l4 ->
                     exists v v', 
                     addThreeVectors l1 l2 l3 v /\ addThreeVectors l1' l2' l3' v' /\
                     v++v' = l4. 
Proof.
  induction l1; intros. 
  {destruct l2; destruct l3; simpl in *; try omega. exists nil. exists l4. split. constructor. 
   split. auto. simpl. auto. }
  {destruct l2; destruct l3; simpl in *; try omega. inv H1. inv H. inv H0. 
   apply IHl1 in H9; auto.invertHyp. exists (a+n+n0::x). exists x0. split. constructor. 
   auto. split; auto. }
Qed. 
                                                                         
Theorem allLTEApp : forall n l1 l2, allLTE n l1 -> allLTE n l2 ->
                               allLTE n (l1++l2). 
Proof.
  intros. induction H. simpl. auto. simpl. constructor; auto. 
Qed. 

Theorem BordaTwoManipulatorsNPC : forall l l', reduce l l' ->
                                          (PermSum l <-> twoManipulation l').
Proof.
  intros. split; intros. 
  {inv H. inv H0. invertHyp. copy H3. apply reduceMidEqLengths in H4. 
   copy H0. copy H2. apply Permutation_length in H6. apply Permutation_length in H7.
   assert(exists v, addThreeVectors (2 + length l::x++[0; S (length l)])
                               (2 + length l::x0++[0; S (length l)]) 
                               (C::l'0++[4+2*(length l)+C; y]) v). 
   apply existsVecAdd; auto. simpl. repeat rewrite app_length. simpl. 
   rewrite H6. rewrite H7. auto. simpl. repeat rewrite app_length. simpl. 
   rewrite H7. rewrite H4. auto. invertHyp. econstructor. eauto. 
   inv H9. simpl. repeat rewrite <- plus_n_Sm. constructor. 
   apply addVecsApp in H16; try omega. invertHyp. inv H9. inv H17. inv H16. 
   apply allLTEApp. Focus 2. constructor. omega. constructor. omega. constructor. 
   




















