
Inductive ilist {A:Set} : nat -> Set :=
| iNil : ilist O
| iCons : forall n, A -> ilist n -> ilist (S n).

Fixpoint app' {A:Set} n1 (ls1 : @ilist A n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 in (ilist n1) return (ilist (n1 + n2)) with
      | iNil => ls2
      | iCons _ x ls1' => iCons _ x (app' _ ls1' _ ls2)
    end.

Fixpoint addLists n (l1:@ilist nat n) (l2:@ilist nat n) : ilist n :=
  match l1 in (ilist n), l2 in (ilist n) return (ilist n) with
      |iCons a h1 t1, iCons b h2 t2 => iCons _ (h1+h2) (addLists _ t1 t2)
      |_, _ => iNil
  end. 

(*An attempt to formalize the result presented in: 
**"Complexity of and Algorithms for Borda Manipulation" - 
**http://www.cs.toronto.edu/~jdavies/daviesAAAI11.pdf*)

Require Export Coq.Sorting.Permutation. 
Require Export Omega.     
(*Require Export List.
Export ListNotations. *)

(*indexed lists based on material from http://adam.chlipala.net/cpdt/html/MoreDep.html*)
Inductive ilist {A:Type} : nat -> Type :=
  | iNil : ilist O
  | iCons : forall n, A -> ilist n -> ilist (S n).

Notation " [ ] " := iNil : list_scope.
Notation " [ x ] " := (iCons x iNil) : list_scope.
Notation " [ x ; .. ; y ] " := (iCons x .. (iCons y iNil) ..) : list_scope.

Fixpoint app' n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 in (ilist n1) return (ilist (n1 + n2)) with
      | iNil => ls2
      | iCons _ x ls1' => iCons x (app' ls1' ls2)
    end.

Fixpoint iapp {A:Type} (n1:nat) (l1 : ilist n1) (n2:nat) (l2 : ilist n2) : ilist (n1+n2) :=
  match l1 in ilist n1 return (ilist (n1 + n2)) with
      |iCons n1' hd tl => iCons (n1'+n2) hd (iapp n1' tl n2 l2)
      |iNil => l2
  end. 


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

Theorem eqLengthsVecAdd : forall l1 l2 l3, length l1 = length l2 -> length l2 = length l3 ->
                                      exists l, addThreeVectors l1 l2 l3 l. 
Proof.
  induction l1; intros. 
  {destruct l2; destruct l3; simpl in *; try omega. exists nil. constructor. }
  {destruct l2; destruct l3; simpl in *; try omega. inv H. inv H0. apply IHl1 in H1; auto. 
   invertHyp. exists (a+n+n0::x). constructor. auto. }
Qed. 

Theorem reduceMidEqLengths : forall l C l' n, reduceMid n C l l' -> length l = length l'. 
Proof.
  intros. induction H; auto. simpl. rewrite IHreduceMid. auto. 
Qed. 

Lemma zgtz : 0 > 0 -> False.
  omega. 
Qed.

Definition pred_strong2 (s : {n : nat | n > 0}) : nat :=
  match s with
    | exist O pf => match zgtz pf with end
    | exist (S n') _ => n'
  end.

Theorem consLengthEq : forall (A:Type) (h1 h2 :A) t1 t2,
                         length (h1::t1) = length (h2::t2) -> length t1 = length t2. 
Proof. intros. inv H. auto. 
Qed. 

Fixpoint vecAdd v1 v2 (prf:length v1 = length v2) :=
  match v1 with
      |h1::t1 => match v2 with
                    |h2::t2 => h1+h2::vecAdd t1 t2 (consLengthEq nat h1 h2 t1 t2 prf)
                    |_ => nil
                end
      |_ => nil
  end. 


, v2 with
      |h1::t1, h2::t2 => 
      |_,_ => nil
  end. 

Theorem BordaTwoManipulatorsNPC : forall l l', reduce l l' -> (PermSum l <-> twoManipulation l').
Proof.
  intros. split; intros. 
  {inv H. inv H0. invertHyp. copy H3.
   


   eapply twoManipulation_ with (v1 := 2 + length l::x++[0; S (length l)])
                                  (v2 := 2 + length l::x0++[0; S (length l)]).
   eapply eqLengthsVecAdd. 


















