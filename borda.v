Require Omega.   
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.  
Require Export Coq.Sorting.Permutation. 

(*===================================Some Tactics===================================*)
Ltac inv H := inversion H; subst; clear H. 

Ltac invertHyp :=
  match goal with
      |H:exists x, ?P |- _ => inv H; try invertHyp
      |H:?P /\ ?Q |- _ => inv H; try invertHyp
  end. 

Ltac solveByInv :=
  match goal with
      |H:_ |- _ => solve[inv H]
  end. 

Ltac permTac := 
  match goal with
    | |- Permutation ?l ?l => auto
    | |- Permutation (?x::?y) (?x::?z) => apply perm_skip; permTac
    | |- Permutation (?x::?y::?z) (?y::?x::?z') => apply perm_swap; permTac
  end. 

(*===================================Number Partitioning===================================*)

Definition sum (l:list nat) := fold_left plus l 0. 

Definition numPartition (l : list nat) (k : nat) : Prop :=
  sum l = 2 * k /\ exists l1 l2, Permutation (l1++l2) l /\ sum l1 = k /\ sum l2 = k. 

Theorem numPart363 : numPartition [3; 6; 3] 6. 
Proof.
  unfold numPartition. split; auto. exists [3;3]. exists [6]. split; auto. simpl. permTac. 
Qed. 

Theorem noNumPart354 : ~ numPartition [3; 5; 4] 6. 
Proof.
  unfold not. intros. unfold numPartition in H. invertHyp. 
  destruct x; destruct x0; try solveByInv. destruct x; destruct x0. 
  {simpl in *. apply Permutation_length in H. solveByInv. }
  {destruct x0. 
   {unfold sum in *. simpl in *. subst. eapply Permutation_in with(x:=6)in H.
    inv H. solveByInv. inv H1. solveByInv. inv H. solveByInv. inv H1. simpl. auto. }
   {simpl in *. apply Permutation_length in H. solveByInv. }
  }
  {destruct x. 
   {unfold sum in *. simpl in *. subst. apply Permutation_in with (x:=6) in H. 
    inv H. solveByInv. inv H2. solveByInv. inv H. solveByInv. inv H2. simpl. auto. }
   {simpl in *. apply Permutation_length in H. simpl in *. inv H.
    rewrite app_length in H4. simpl in *. rewrite plus_comm in H4. solveByInv. }
  }
  {simpl in *. apply Permutation_length in H. simpl in *. rewrite app_length in H. 
   simpl in *. repeat rewrite <- plus_n_Sm in *. solveByInv. }
Qed. 

(*===================================Borda===================================*)

Definition candidate := nat.
Definition vote := list candidate.

Fixpoint round_up (v:vote) (c:candidate) (i:nat) :=
  match v with
      |hd::tl => if eq_nat_dec hd c
                 then i
                 else round_up tl c (i-1)
      |nil => 0
  end. 

Fixpoint round_down (v:vote) (c:candidate) :=
  match v with
      |hd::tl => if eq_nat_dec hd c
                 then length v
                 else round_down tl c
      |nil => 0
  end. 

(*n is the total number of candidates in the election *)
Fixpoint score_candidate_star (vs : list vote) (c:candidate) (n:nat) :=
  match vs with
      |hd::tl => round_up hd c n + score_candidate_star tl c n
      |nil => 0
  end. 

Fixpoint conduct_election (vs:list vote) (i:nat) (num_candidates : nat) :=
  match i with
      |0 => nil
      |S i' => score_candidate_star vs i num_candidates::conduct_election vs i' num_candidates
  end. 

Definition winner vs n := fold_left max (conduct_election vs n n) 0.

(*Check that the votes from the coalition of manipulators is consistent with 
**the weights specified*)
Fixpoint wfVotes (votes : list (list vote)) weights :=
  match votes, weights with
      |v::vs, w::ws => length v = w /\ wfVotes vs ws
      |nil, nil => True
      |_, _ => False
  end. 

Definition flatten {A:Type} (l:list (list A)) := 
  fold_left (@app A) l nil. 

(*k represents the weights of each manipulator, n is the number of candidates*)
(*the existentially quantified list l is a list of votes from the coalition of manipulators*)
Definition manipulate (vs:list vote) (p:candidate) (k:list nat) (n:nat) :=
  exists l, wfVotes l k /\ winner ((flatten l) ++ vs) n = p. 

Theorem ModifiedBorda3CandidateNPHard : forall (l:list nat) k p,
                                          numPartition l k -> (exists votes, manipulate votes p l 3).
Proof.
  intros. unfold numPartition in H. invertHyp. 
























































