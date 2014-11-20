Require Export Coq.Sorting.Permutation. 
Require Export Omega.   
Require Export List. 
Export ListNotations. 
Require Export hetList. 
Require Import ZArith.
Open Scope Z_scope.

(*looks nicer in unicode*)
Definition int := Z. 

Fixpoint sum (l : list int) : int := 
  match l with
      |hd::tl => hd + sum tl
      |List.nil => 0
  end. 

(*split L l1 l2: L is composed of l1 and l2*)
Inductive split : list int -> list int -> list int -> Prop :=
|splitNil : split nil nil nil
|splitConsL : forall a1 a2 x b1 b2 c,
                split (a1++a2) (b1++b2) c ->
                split (a1++x::a2) (b1++x::b2) c
|splitConsR : forall a1 a2 x b c1 c2,
                split (a1++a2) b (c1++c2) ->
                split (a1++x::a2) b (c1++x::c2). 

Inductive partition (k:int) (l:list int) : Prop :=
|partition_ : forall (l1 l2 : list int) , sum l = k * 2 -> split l l1 l2 ->
                                   sum l1 = k -> sum l2 = k -> partition k l. 

(*triple of integers*)
Definition vote : Type := prod (prod int int) int. 

Inductive voteWF : vote -> int -> Prop := 
|vetoP : forall k, voteWF (0,2*k,2*k) k
|vetaA : forall k, voteWF (2*k,0,2*k) k
|vetaB : forall k, voteWF (2*k,k,2*0) k. 

Definition add_votes v1 v2 :=
  match v1, v2 with
      |(a,b,c), (d,e,f) => (a+d,b+e,c+f)
  end. 

Fixpoint score_votes vs :=
  match vs with
      |v::vs => add_votes v (score_votes vs)
      |nil => (0,0,0)
  end. 

(*The convention here is that the first position corresponds to the 
**candidate the manipulators want to win << p, a, b >> *)
Inductive p_wins : vote -> Prop :=
|p_wins_ : forall p a b, p >= a -> p >= b -> p_wins(p, a, b). 

Inductive mkVote k : vote -> Prop :=
|veto_p : mkVote k (0, 2*k, 2*k)
|veto_a : mkVote k (2*k, 0, 2*k)
|veto_b : mkVote k (2*k, 2*k, 0).

Inductive mkVotes : list int -> list vote -> Prop :=
|mkVotesNil : mkVotes nil nil
|mkVotesNonNil : forall k1 k2 v1 v2 k v, 
                   mkVotes (k1++k2) (v1++v2) -> mkVote k v ->
                   mkVotes (k1++k::k2) (v1++v::v2). 

(*base votes correspond to the non-manipulator votes, n is the number of candidates*)
Inductive manipulate (base_votes : vote) (weights : list int) : Prop := 
|manipulate_ : forall votes, mkVotes weights votes -> 
                        p_wins (score_votes (base_votes::votes)) ->
                        manipulate base_votes weights. 

Definition reduce k (l:list int) := ((0,k*2-1,k*2-1), l). 

Ltac inv H := inversion H; subst; clear H. 

Ltac copy H :=
  match type of H with
      |?x => assert(x) by auto
  end. 

Ltac invertHyp := 
  match goal with
      |H:exists x, ?P |- _ => inv H; try invertHyp 
      |H:?A /\ ?B |- _ => inv H; try invertHyp
  end. 

Theorem sumRemoveMid : forall a b c k, sum (a++b::c) = k -> 
                                  sum (a++c) = k - b. 
Proof.
  induction a; intros. 
  {simpl in *. symmetry in H. apply Zplus_minus_eq in H. auto. }
  {simpl in *. symmetry in H. apply Zplus_minus_eq in H. eapply IHa in H. 
   rewrite H. rewrite Z.add_sub_assoc. rewrite Zplus_minus. auto. }
Qed. 

Theorem scoreVotesRemoveMid : forall vs1 vs2 a b c s1 s2 s3, 
                                score_votes (vs1++vs2) = (s1-a,s2-b,s3-c) ->
                                score_votes (vs1++(a,b,c)::vs2) = (s1,s2,s3).
Proof.
  intros vs1 vs2. induction vs1; intros.  
  {simpl in *. rewrite H. repeat rewrite Zplus_minus. auto. }
  {simpl in *. unfold add_votes in *. destruct a. destruct p.  
   destruct (score_votes (vs1++vs2)). destruct p. inv H.
   rewrite <- Zeq_plus_swap in H1. rewrite <- Zeq_plus_swap in H2. 
   rewrite <- Zeq_plus_swap in H3. erewrite IHvs1. 
   subst. repeat rewrite <- Zplus_assoc. eauto. subst.
   repeat rewrite Z.add_simpl_r. auto. }
Qed. 

Theorem mkVotesSum : forall weights l1 l2 k1 k2,
                       sum l1 = k1 -> sum l2 = k2 -> split weights l1 l2 ->
                       exists vs, mkVotes weights vs /\ score_votes vs = ((k1+k2)*2, 2*k2, 2*k1). 
Proof.
  intros. genDeps {{ k1; k2 }}. induction H1; intros. 
  {simpl in *. subst. exists nil. simpl. repeat constructor. }
  {apply sumRemoveMid in H. eapply IHsplit in H; eauto. invertHyp. 
    assert(exists x1 x2, x0 = x1++x2). exists nil. exists x0. auto. invertHyp. 
   exists (x1++(2*x,0,2*x)::x2). split. econstructor. auto. constructor. 
   apply scoreVotesRemoveMid. 
   assert((k1 + sum c) * 2 - 2*x = (k1 - x + sum c) * 2). omega. rewrite H2. 
   assert(2*k1 - 2*x = (k1 - x) * 2). omega. rewrite H3.
   rewrite <- Zminus_0_l_reverse. rewrite (Zmult_comm (k1-x) 2). auto. }
  {apply sumRemoveMid in H0. eapply IHsplit in H0; eauto. invertHyp. 
    assert(exists x1 x2, x0 = x1++x2). exists nil. exists x0. auto. invertHyp. 
   exists (x1++(2*x,2*x,0)::x2). split. econstructor. auto. constructor. 
   apply scoreVotesRemoveMid. 
   assert((sum b + k2) * 2 - 2*x = (k2 - x + sum b) * 2). omega. rewrite H2. 
   assert(2 * k2 - 2 * x = (k2 - x) * 2). omega. rewrite H3.
   rewrite <- Zminus_0_l_reverse. rewrite (Zmult_comm (k2-x) 2). 
   rewrite (Zplus_comm _ (sum b)). auto. }
Qed. 

Theorem veto_npc : forall l (k:int) nonManipVote weights,
                     reduce k l = (nonManipVote, weights) -> sum l = k*2 ->
                     (partition k l <-> manipulate nonManipVote weights). 
Proof.
  intros. split; intros. 
  {unfold reduce in H. inv H. inversion H1. eapply mkVotesSum in H2; eauto. 
   invertHyp. econstructor. eauto. simpl. rewrite H3. constructor; omega. }
  {unfold reduce in *. inv H. inv H1. 













