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
|splitConsL : forall a x b1 b2 c,
                split a (b1++b2) c ->
                split (x::a) (b1++x::b2) c
|splitConsR : forall a x b c1 c2,
                split a b (c1++c2) ->
                split (x::a) b (c1++x::c2). 

Inductive partition (k:int) (l:list int) : Prop :=
|partition_ : forall (l1 l2 : list int), 
                sum l = k * 2 -> split l l1 l2 ->
                sum l1 = k -> sum l2 = k -> partition k l. 

(*triple of integers*)
Definition vote : Type := prod (prod int int) int. 

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
|p_wins_ : forall p a b, p > a -> p > b -> p_wins(p, a, b). 

(*make a vote of weight 6k*)
Inductive mkVote k : vote -> Prop :=
|favor_a : mkVote k (k*12, k*6, 0)
|favor_b : mkVote k (k*12, 0, k*6).

(*construct a list of votes given a list of weights*)
Inductive mkVotes : list int -> list vote -> Prop :=
|mkVotesNil : mkVotes nil nil
|mkVotesNonNil : forall ks vs k v, 
                   mkVotes ks vs -> mkVote k v ->
                   mkVotes (k::ks) (v::vs). 

(*base_vote is the vote of the non manipulator.  
**weights are the weights of the manipulators*)
Inductive manipulate (base_vote : vote) (weights : list int) : Prop := 
|manipulate_ : forall votes, 
                 mkVotes weights votes -> 
                 p_wins (score_votes (base_vote::votes)) ->
                 manipulate base_vote weights. 

Definition reduce k (l:list int) := ((0,k*18-3,k*18-3), l). 

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

Ltac votesEq :=
  match goal with
      | |- (?a,?b,?c)=(?a,?b,?f) =>
        let n := fresh 
        in assert(n:c=f) by omega; rewrite n; try votesEq
      | |- (?a,?b,?c)=(?a,?e,?f) =>
        let n := fresh 
        in assert(n:b=e) by omega; rewrite n; try votesEq
      | |- (?a,?b,?c)=(?d,?e,?f) =>
        let n := fresh 
        in assert(n:a=d) by omega; rewrite n; try votesEq
      | |- _ => eauto
  end. 

Theorem mkVotesSum : forall weights l1 l2 k1 k2,
                       sum l1 = k1 -> sum l2 = k2 -> split weights l1 l2 ->
                       exists vs, mkVotes weights vs /\ 
                             score_votes vs = ((k1+k2)*12, k2*6, k1*6). 
Proof.
  intros. genDeps {{ k1; k2 }}. induction H1; intros. 
  {simpl in *. subst. exists nil. simpl. repeat constructor. }
  {apply sumRemoveMid in H. eapply IHsplit in H; eauto. invertHyp.
   exists ((x*12,0,x*6)::x0). split. constructor. auto. constructor.
   simpl. rewrite H0. votesEq. }
  {apply sumRemoveMid in H0. eapply IHsplit in H0; eauto. invertHyp.
   exists ((x*12,x*6,0)::x0). split. constructor. auto. constructor.
   simpl. rewrite H0. votesEq. }
Qed. 

Theorem score_votes_total : forall vs, 
                              exists s1 s2 s3, score_votes vs = (s1,s2,s3). 
Proof.
  induction vs.
  {exists 0. exists 0. exists 0. simpl. auto. }
  {destruct a. destruct p. invertHyp. repeat econstructor. 
   simpl. rewrite H. auto. }
Qed. 

Theorem add_votesSub : forall k1 k2 k3 vs s1 s2 s3, 
                         add_votes (k1,k2,k3) vs = (s1,s2,s3) ->
                         vs = (s1-k1,s2-k2,s3-k3). 
Proof.
  intros. simpl in *. destruct vs. destruct p. inv H. 
  repeat (rewrite <- Z.add_sub_assoc; rewrite Zplus_minus). auto. 
Qed. 

Definition multOf x k := exists y, y * k = x. 

Theorem mustBe24K : forall weights k votes s1 s2 s3, 
                 sum weights = k  ->
                 mkVotes weights votes -> 
                 score_votes votes = (s1,s2,s3) -> 
                 s1  = k * 12 /\ (s2 + s3) * 2 = s1 /\ multOf s2 6 /\ multOf s3 6. 
Proof.
  intros. genDeps {{ k; s1; s2; s3 }}. induction H0; intros. 
  {simpl in *. inv H1. split; auto. split; auto. unfold multOf.
   split; exists 0; auto. }
  {simpl in *. symmetry in H2. apply Zplus_minus_eq in H2. inv H.
   {apply add_votesSub in H1. eapply IHmkVotes in H1; eauto. invertHyp. 
    unfold multOf in *. invertHyp. split. omega. split. omega. split. 
    exists (x0+k). omega. exists x. omega. }
   {apply add_votesSub in H1. eapply IHmkVotes in H1; eauto. split. omega. split. 
    omega. unfold multOf in *. invertHyp. split. exists x0. omega. exists (x+k). omega. }
  }
Qed. 

Ltac solveByInv := 
  match goal with
      |H:_ |- _ => solve[inv H]
  end. 

Theorem weightsToVotes : forall votes weights s1 s2 s3, 
                  mkVotes weights votes ->
                  score_votes votes = (s1,s2,s3) ->
                  exists l1 l2, split weights l1 l2 /\ sum l1 * 6 = s2 /\ sum l2 * 6 = s3. 
Proof.
  intros. genDeps {{ s1; s2; s3 }}. induction H; intros. 
  {simpl in H0. inv H0. exists nil. exists nil. split. constructor. auto. }
  {simpl in H1. inv H0. 
   {apply add_votesSub in H1. eapply IHmkVotes in H1. invertHyp. 
    exists (nil++k::x). exists x0. split. constructor. simpl. auto. simpl. 
    split; omega. }
   {apply add_votesSub in H1. eapply IHmkVotes in H1. invertHyp. 
     exists x. exists (nil++k::x0). split. constructor. simpl. auto. simpl. 
    split; omega. }
  }
Qed. 

Theorem veto_npc : forall l k nonManipVote weights,
                     reduce k l = (nonManipVote, weights) -> sum l = k*2 ->
                     (partition k l <-> manipulate nonManipVote weights). 
Proof.
  intros. split; intros. 
  {unfold reduce in H. inv H. inversion H1. eapply mkVotesSum in H2; eauto. 
   invertHyp. econstructor. eauto. simpl. rewrite H3. constructor; omega. }
  {unfold reduce in *. inv H. inv H1.  
   assert(exists s1 s2 s3, score_votes votes = (s1,s2,s3)). apply score_votes_total. 
   invertHyp. simpl in H2. rewrite H3 in H2. inv H2. copy H0. 
   eapply mustBe24K in H1; eauto. invertHyp. unfold multOf in *. invertHyp.  
   assert(x1 <= k). omega. assert(x <= k). omega. rewrite <- Z.mul_assoc in H1. 
   simpl in H1. assert((x1+x) = k * 2). omega. assert(x1=k /\ x=k). omega. invertHyp.
   eapply weightsToVotes in H; eauto. invertHyp. econstructor; eauto. 
   erewrite Z.mul_cancel_r in H; auto.  omega. erewrite Z.mul_cancel_r in H10; auto. 
   omega. }
Qed. 






