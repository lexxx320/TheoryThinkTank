Require Export Coq.Sorting.Permutation. 
Require Export Omega.   
Require Export List. 
Export ListNotations. 
Require Export hetList. 
Require Import ZArith.
Open Scope Z_scope.
Require Export Coq.Sets.Ensembles. 
Require Export Coq.Vectors.VectorDef. 

(*looks nicer in unicode*)
Definition int := Z. 

Fixpoint sum (l : list int) : int := 
  match l with
      |hd::tl => hd + sum tl
      |List.nil => 0
  end. 

Inductive partition (k:int) (l:list int) : Prop :=
|partition_ : forall (l1 l2 : list int) , sum l = k * 2 -> Permutation (l1++l2) l ->
                                   sum l1 = k -> sum l2 = k -> partition k l. 

(*list of exactly three elements*)
Definition vote := t int 3. 

(*shorthand notation for votes*)
Local Notation " '<<' c1 , c2 , c3 '>>' " := 
  (cons _ c1 _ (cons _ c2 _ (cons _ c3 _ (nil _)))).

Definition zero_vote := << 0, 0, 0 >>.
Definition add_votes {n:nat} v1 v2 := @map2 int int int (fun x y => x + y) n v1 v2. 

Fixpoint foldVotes vs (base:vote) :=
  match vs with
      |v::vs => add_votes v (foldVotes vs base)
      |List.nil => base
  end. 

(*The convention here is that the first position corresponds to the 
**candidate the manipulators want to win << p, a, b >> *)
Inductive p_wins : vote -> Prop :=
|p_wins_ : forall hd tl, Forall (fun x => x <= hd) tl -> p_wins (cons _ hd _ tl). 

(*base votes correspond to the non-manipulator votes*)
Inductive manipulate (base_votes : vote) : Prop := 
|manipulate_ : forall votes, p_wins (foldVotes votes base_votes ) ->
                        manipulate base_votes. 

Fixpoint build_veto_a ks :=
  match ks with
    |k::ks' => List.cons << k*2, 0, k*2 >>(build_veto_a ks')
    |List.nil => List.nil
  end. 

Fixpoint build_veto_b ks :=
  match ks with
    |k::ks' => List.cons << k*2, k*2, 0 >> (build_veto_b ks')
    |List.nil => List.nil
  end. 

(*2k-1 votes veto p*)
Definition reduce k := << 0, k*2-1, k*2-1 >>. 

Ltac inv H := inversion H; subst; clear H. 

Theorem sum_veto_a : forall l k, sum l = k -> 
                            foldVotes (build_veto_a l) zero_vote = << k*2, 0, k*2 >>. 
Proof.
  induction l; intros. 
  {simpl in *. subst. simpl. reflexivity. }
  {simpl in H. symmetry in H. apply Zplus_minus_eq in H. apply IHl in H.
   simpl. rewrite H. simpl. assert(a*2+(k-a)*2 = k*2). omega. rewrite H0.
   reflexivity. }
Qed. 

Theorem sum_veto_b : forall l k, sum l = k -> 
                            foldVotes(build_veto_b l) zero_vote = << k*2, k*2, 0 >>. 
Proof.
  induction l; intros. 
  {inv H. simpl. reflexivity. } 
  {simpl in H. symmetry in H. apply Zplus_minus_eq in H. apply IHl in H.
   simpl. rewrite H. simpl. assert(a*2+(k-a)*2 = k*2). omega. rewrite H0. reflexivity. }
Qed. 

(*
Theorem add_veto_a_b : forall l1 l2 l k, Permutation (l1++l2) l -> sum l = k * 2 ->
                                    sum l1 = k -> sum l2 = k -> 
                                    add_votes (build_veto_a l1) (build_veto_b l2) =<< k*4, k*2, k*2 >>. 
Proof.
  intros. apply sum_veto_a in H1. rewrite H1. apply sum_veto_b in H2. rewrite H2. 
  simpl. assert(k*2+k*2 = k*4). omega. rewrite H3. rewrite <- Zplus_0_r_reverse. 
  reflexivity. 
Qed. 
*)

Definition shiftout {A} {n:nat} (v:t A (S n)) : t A n :=
  Eval cbv delta beta in (rectS (fun n _ => t A n) (fun a => @nil A )
                         (fun h _ _ H => cons _ h _ H) v).

Definition add_votesZero {n:nat} (x:t int (S n)) : t int n :=
  Eval cbv delta beta in (rectS (fun n _ => t int n) (fun a => @nil int)
                         (fun h _ _ H => cons _ h _ H) x). 

Theorem _add_votesZero : forall x, add_votes zero_vote x = x. 
Proof.
  intros. simpl. apply add_votesZero in x. 



Theorem foldVotesApp : forall v1 v2 base, 
                         foldVotes(v1++v2) base = add_votes (foldVotes v1 zero_vote) (foldVotes v2 base). 
Proof.
  induction v1; intros. 
  {replace (foldVotes [] zero_vote) with zero_vote; auto. 


Theorem veto_npc : forall l (k:int) vs, reduce k = vs ->
                                 (partition k l <-> manipulate vs). 
Proof.
  intros. split; intros. 
  {inversion H0. apply manipulate_ with (votes := build_veto_a l1 ++ build_veto_b l2).
                         


