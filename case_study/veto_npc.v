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
Definition fold_votes (vs:list vote) base := List.fold_left add_votes vs base. 
Definition fold_votes0 (vs:list vote) := List.fold_left add_votes vs zero_vote. 

(*The convention here is that the first position corresponds to the 
**candidate the manipulators want to win << p, a, b >> *)
Inductive p_wins : vote -> Prop :=
|p_wins_ : forall hd tl, Forall (fun x => x <= hd) tl -> p_wins (cons _ hd _ tl). 

(*base votes correspond to the non-manipulator votes*)
Inductive manipulate (base_votes : vote) : Prop := 
|manipulate_ : forall votes, p_wins (fold_votes votes base_votes ) ->
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

Definition reduce k := << 0, k*2-1, k*2-2 >>. 

Ltac inv H := inversion H; subst; clear H. 

Theorem fold_cons : forall (A:Type) (a:A) b f (z:A), 
                      List.fold_left f (a::b) z =
                      List.fold_left f b (f z a). 
Proof.
  intros. simpl. auto. 
Qed. 

Theorem fold0CommCons : forall vs v,
                          fold_votes0 (v::vs) = add_votes (fold_votes0 vs) v. 
Proof.
  induction vs; intros. 
  {unfold fold_votes0. rewrite fold_cons. unfold List.fold_left. auto. }
  {unfold fold_votes0 in *. rewrite fold_cons. 




Theorem sum_veto_a : forall l k, sum l = k -> 
                            fold_votes0 (build_veto_a l) = << k*2, 0, k*2 >>. 
Proof.
  induction l; intros. 
  {simpl in *. subst. simpl. reflexivity. }
  {simpl in H. symmetry in H. apply Zplus_minus_eq in H. apply IHl in H.
   simpl. 

rewrite H. simpl. assert(a*2+(k-a)*2 = k*2). omega. rewrite H0. reflexivity. }
Qed. 

Theorem sum_veto_b : forall l k, sum l = k -> build_veto_b l = << k*2, k*2, 0 >>. 
Proof.
  induction l; intros. 
  {inv H. simpl. reflexivity. }
  {simpl in H. symmetry in H. apply Zplus_minus_eq in H. apply IHl in H.
   simpl. rewrite H. simpl. assert(a*2+(k-a)*2 = k*2). omega. rewrite H0. reflexivity. }
Qed. 

Theorem add_veto_a_b : forall l1 l2 l k, Permutation (l1++l2) l -> sum l = k * 2 ->
                                    sum l1 = k -> sum l2 = k -> 
                                    add_votes (build_veto_a l1) (build_veto_b l2) =<< k*4, k*2, k*2 >>. 
Proof.
  intros. apply sum_veto_a in H1. rewrite H1. apply sum_veto_b in H2. rewrite H2. 
  simpl. assert(k*2+k*2 = k*4). omega. rewrite H3. rewrite <- Zplus_0_r_reverse. 
  reflexivity. 
Qed. 

Theorem veto_npc : forall l k vs, reduce k = vs ->
                             (partition k l <-> manipulate vs). 
Proof.
  intros. split; intros. 
  {inversion H0. apply manipulate_ with (votes := (add_votes (build_veto_a l1) 
                                                            (build_veto_b l2))). 
   eapply add_veto_a_b in H2; eauto. rewrite H2. subst. constructor. repeat constructor; omega. }
  {inv H0. 



