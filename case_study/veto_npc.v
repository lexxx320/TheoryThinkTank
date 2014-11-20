Require Export Coq.Sorting.Permutation. 
Require Export Omega.   
Require Export List. 
Export ListNotations. 
Require Export hetList. 
Require Import ZArith.
Open Scope Z_scope.
Require Export Coq.Sets.Ensembles. 

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

Inductive voteWF : list int -> int -> Prop := 
|vetoP : forall k, voteWF [0; k; k] k
|vetaA : forall k, voteWF [k; 0; k] k
|vetaB : forall k, voteWF [k; k; 0] k. 

Definition vote := list int. 

Inductive add_votes : vote -> vote -> vote -> Prop :=
|addNil : add_votes nil nil nil
|addCons : forall h1 h2 t1 t2 t3,
             add_votes t1 t2 t3 -> add_votes (h1::t1) (h2::t2) (h1+h2::t3). 

Inductive fold_votes : list vote -> vote -> Prop :=
|foldSingle : forall v, fold_votes [v] v
|foldCons : forall hd tl res res', fold_votes tl res -> add_votes hd res res' ->
                              fold_votes (hd::tl) res'.

(*The convention here is that the first position corresponds to the 
**candidate the manipulators want to win << p, a, b >> *)
Inductive p_wins : vote -> Prop :=
|p_wins_ : forall hd tl, Forall (fun x => x <= hd) tl -> p_wins (hd::tl). 

(*base votes correspond to the non-manipulator votes, n is the number of candidates*)
Inductive manipulate (base_votes : vote) votes : Prop := 
|manipulate_ : forall res, fold_votes (base_votes::votes) res -> p_wins res ->
                            Forall (fun v => exists k, voteWF v k) votes ->
                            manipulate base_votes votes. 

Fixpoint build_veto_a ks :=
  match ks with
    |k::ks' => [k*2; 0; k*2]::(build_veto_a ks')
    |nil => [[0;0;0]]
  end. 

Fixpoint build_veto_b ks :=
  match ks with
    |k::ks' => [k*2; k*2; 0]::(build_veto_b ks')
    |nil => [[0;0;0]]
  end. 

Inductive weights : list vote -> list int -> Prop :=
|nilWeights : weights nil nil
|consWeights : forall v k vs ks, voteWF v k -> weights vs ks -> 
                            weights (v::vs) (k::ks). 

Inductive reduce k l : vote -> list vote -> Prop :=
|reduce_ : forall vs ks, weights vs ks -> Permutation ks l ->
                    reduce k l [0;k*2-1; k*2-1] vs.

Ltac inv H := inversion H; subst; clear H. 

Theorem sum_veto_a : forall l k, sum l = k -> 
                            fold_votes (build_veto_a l) [k*2; 0; k*2]. 
Proof.
  induction l; intros. 
  {simpl in *. subst. simpl. constructor. }
  {simpl in H. symmetry in H. apply Zplus_minus_eq in H. apply IHl in H.
   simpl. econstructor. eauto. assert(k*2=(a*2) + ((k-a)*2)). omega. rewrite H0. 
   repeat constructor. }
Qed. 

Theorem sum_veto_b : forall l k, sum l = k -> 
                            fold_votes (build_veto_b l) [k*2; k*2; 0].
Proof.
  induction l; intros. 
  {simpl in *. subst. simpl. constructor. }
  {simpl in H. symmetry in H. apply Zplus_minus_eq in H. apply IHl in H.
   simpl. econstructor. eauto. assert(k*2=(a*2) + ((k-a)*2)). omega. rewrite H0. 
   repeat constructor. }
Qed. 

Inductive sub_votes : vote -> vote -> vote -> Prop :=
|subNil : sub_votes [] [] []
|subCons : forall (h1 h2 : int) (t1 t2 t3 : vote),
             sub_votes t1 t2 t3 ->
             sub_votes (h1 :: t1) (h2 :: t2) (h1 - h2 :: t3).

Ltac invertHyp := 
  match goal with
      |H:exists x, ?P |- _ => inv H; try invertHyp
      |H:?A /\ ?B |- _ => inv H; try invertHyp
  end. 

Ltac copy H :=
  match type of H with
      |?x => assert(x) by auto
  end. 

Theorem addSub : forall a b c d e, 
                   add_votes a b c -> add_votes c d e ->
                   exists res, sub_votes e a res. 
Proof.
  intros. genDeps {{ d; e }}. induction H; intros. 
  {inv H0. repeat econstructor. }
  {inv H0. apply IHadd_votes in H5. invertHyp. econstructor. 
   econstructor. eauto. }
Qed. 


Theorem addSub' : forall a res res1 res2 res3 x, 
                 add_votes a res res1 -> add_votes res1 res2 res3 ->
                 sub_votes res3 a x -> add_votes res res2 x. 
Proof.
  intros. genDeps {{ res2;res3;x }}. induction H; intros.
  {inv H0. inv H1. constructor. }
  {inv H0. inv H1. assert(h1+h2+h3-h1 = h2+h3). omega. rewrite H0. 
   constructor. eauto. }
Qed. 

Theorem addSubEq : forall a b c, sub_votes a b c -> add_votes c b a.
Proof.
  intros. induction H. 
  {constructor. }
  {assert((h1-h2)+h2 = h1). omega. rewrite <- H0 at 2. constructor. auto. }
Qed. 

Theorem add_votes_comm : forall a b c, add_votes a b c -> add_votes b a c. 
Proof.
  intros. induction H. 
  {constructor. }
  {replace (h1+h2) with (h2+h1). constructor. auto. omega. }
Qed. 

Theorem fold_votes_app : forall a b res1 res2 res3, 
                           fold_votes a res1 -> 
                           fold_votes b res2 ->
                           add_votes res1 res2 res3 -> 
                           fold_votes (a++b) res3.
Proof.
  induction a; intros. 
  {inv H. }
  {inv H. 
   {econstructor. eauto. auto. }
   {simpl. copy H1. eapply addSub with (a:= a) in H1; eauto. invertHyp. 
    econstructor. eapply IHa; eauto. eapply addSub'; eauto. 
    apply add_votes_comm. eapply addSubEq. auto. }
  }
Qed. 

Theorem ForallApp : forall (A:Type) P (l1 l2 : list A), 
                      Forall P l1 -> Forall P l2 -> Forall P (l1++l2).
Proof.
  induction l1; intros. 
  {simpl. auto. }
  {inv H. simpl. constructor; auto. }
Qed. 

Theorem build_veto_aWF : forall l, Forall (fun v => exists k, voteWF v k) (build_veto_a l). 
Proof.
  induction l; intros. 
  {simpl. repeat econstructor. }
  {simpl. repeat econstructor. auto. }
Qed. 

Theorem build_veto_bWF : forall l, Forall (fun v => exists k, voteWF v k) (build_veto_b l). 
Proof.
  induction l; intros. 
  {simpl. repeat econstructor. }
  {simpl. repeat econstructor. auto. }
Qed. 

Theorem veto_npc : forall l (k:int) vs mVs, reduce k l vs mVs ->
                                     (partition k l <-> manipulate vs mVs). 
Proof.
  intros. split; intros. 
  {inversion H0. apply sum_veto_a in H3. apply sum_veto_b in H4.
   inv H. eapply manipulate_. 
   eapply manipulate_ with (votes := build_veto_a l1 ++ build_veto_b l2).
   econstructor. eapply fold_votes_app; eauto. repeat econstructor. 
   unfold reduce in H. subst. repeat constructor. constructor. 
   repeat constructor; omega. apply ForallApp. apply build_veto_aWF. 
   apply build_veto_bWF. }
  {inv H0. 















