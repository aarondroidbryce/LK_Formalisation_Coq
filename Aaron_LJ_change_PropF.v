Require Export List.
Add LoadPath "../lnt/tense-logic-in-Coq".
Require Import Strong_induction.
Set Implicit Arguments.
Export ListNotations.

Delimit Scope My_scope with M.
Open Scope My_scope.

Parameter PropVars : Set.
Hypothesis Varseq_dec : forall x y:PropVars, {x = y} + {x <> y}.


(** * Definitions

definition of Propositional Formulas*)
Inductive PropF : Set :=
 | Var : PropVars -> PropF
 | Bot : PropF
 | Imp : PropF -> PropF -> PropF
 | Con : PropF -> PropF -> PropF
 | Dis : PropF -> PropF -> PropF
.

Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A → B" := (Imp A B) (at level 16, right associativity) : My_scope.
Notation "⊥" := Bot (at level 0)  : My_scope.
Notation "A ∧ B" := (Con A B) (at level 15, right associativity) : My_scope.
Notation "A ∨ B" := (Dis A B) (at level 15, right associativity) : My_scope.

(** Defined connectives *)
Notation "¬ A" := (A → ⊥) (at level 1)  : My_scope.


(** Valuations are maps PropVars -> bool sending ⊥ to false*)
Fixpoint TrueQ v A : bool := match A with
 | # P   => v P
 | ⊥     => false
 | B → C => (negb (TrueQ v B)) || (TrueQ v C)
 | B ∧ C => (andb (TrueQ v B) (TrueQ v C))
 | B ∨ C => (orb (TrueQ v B) (TrueQ v C))
end.

(** Prove that the defined connectives are correct *)

Lemma def_neg_correct (A: PropF) :
  forall v, TrueQ v (¬ A) = negb (TrueQ v A).
Proof. intros. destruct A.
       simpl. rewrite Bool.orb_false_r. trivial.
       simpl. trivial.
       simpl. rewrite Bool.orb_false_r. trivial.
       simpl. rewrite Bool.orb_false_r. trivial.
       simpl. rewrite Bool.orb_false_r. trivial.
Qed.

Fixpoint  weight p :=
    match p with
      | # q' => 0
      | Bot => 0
      | p' → q' => S (max (weight p') (weight q'))
      | p' ∧ q' => S (max (weight p') (weight q'))
      | p' ∨ q' => S (max (weight p') (weight q'))      
      end.

(** * Gentzen's Sequent Calculus *)

Reserved Notation "Γ |- Δ >> n" (at level 80).
Inductive LJ : nat -> list PropF -> PropF -> Prop :=
| LJId  : forall A Γ, In (Var A) Γ -> LJ 0 Γ (Var A)
| LJBot : forall A Γ, In ⊥ Γ -> LJ 0 Γ A
| LJImpL : forall n m A B Γ1 Γ2 Δ,
                 LJ n (Γ1++B::Γ2) Δ
              -> LJ m (Γ1 ++ [Imp A B] ++ Γ2) A
              -> LJ (S (max n m)) (Γ1++A→B::Γ2) Δ
| LJImpR : forall n A B Γ,
              LJ n (A::Γ) B
           -> LJ (S n) Γ (A→B)
| LJConL1 : forall n A B Γ1 Γ2 Δ,
              LJ n (Γ1 ++ A :: Γ2) Δ
           -> LJ (S n) (Γ1 ++ (A ∧ B) :: Γ2) Δ
| LJConL2 : forall n A B Γ1 Γ2 Δ,
              LJ n (Γ1 ++ B :: Γ2) Δ
           -> LJ (S n) (Γ1 ++ (A ∧ B) :: Γ2) Δ
| LJConR : forall n m A B Γ,
                LJ n Γ A
             -> LJ m Γ B
             -> LJ (S (max n m)) Γ (A ∧ B)
| LJDisL : forall n m A B Γ1 Γ2 Δ,
                LJ n (Γ1++A::Γ2) Δ
             -> LJ m (Γ1++B::Γ2) Δ
             -> LJ (S (max n m)) (Γ1++(A ∨ B)::Γ2) Δ
| LJDisR1 : forall n A B Γ,
              LJ n Γ A
           -> LJ (S n) Γ (A ∨ B)
| LJDisR2 : forall n A B Γ,
              LJ n Γ B
           -> LJ (S n) Γ (A ∨ B)
where "Γ |- Δ >> n" := (LJ (n) (Γ) (Δ)) : My_scope.

Lemma in_elt : forall (A : Type) (a : A) L1 L2, In a (L1 ++ a :: L2).
Proof.
intros.
apply in_app_iff.
right.
simpl.
left.
reflexivity.
Qed.

Lemma cons_eq_app: forall (A : Type) (x y z : list A) (a : A),
  a :: x = y ++ z -> y = [] /\ z = a :: x \/
                         exists (y' : list A), y = a :: y' /\ x = y' ++ z.
Proof.
intros.
destruct y.
 simpl in H. subst. tauto.
 simpl in H. injection H. intros. right. subst. exists y. tauto.
Qed.

Lemma app_eq_app: forall (A : Type) (w x y z : list A),
  w ++ x = y ++ z -> exists (m : list A),
    w = y ++ m /\ z = m ++ x \/ y = w ++ m /\ x = m ++ z.
Proof.
 intro. intro.
 induction w.
    simpl. intros. exists y. rewrite H. tauto.

    intros. simpl in H.
    apply cons_eq_app in H.
    destruct H.  destruct H. rewrite H. simpl.
    exists (a :: w). rewrite H0. simpl. tauto.
    destruct H. destruct H.
    apply IHw in H0. destruct H0. destruct H0. destruct H0.
    rewrite H.  rewrite H0.  rewrite H1.  simpl.
    exists x1. tauto.
    destruct H0. rewrite H.  rewrite H0.  rewrite H1.  simpl.
    exists x1. tauto.
Qed.

Lemma cons_single_app: forall T (A : T) L, A :: L = [A] ++ L.
Proof.
reflexivity.
Qed.

Lemma in_app_comm : forall (A : Type) (a : A) (X Y : list A), In a (X ++ Y) <-> In a (Y ++ X).
Proof.
intros.
induction X.

rewrite app_nil_r.
rewrite app_nil_l.
reflexivity.

rewrite! in_app_iff.
firstorder.
Qed.

Lemma in_cons_comm : forall (A : Type) (a b c: A) (X Y : list A), In a (X ++ b :: c :: Y) <-> In a (X ++ c :: b :: Y).
Proof.
intros.
rewrite! in_app_iff.
simpl.
firstorder.
Qed.

Lemma in_list_eq : forall {A : Type} {l1 l2 l3 : list A} {a : A}, (l1 ++ a :: l2) = l3 -> In a l3.
Proof.
intros.
rewrite <- H.
apply in_app_iff.
right.
apply in_eq.
Qed.

Lemma le_trans: forall a b c, a <= b -> b <= c -> a <= c.
Proof.
intros.
rewrite H.
assumption.
Qed.

Lemma in_app_add: forall (A : Type) (a : A) (L1 L2 : list A), In a L1 -> In a (L1 ++ L2).
Proof.
intros.
induction L2.

rewrite app_nil_r.
assumption.

rewrite cons_single_app.
apply in_app_comm.
simpl.
right.
apply in_app_comm.
assumption.
Qed.

Lemma imp_not_var: forall A B C L1 L2, In (# A) (L1 ++ Imp B C :: L2) -> In (# A) (L1 ++ L2).
Proof.
intros.
apply in_app_comm in H.
simpl in H.
destruct H.

discriminate.
apply in_app_comm.
assumption.
Qed.

Lemma imp_not_bot: forall B C L1 L2, In Bot (L1 ++ Imp B C :: L2) -> In Bot (L1 ++ L2).
Proof.
intros.
apply in_app_comm in H.
simpl in H.
destruct H.

discriminate.
apply in_app_comm.
assumption.
Qed.

Lemma con_not_var: forall A B C L1 L2, In (# A) (L1 ++ Con B C :: L2) -> In (# A) (L1 ++ L2).
Proof.
intros.
apply in_app_comm in H.
simpl in H.
destruct H.

discriminate.
apply in_app_comm.
assumption.
Qed.

Lemma con_not_bot: forall B C L1 L2, In Bot (L1 ++ Con B C :: L2) -> In Bot (L1 ++ L2).
Proof.
intros.
apply in_app_comm in H.
simpl in H.
destruct H.

discriminate.
apply in_app_comm.
assumption.
Qed.

Lemma dis_not_var: forall A B C L1 L2, In (# A) (L1 ++ Dis B C :: L2) -> In (# A) (L1 ++ L2).
Proof.
intros.
apply in_app_comm in H.
simpl in H.
destruct H.

discriminate.
apply in_app_comm.
assumption.
Qed.

Lemma dis_not_bot: forall B C L1 L2, In Bot (L1 ++ Dis B C :: L2) -> In Bot (L1 ++ L2).
Proof.
intros.
apply in_app_comm in H.
simpl in H.
destruct H.

discriminate.
apply in_app_comm.
assumption.
Qed.

Lemma in_double: forall (A : Type) (a : A) B L1 L2 L3, In a (L1 ++ B :: L2 ++ B :: L3) -> In a (L1 ++ B :: L2 ++ L3) .
Proof.
intros.
rewrite in_app_iff in H.
simpl in H.
rewrite or_comm in H.
rewrite or_assoc in H.
destruct H.

subst.
firstorder.

rewrite in_app_comm in H.
rewrite <- app_comm_cons in H.
simpl in H.
rewrite in_app_comm in H.
rewrite or_comm in H.
rewrite in_app_iff.
assumption.
Qed.

Lemma Id_extension : forall A Γ, In A Γ -> exists n, weight A <= n /\ Γ |- A >> n.
Proof.
intros A.
induction A.

(*PropVar*)
intros.
exists 0.
split.
apply le_n.
apply (LJId _ _ H).

(*Bot*)
intros.
exists 0.
split.
apply le_n.
apply (LJBot _ _ H).

(*Imp*)
intros.
simpl.
destruct (in_split _ _ H) as [l1 [l2 Z1]].
subst.
destruct (IHA1 (A1 :: l1 ++ [Imp A1 A2] ++ l2) (in_eq (A1) _) ) as [a [I1 I2]].
destruct (IHA2 ((A1 :: l1) ++ A2 :: l2) (in_elt A2 _ _)) as [b [I3 I4]].
pose (LJImpL _ _ _ I4 I2) as I5.
exists (S (S (max b a))).
split.

rewrite PeanoNat.Nat.max_comm.
apply (le_n_S _ _ (le_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ I3 I1))).

apply (LJImpR I5).

(*Con*)
intros.
simpl.
destruct (in_split _ _ H) as [l1 [l2 Z1]].
subst.
destruct (IHA1 (l1 ++ A1 :: l2) (in_elt A1 _ _) ) as [a [L1 L2]].
destruct (IHA2 (l1 ++ A2 :: l2) (in_elt A2 _ _) ) as [b [R1 R2]].
pose (LJConL1 _ A2 _ _ L2) as L3.
pose (LJConL2 A1 _ _ _ R2) as R3.
exists (S (max (S a) (S b))).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ (le_S _ _ L1) (le_S _ _ R1))).

apply (LJConR L3 R3).

(*Dis*)
intros.
simpl.
destruct (in_split _ _ H) as [l1 [l2 Z1]].
subst.
destruct (IHA1 (l1 ++ A1 :: l2) (in_elt A1 _ _) ) as [a [L1 L2]].
destruct (IHA2 (l1 ++ A2 :: l2) (in_elt A2 _ _) ) as [b [R1 R2]].
pose (LJDisR1 A2 L2) as L3.
pose (LJDisR2 A1 R2) as R3.
exists (S (max (S a) (S b))).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ (le_S _ _ L1) (le_S _ _ R1))).

apply (LJDisL _ _ _ _ L3 R3).
Qed.

Lemma exchange_L:
  forall n E F Γ1 Γ2 Δ (D: LJ n (Γ1 ++ E :: F :: Γ2) Δ), LJ n (Γ1 ++ F :: E :: Γ2) Δ.
Proof.
intro n.
induction n using strong_induction.

(*Base Case*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Id*)
apply in_cons_comm in Ant.
apply (LJId _ _ Ant).

(*Bot*)
apply in_cons_comm in Fal.
apply (LJBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite (cons_single_app F) in *.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L1 R1).

inversion Z2 as [[Z3 Z4]].
destruct l.

inversion Z4.
subst.
rewrite app_assoc_reverse in L.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
rewrite app_assoc_reverse in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
apply (LJImpL _ _ _ L1 R1).
 
inversion Z4.
subst.
rewrite app_assoc_reverse in L.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
rewrite app_assoc_reverse in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite! app_comm_cons in *.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L1 R1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite (cons_single_app F) in *.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L1 R1).

inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
rewrite! app_assoc in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite! app_assoc_reverse in *.
apply (LJImpL _ _ _ L1 R1).

(*ImpR*)
subst.
rewrite app_comm_cons in I.
pose (H _ (le_n _) _ _ _ _ _ I) as I1.
apply (LJImpR I1).

(*ConL1*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (le_n _) _ _ _ _ _ L) as L1.
rewrite (cons_single_app F) in *.
rewrite app_assoc in *.
apply (LJConL1 A B _ _ L1).

inversion Z2 as [[Z3 Z4]].
destruct l.

inversion Z4.
subst.
rewrite app_assoc_reverse in L.
pose (H _ (le_n _) _ _ _ _ _ L) as L1.
apply (LJConL1 A B _ _ L1).
 
inversion Z4.
subst.
rewrite app_assoc_reverse in L.
pose (H _ (le_n _) _ _ _ _ _ L) as L1.
rewrite! app_comm_cons in *.
rewrite app_assoc in *.
apply (LJConL1 A B _ _ L1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (le_n _) _ _ _ _ _ L) as L1.
rewrite (cons_single_app F) in *.
rewrite app_assoc in *.
apply (LJConL1 A B _ _ L1).

inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
pose (H _ (le_n _) _ _ _ _ _ L) as L1.
rewrite! app_assoc_reverse in *.
apply (LJConL1 A B _ _ L1).

(*ConL2*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (le_n _) _ _ _ _ _ R) as R1.
rewrite (cons_single_app F) in *.
rewrite app_assoc in *.
apply (LJConL2 A B _ _ R1).

inversion Z2 as [[Z3 Z4]].
destruct l.

inversion Z4.
subst.
rewrite app_assoc_reverse in R.
pose (H _ (le_n _) _ _ _ _ _ R) as R1.
apply (LJConL2 A B _ _ R1).
 
inversion Z4.
subst.
rewrite app_assoc_reverse in R.
pose (H _ (le_n _) _ _ _ _ _ R) as R1.
rewrite! app_comm_cons in *.
rewrite app_assoc in *.
apply (LJConL2 A B _ _ R1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (le_n _) _ _ _ _ _ R) as R1.
rewrite (cons_single_app F) in *.
rewrite app_assoc in *.
apply (LJConL2 A B _ _ R1).

inversion Z2.
subst.
rewrite app_comm_cons in R.
rewrite app_assoc in R.
pose (H _ (le_n _) _ _ _ _ _ R) as R1.
rewrite! app_assoc_reverse in *.
apply (LJConL2 A B _ _ R1).

(*ConR*)
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
apply (LJConR L1 R1).

(*DisL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite (cons_single_app F) in *.
rewrite app_assoc in *.
apply (LJDisL _ _ _ _ L1 R1).

inversion Z2 as [[Z3 Z4]].
destruct l.

inversion Z4.
subst.
rewrite app_assoc_reverse in L.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
rewrite app_assoc_reverse in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
apply (LJDisL _ _ _ _ L1 R1).
 
inversion Z4.
subst.
rewrite app_assoc_reverse in L.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
rewrite app_assoc_reverse in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite! app_comm_cons in *.
rewrite app_assoc in *.
apply (LJDisL _ _ _ _ L1 R1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite (cons_single_app F) in *.
rewrite app_assoc in *.
apply (LJDisL _ _ _ _ L1 R1).

inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
rewrite app_comm_cons in R.
rewrite app_assoc in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite! app_assoc_reverse in *.
apply (LJDisL _ _ _ _ L1 R1).

(*DisR1*)
subst.
pose (H _ (le_n _) _ _ _ _ _ L) as L1.
apply (LJDisR1 B L1).

(*DisR2*)
subst.
pose (H _ (le_n _) _ _ _ _ _ R) as R1.
apply (LJDisR2 A R1).
Qed.

Lemma move_R_L:
  forall n Δ A Γ3 Γ2 Γ1,
    LJ n (Γ1 ++ A :: Γ2 ++ Γ3) Δ ->
    LJ n (Γ1 ++ Γ2 ++ A :: Γ3) Δ.
Proof.
intros n Δ A Γ3 Γ2.
induction Γ2.

intros.
assumption.


intros.
rewrite cons_single_app.
rewrite app_assoc_reverse.
rewrite app_assoc.
apply IHΓ2.
rewrite app_assoc_reverse.
apply exchange_L.
assumption.
Qed.

Lemma swap_L:
  forall n Δ Γ2 Γ3 Γ1 Γ4,
    LJ n (Γ1 ++ Γ2 ++ Γ3 ++ Γ4) Δ->
    LJ n (Γ1 ++ Γ3 ++ Γ2 ++ Γ4) Δ.
Proof.
intros n Δ Γ2 Γ3.
induction Γ2.

intros.
assumption.
intros.

apply move_R_L.
rewrite cons_single_app in H.
rewrite app_assoc_reverse in H.
rewrite app_assoc in H.

rewrite cons_single_app.
rewrite app_assoc.
apply (IHΓ2 (Γ1 ++ [a]) Γ4 H).
Qed.

Lemma weakening_L:
    forall n Γ1 Γ2 Δ (D: LJ n (Γ1 ++ Γ2) Δ),
      forall W, LJ n (Γ1 ++ W ++ Γ2) Δ.
Proof.
intro n.
induction n using strong_induction.

(*Base Case*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Id*)
rewrite in_app_comm in Ant.
apply (in_app_add _ _ W) in Ant.
rewrite app_assoc_reverse in Ant.
rewrite in_app_comm in Ant.
rewrite app_assoc_reverse in Ant.
apply (LJId _ _ Ant).

(*Bot*)
rewrite in_app_comm in Fal.
apply (in_app_add _ _ W) in Fal.
rewrite app_assoc_reverse in Fal.
rewrite in_app_comm in Fal.
rewrite app_assoc_reverse in Fal.
apply (LJBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

subst.
rewrite app_assoc_reverse in L.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L W) as L1.
rewrite app_assoc_reverse in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R W) as R1.
rewrite app_assoc in *.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L1 R1).

subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L W) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R W) as R1.
rewrite app_assoc_reverse.
apply swap_L.
rewrite <- Z2.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L1 R1).

(*ImpR*)
subst.
rewrite app_comm_cons in I.
pose (H _ (le_n _) _ _ _ I W) as I1.
apply (LJImpR I1).


(*ConL1*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (le_n _) _ _ _ L W) as L1.
rewrite app_assoc in *.
apply (LJConL1 A B _ _ L1).

subst.
rewrite app_assoc_reverse in L.
pose (H _ (le_n _) _ _ _ L W) as L1.
rewrite! app_assoc in *.
apply (LJConL1 A B _ _ L1).

destruct l.

rewrite app_nil_r in Z1.
rewrite app_nil_l in Z2.
subst.
pose (H _ (le_n _) _ _ _ L W) as L1.
rewrite app_assoc in *.
apply (LJConL1 A B _ _ L1).

inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
pose (H _ (le_n _) _ _ _ L W) as L1.
rewrite! app_assoc_reverse in *.
apply (LJConL1 A B _ _ L1).

(*ConL2*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (le_n _) _ _ _ R W) as R1.
rewrite app_assoc in *.
apply (LJConL2 A B _ _ R1).

subst.
rewrite app_assoc_reverse in R.
pose (H _ (le_n _) _ _ _ R W) as R1.
rewrite !app_assoc in *.
apply (LJConL2 A B _ _ R1).

destruct l.

rewrite app_nil_r in Z1.
rewrite app_nil_l in Z2.
subst.
pose (H _ (le_n _) _ _ _ R W) as R1.
rewrite app_assoc in *.
apply (LJConL2 A B _ _ R1).

inversion Z2.
subst.
rewrite app_comm_cons in R.
rewrite app_assoc in R.
pose (H _ (le_n _) _ _ _ R W) as R1.
rewrite! app_assoc_reverse in *.
apply (LJConL2 A B _ _ R1).

(*ConR*)
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L W) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R W) as R1.
apply (LJConR L1 R1).

(*DisL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L W) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R W) as R1.
rewrite app_assoc in *.
apply (LJDisL _ _ _ _ L1 R1).

subst.
rewrite app_assoc_reverse in L.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L W) as L1.
rewrite app_assoc_reverse in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R W) as R1.
rewrite! app_assoc in *.
apply (LJDisL _ _ _ _ L1 R1).

destruct l.

rewrite app_nil_r in Z1.
rewrite app_nil_l in Z2.
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L W) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R W) as R1.
rewrite app_assoc in *.
apply (LJDisL _ _ _ _ L1 R1).

inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L W) as L1.
rewrite app_comm_cons in R.
rewrite app_assoc in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R W) as R1.
rewrite! app_assoc_reverse in *.
apply (LJDisL _ _ _ _ L1 R1).

(*DisR1*)
subst.
pose (H _ (le_n _) _ _ _ L W) as L1.
apply (LJDisR1 B L1).

(*DisR2*)
subst.
pose (H _ (le_n _) _ _ _ R W) as R1.
apply (LJDisR2 A R1).
Qed.

Lemma inv_ImpL:
  forall n E F Γ1 Γ2 Δ (D: LJ n (Γ1 ++ (E→F) :: Γ2) Δ),
    (exists m, m <= n /\ LJ m (Γ1 ++ F :: Γ2) Δ).
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
exists 0.
split.

apply le_n.

inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Id*)
apply imp_not_var in Ant.
apply in_app_comm in Ant.
apply (in_app_add _ _ [F] ) in Ant.
rewrite app_assoc_reverse in Ant.
apply in_app_comm in Ant.
rewrite app_assoc_reverse in Ant.
apply (LJId _ _ Ant).

(*Bot*)
apply imp_not_bot in Fal.
apply in_app_comm in Fal.
apply (in_app_add _ _ [F] ) in Fal.
rewrite app_assoc_reverse in Fal.
apply in_app_comm in Fal.
rewrite app_assoc_reverse in Fal.
apply (LJBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
exists a.
split.

apply (le_S _ _ (PeanoNat.Nat.le_max_l _ _)).

assumption.

inversion Z2.
subst.
rewrite app_assoc_reverse in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc_reverse in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (Nat.max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L2 R2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
exists a.
split.

apply (le_S _ _ (PeanoNat.Nat.le_max_l _ _)).

assumption.

inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite! app_assoc in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (Nat.max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite! app_assoc_reverse in *.
apply (LJImpL _ _ _ L2 R2).

(*ImpR*)
subst.
rewrite app_comm_cons in I.
destruct (H _ (le_n _) _ _ _ _ _ I) as [b [I1 I2]].
exists (S b).
split.

apply (le_n_S _ _ I1).

apply (LJImpR I2).

(*ConL1*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in L.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
rewrite app_comm_cons in *.
rewrite app_assoc in *.
exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJConL1 A B _ _ L2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
rewrite app_assoc_reverse in *.
exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJConL1 A B _ _ L2).

(*ConL2*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in R.
destruct (H _ (le_n _) _ _ _ _ _ R) as [a [R1 R2]].
rewrite app_comm_cons in *.
rewrite app_assoc in *.
exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJConL2 A B _ _ R2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in R.
rewrite app_assoc in R.
destruct (H _ (le_n _) _ _ _ _ _ R) as [a [R1 R2]].
rewrite app_assoc_reverse in *.
exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJConL2 A B _ _ R2).

(*ConR*)
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

apply (LJConR L2 R2).

(*DisL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc_reverse in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
rewrite app_comm_cons in *.
rewrite app_assoc in *.
exists (S (max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

apply (LJDisL _ _ _ _ L2 R2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite app_comm_cons in R.
rewrite app_assoc in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
rewrite app_assoc_reverse in *.
exists (S (max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

apply (LJDisL _ _ _ _ L2 R2).

(*DisR1*)
subst.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJDisR1 B L2).

(*DisR2*)
subst.
destruct (H _ (le_n _) _ _ _ _ _ R) as [a [R1 R2]].
exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJDisR2 A R2).
Qed.

Lemma inv_ImpR:
  forall n E F Γ (D : LJ n Γ (E→F)),
   (exists m, m <= n /\ LJ m (E::Γ) F).
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
subst.
exists 0.
split.

apply le_n.

inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Bot*)
apply (in_app_add _ _ [E]) in Fal.
apply in_app_comm in Fal.
apply (LJBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L) as [c [L1 L2]].
pose (weakening_L [] _ R [E]) as R1.
exists (S (Nat.max c b)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 (le_n _))).

rewrite app_comm_cons in L2.
apply (LJImpL _ _ _ L2 R1).

(*ImpR*)
subst.
exists n.
split.

apply (le_S _ _ (le_n _)).

assumption.

(*ConL1*)
subst.
destruct (H _ (le_n _) _ _ _ L) as [a [L1 L2]].
rewrite app_comm_cons in *.
exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJConL1 A B _ _ L2).

(*ConL2*)
subst.
destruct (H _ (le_n _) _ _ _ R) as [a [R1 R2]].
rewrite app_comm_cons in *.
exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJConL2 A B _ _ R2).

(*DisL*)
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite app_comm_cons in *.
apply (LJDisL _ _ _ _ L2 R2).
Qed.

Lemma inv_ConL:
  forall n E F Γ1 Γ2 Δ (D: LJ n (Γ1 ++ (Con E F) :: Γ2) Δ),
    (exists m, m <= n /\ LJ m (Γ1 ++ E :: F :: Γ2) Δ).
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
exists 0.
split.

apply le_n.

inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Id*)
apply con_not_var in Ant.
apply in_app_comm in Ant.
apply (in_app_add _ _ (E :: [F]) ) in Ant.
rewrite app_assoc_reverse in Ant.
apply in_app_comm in Ant.
rewrite app_assoc_reverse in Ant.
apply (LJId _ _ Ant).

(*Bot*)
apply con_not_bot in Fal.
apply in_app_comm in Fal.
apply (in_app_add _ _ (E :: [F]) ) in Fal.
rewrite app_assoc_reverse in Fal.
apply in_app_comm in Fal.
rewrite app_assoc_reverse in Fal.
apply (LJBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc_reverse in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (Nat.max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite! app_comm_cons in *.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L2 R2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite! app_assoc in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (Nat.max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite! app_assoc_reverse in *.
apply (LJImpL _ _ _ L2 R2).

(*ImpR*)
subst.
rewrite app_comm_cons in I.
destruct (H _ (le_n _) _ _ _ _ _ I) as [b [I1 I2]].
exists (S b).
split.

apply (le_n_S _ _ I1).

apply (LJImpR I2).

(*ConL1*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (weakening_L _ _ L [B]) as L1.
apply exchange_L in L1.
exists n.
split.

apply (le_S _ _ (le_n _)).

assumption.

inversion Z2.
subst.
rewrite app_assoc_reverse in L.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
rewrite! app_comm_cons in *.
rewrite app_assoc in *.
exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJConL1 A B _ _ L2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (weakening_L _ _ L [F]) as L1.
apply exchange_L in L1.
exists n.
split.

apply (le_S _ _ (le_n _)).

assumption.

inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
rewrite app_assoc_reverse in *.
exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJConL1 A B _ _ L2).

(*ConL2*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (weakening_L _ _ R [A]) as R1.
exists n.
split.

apply (le_S _ _ (le_n _)).

assumption.

inversion Z2.
subst.
rewrite app_assoc_reverse in R.
destruct (H _ (le_n _) _ _ _ _ _ R) as [a [R1 R2]].
rewrite! app_comm_cons in *.
rewrite app_assoc in *.
exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJConL2 A B _ _ R2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (weakening_L _ _ R [E]) as R1.
exists n.
split.

apply (le_S _ _ (le_n _)).

assumption.

inversion Z2.
subst.
rewrite app_comm_cons in R.
rewrite app_assoc in R.
destruct (H _ (le_n _) _ _ _ _ _ R) as [a [R1 R2]].
rewrite app_assoc_reverse in *.
exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJConL2 A B _ _ R2).

(*ConR*)
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

apply (LJConR L2 R2).

(*DisL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc_reverse in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
rewrite! app_comm_cons in *.
rewrite app_assoc in *.
exists (S (max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

apply (LJDisL _ _ _ _ L2 R2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite app_comm_cons in R.
rewrite app_assoc in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
rewrite app_assoc_reverse in *.
exists (S (max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

apply (LJDisL _ _ _ _ L2 R2).

(*DisR1*)
subst.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJDisR1 B L2).

(*DisR2*)
subst.
destruct (H _ (le_n _) _ _ _ _ _ R) as [a [R1 R2]].
exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJDisR2 A R2).
Qed.

Lemma inv_ConR:
  forall n E F Γ (D : LJ n Γ (Con E F)),
   ((exists m, m <= n /\ LJ m Γ E) /\ (exists m, m <= n /\ LJ m Γ F)).
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
subst.
split.

exists 0.
split.

apply le_n.

inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Bot*)
apply (LJBot _ _ Fal).

exists 0.
split.

apply le_n.

inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Bot*)
apply (LJBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L) as [[c [L1 L2]] [d [L3 L4]]].
split.

exists (S (Nat.max c b)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 (le_n _))).

apply (LJImpL _ _ _ L2 R).

exists (S (max d b)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L3 (le_n _))).

apply (LJImpL _ _ _ L4 R).

(*ConL1*)
subst.
destruct (H _ (le_n _) _ _ _ L) as [[a [L1 L2]] [b [L3 L4]]].
split.

exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJConL1 A B _ _ L2).

exists (S b).
split.

apply (le_n_S _ _ L3).

apply (LJConL1 A B _ _ L4).

(*ConL2*)
subst.
destruct (H _ (le_n _) _ _ _ R) as [[a [R1 R2]] [b [R3 R4]]].
split.

exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJConL2 A B _ _ R2).

exists (S b).
split.

apply (le_n_S _ _ R3).

apply (LJConL2 A B _ _ R4).

(*ConR*)
split.

exists a.
split.

apply (le_S _ _ (PeanoNat.Nat.le_max_l _ _)).

assumption.

exists b.
split.

apply (le_S _ _ (PeanoNat.Nat.le_max_r _ _)).

assumption.

(*DisL*)
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L) as [[c [L1 L2]] [d [L3 L4]]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R) as [[e [R1 R2]] [f [R3 R4]]].
split.

exists (S (max c e)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

apply (LJDisL _ _ _ _ L2 R2).

exists (S (max d f)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L3 R3)).

apply (LJDisL _ _ _ _ L4 R4).
Qed.

Lemma inv_DisL:
  forall n E F Γ1 Γ2 Δ (D: LJ n (Γ1 ++ (Dis E F) :: Γ2) Δ),
    (exists m, m <= n /\ LJ m (Γ1 ++ E :: Γ2) Δ) /\ (exists m, m <= n /\ LJ m (Γ1 ++ F :: Γ2) Δ).
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
split.

exists 0.
split.

apply le_n.

inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Id*)
apply dis_not_var in Ant.
apply in_app_comm in Ant.
apply (in_app_add _ _ [E] ) in Ant.
rewrite app_assoc_reverse in Ant.
apply in_app_comm in Ant.
rewrite app_assoc_reverse in Ant.
apply (LJId _ _ Ant).

(*Bot*)
apply dis_not_bot in Fal.
apply in_app_comm in Fal.
apply (in_app_add _ _ [E] ) in Fal.
rewrite app_assoc_reverse in Fal.
apply in_app_comm in Fal.
rewrite app_assoc_reverse in Fal.
apply (LJBot _ _ Fal).

exists 0.
split.

apply le_n.

inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Id*)
apply dis_not_var in Ant.
apply in_app_comm in Ant.
apply (in_app_add _ _ [F] ) in Ant.
rewrite app_assoc_reverse in Ant.
apply in_app_comm in Ant.
rewrite app_assoc_reverse in Ant.
apply (LJId _ _ Ant).

(*Bot*)
apply dis_not_bot in Fal.
apply in_app_comm in Fal.
apply (in_app_add _ _ [F] ) in Fal.
rewrite app_assoc_reverse in Fal.
apply in_app_comm in Fal.
rewrite app_assoc_reverse in Fal.
apply (LJBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [[c [L1 L2]] [d [L3 L4]]].
rewrite app_assoc_reverse in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [[e [R1 R2]] [f [R3 R4]]].
split.

exists (S (Nat.max c e)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite! app_comm_cons in *.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L2 R2).

exists (S (Nat.max d f)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L3 R3)).

rewrite! app_comm_cons in *.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L4 R4).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [[c [L1 L2]] [d [L3 L4]]].
rewrite! app_assoc in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [[e [R1 R2]] [f [R3 R4]]].
split.

exists (S (Nat.max c e)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite! app_assoc_reverse in *.
apply (LJImpL _ _ _ L2 R2).

exists (S (Nat.max d f)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L3 R3)).

rewrite! app_assoc_reverse in *.
apply (LJImpL _ _ _ L4 R4).

(*ImpR*)
subst.
rewrite app_comm_cons in I.
destruct (H _ (le_n _) _ _ _ _ _ I) as [[b [I1 I2]] [c [I3 I4]]].
split.

exists (S b).
split.

apply (le_n_S _ _ I1).

apply (LJImpR I2).

exists (S c).
split.

apply (le_n_S _ _ I3).

apply (LJImpR I4).

(*ConL1*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in L.
destruct (H _ (le_n _) _ _ _ _ _ L) as [[a [L1 L2]] [b [L3 L4]]].
rewrite! app_comm_cons in *.
rewrite! app_assoc in *.
split.

exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJConL1 A B _ _ L2).

exists (S b).
split.

apply (le_n_S _ _ L3).

apply (LJConL1 A B _ _ L4).


destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (le_n _) _ _ _ _ _ L) as [[a [L1 L2]] [b [L3 L4]]].
rewrite! app_assoc_reverse in *.
split.

exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJConL1 A B _ _ L2).

exists (S b).
split.

apply (le_n_S _ _ L3).

apply (LJConL1 A B _ _ L4).

(*ConL2*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in R.
destruct (H _ (le_n _) _ _ _ _ _ R) as [[a [R1 R2]] [b [R3 R4]]].
rewrite! app_comm_cons in *.
rewrite! app_assoc in *.
split.

exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJConL2 A B _ _ R2).

exists (S b).
split.

apply (le_n_S _ _ R3).

apply (LJConL2 A B _ _ R4).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in R.
rewrite app_assoc in R.
destruct (H _ (le_n _) _ _ _ _ _ R) as [[a [R1 R2]] [b [R3 R4]]].
rewrite! app_assoc_reverse in *.
split.

exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJConL2 A B _ _ R2).

exists (S b).
split.

apply (le_n_S _ _ R3).

apply (LJConL2 A B _ _ R4).

(*ConR*)
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [[c [L1 L2]] [d [L3 L4]]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [[e [R1 R2]] [f [R3 R4]]].
split.

exists (S (max c e)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

apply (LJConR L2 R2).

exists (S (max d f)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L3 R3)).

apply (LJConR L4 R4).

(*DisL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
split.

exists a.
split.

apply (le_S _ _ (PeanoNat.Nat.le_max_l _ _)).

assumption.

exists b.

split.
apply (le_S _ _ (PeanoNat.Nat.le_max_r _ _)).

assumption.

inversion Z2.
subst.
rewrite app_assoc_reverse in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [[c [L1 L2]] [d [L3 L4]]].
rewrite app_assoc_reverse in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [[e [R1 R2]] [f [R3 R4]]].
rewrite! app_comm_cons in *.
rewrite! app_assoc in *.
split.

exists (S (max c e)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

apply (LJDisL _ _ _ _ L2 R2).

exists (S (max d f)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L3 R3)).

apply (LJDisL _ _ _ _ L4 R4).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
split.

exists a.
split.

apply (le_S _ _ (PeanoNat.Nat.le_max_l _ _)).

assumption.

exists b.

split.
apply (le_S _ _ (PeanoNat.Nat.le_max_r _ _)).

assumption.

inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [[c [L1 L2]] [d [L3 L4]]].
rewrite app_comm_cons in R.
rewrite app_assoc in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [[e [R1 R2]] [f [R3 R4]]].
rewrite! app_assoc_reverse in *.
split.

exists (S (max c e)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

apply (LJDisL _ _ _ _ L2 R2).

exists (S (max d f)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L3 R3)).

apply (LJDisL _ _ _ _ L4 R4).

(*DisR1*)
subst.
destruct (H _ (le_n _) _ _ _ _ _ L) as [[a [L1 L2]] [b [L3 L4]]].
split.

exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJDisR1 B L2).

exists (S b).
split.

apply (le_n_S _ _ L3).

apply (LJDisR1 B L4).


(*DisR2*)
subst.
destruct (H _ (le_n _) _ _ _ _ _ R) as [[a [R1 R2]] [b [R3 R4]]].
split.

exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJDisR2 A R2).

exists (S b).
split.

apply (le_n_S _ _ R3).

apply (LJDisR2 A R4).
Qed.

Lemma inv_DisR:
  forall n E F Γ (D : LJ n Γ (Dis E F)),
   ((exists m, m <= n /\ LJ m Γ E) \/ (exists m, m <= n /\ LJ m Γ F)).
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
subst.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Bot*)
left.
exists 0.
split.

apply le_n.

apply (LJBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L) as [[c [L1 L2]] | [d [L3 L4]]].

left.
exists (S (Nat.max c b)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 (le_n _))).

apply (LJImpL _ _ _ L2 R).

right.
exists (S (max d b)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L3 (le_n _))).

apply (LJImpL _ _ _ L4 R).

(*ConL1*)
subst.
destruct (H _ (le_n _) _ _ _ L) as [[a [L1 L2]] | [b [L3 L4]]].

left.
exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJConL1 A B _ _ L2).

right.
exists (S b).
split.

apply (le_n_S _ _ L3).

apply (LJConL1 A B _ _ L4).

(*ConL2*)
subst.
destruct (H _ (le_n _) _ _ _ R) as [[a [R1 R2]] | [b [R3 R4]]].

left.
exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJConL2 A B _ _ R2).

right.
exists (S b).
split.

apply (le_n_S _ _ R3).

apply (LJConL2 A B _ _ R4).

(*DisL*)
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L) as [[c [L1 L2]] | [d [L3 L4]]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R) as [[e [R1 R2]] | [f [R3 R4]]].

left.
exists (S (max c e)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

apply (LJDisL _ _ _ _ L2 R2).


left.
exists (S (max c f)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R3)).

admit.

admit.

(*DisR1*)
subst.
left.
exists n.
split.

apply (le_S _ _(le_n _)).

assumption.

(*DisR2*)
subst.
right.
exists n.
split.

apply (le_S _ _(le_n _)).

assumption.
Admitted.


Lemma conj_comm : forall n E F Γ1 Γ2 Δ (D : (Γ1 ++ Con E F :: Γ2) |- Δ >> n),
  (Γ1 ++ Con F E :: Γ2) |- Δ >> n.
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Id*)
subst.
apply con_not_var in Ant.
rewrite in_app_comm in Ant.
pose (in_app_add _ _ [Con F E] Ant) as Ant1.
rewrite app_assoc_reverse in Ant1.
rewrite in_app_comm in Ant1.
rewrite app_assoc_reverse in Ant1.
apply (LJId _ _ Ant1).

(*Bot*)
subst.
apply con_not_bot in Fal.
rewrite in_app_comm in Fal.
pose (in_app_add _ _ [Con F E] Fal) as Fal1.
rewrite app_assoc_reverse in Fal1.
rewrite in_app_comm in Fal1.
rewrite app_assoc_reverse in Fal1.
apply (LJBot _ _ Fal1).

(*Inductive*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- app_comm_cons in *.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L1 R1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite! app_assoc in *.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite! app_assoc_reverse in *.
apply (LJImpL _ _ _ L1 R1).

(*ImpR*)
subst.
rewrite app_comm_cons in I.
pose (H _ (le_n _) _ _ _ _ _ I) as I1.
apply (LJImpR I1).

(*ConL1*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.

subst.
apply (LJConL2 _ _ _ _ L).

inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- app_comm_cons in *.
pose (H _ (le_n _) _ _ _ _ _ L) as L1.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJConL1 _ _ _ _ L1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.

subst.
apply (LJConL2 _ _ _ _ L).

inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite! app_assoc in *.
pose (H _ (le_n _) _ _ _ _ _ L) as L1.
rewrite! app_assoc_reverse in *.
apply (LJConL1 _ _ _ _ L1).

(*ConL2*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.

subst.
apply (LJConL1 _ _ _ _ R).

inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- app_comm_cons in *.
pose (H _ (le_n _) _ _ _ _ _ R) as R1.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJConL2 _ _ _ _ R1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.

subst.
apply (LJConL1 _ _ _ _ R).

inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite! app_assoc in *.
pose (H _ (le_n _) _ _ _ _ _ R) as R1.
rewrite! app_assoc_reverse in *.
apply (LJConL2 _ _ _ _ R1).

(*ConR*)
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
apply (LJConR L1 R1).

(*DisL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- app_comm_cons in *.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJDisL _ _ _ _ L1 R1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite! app_assoc in *.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite! app_assoc_reverse in *.
apply (LJDisL _ _ _ _ L1 R1).

(*DisR1*)
subst.
pose (H _ (le_n _) _ _ _ _ _ L) as L1.
apply (LJDisR1 _ L1).

(*DisR2*)
subst.
pose (H _ (le_n _) _ _ _ _ _ R) as R1.
apply (LJDisR2 _ R1).
Qed.

Lemma conj_assoc_no_height : forall n E F G Γ1 Γ2 Δ (D : (Γ1 ++ Con E (Con F G) :: Γ2) |- Δ >> n),
 exists m, (Γ1 ++ Con (Con E F) G :: Γ2) |- Δ >> m.
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Id*)
subst.
apply con_not_var in Ant.
rewrite in_app_comm in Ant.
pose (in_app_add _ _ [Con (Con E F) G] Ant) as Ant1.
rewrite app_assoc_reverse in Ant1.
rewrite in_app_comm in Ant1.
rewrite app_assoc_reverse in Ant1.
exists 0.
apply (LJId _ _ Ant1).

(*Bot*)
subst.
apply con_not_bot in Fal.
rewrite in_app_comm in Fal.
pose (in_app_add _ _ [Con (Con E F) G] Fal) as Fal1.
rewrite app_assoc_reverse in Fal1.
rewrite in_app_comm in Fal1.
rewrite app_assoc_reverse in Fal1.
exists 0.
apply (LJBot _ _ Fal1).

(*Inductive*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- app_comm_cons in *.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ _ L) as [c L1].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ _ R) as [d R1].
rewrite app_comm_cons in *.
rewrite app_assoc in *.
exists (S (max c d)).
apply (LJImpL _ _ _ L1 R1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite! app_assoc in *.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ _ L) as [c L1].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ _ R) as [d R1].
rewrite! app_assoc_reverse in *.
exists (S (max c d)).
apply (LJImpL _ _ _ L1 R1).

(*ImpR*)
subst.
rewrite app_comm_cons in I.
destruct (H _ (le_n _) _ _ _ _ _ _ I) as [a I1].
exists (S a).
apply (LJImpR I1).

(*ConL1*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.

subst.
exists (S (S n)).
apply (LJConL1 _ _ _ _ (LJConL1 _ _ _ _ L)).

inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- app_comm_cons in *.
destruct (H _ (le_n _) _ _ _ _ _ _ L) as [a L1].
rewrite app_comm_cons in *.
rewrite app_assoc in *.
exists (S a).
apply (LJConL1 _ _ _ _ L1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.

subst.
exists (S (S n)).
apply (LJConL1 _ _ _ _ (LJConL1 _ _ _ _ L)).

inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite! app_assoc in *.
destruct (H _ (le_n _) _ _ _ _ _ _ L) as [a L1].
rewrite! app_assoc_reverse in *.
exists (S a).
apply (LJConL1 _ _ _ _ L1).

(*ConL2*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.

subst.
admit.

inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- app_comm_cons in *.
destruct (H _ (le_n _) _ _ _ _ _ _ R) as [a R1].
rewrite app_comm_cons in *.
rewrite app_assoc in *.
exists (S a).
apply (LJConL2 _ _ _ _ R1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.

subst.
admit.

inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite! app_assoc in *.
pose (H _ (le_n _) _ _ _ _ _ _ R) as R1.
rewrite! app_assoc_reverse in *.
apply (LJConL2 _ _ _ _ R1).

(*ConR*)
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ _ R) as R1.
apply (LJConR L1 R1).

(*DisL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- app_comm_cons in *.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ _ R) as R1.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJDisL _ _ _ _ L1 R1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite! app_assoc in *.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ _ R) as R1.
rewrite! app_assoc_reverse in *.
apply (LJDisL _ _ _ _ L1 R1).

(*DisR1*)
subst.
pose (H _ (le_n _) _ _ _ _ _ _ L) as L1.
apply (LJDisR1 _ L1).

(*DisR2*)
subst.
pose (H _ (le_n _) _ _ _ _ _ _ R) as R1.
apply (LJDisR2 _ R1).
Admitted.

Lemma disj_comm : forall n E F Γ1 Γ2 Δ (D : (Γ1 ++ Dis E F :: Γ2) |- Δ >> n),
  (Γ1 ++ Dis F E :: Γ2) |- Δ >> n.
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Id*)
subst.
apply dis_not_var in Ant.
rewrite in_app_comm in Ant.
pose (in_app_add _ _ [Dis F E] Ant) as Ant1.
rewrite app_assoc_reverse in Ant1.
rewrite in_app_comm in Ant1.
rewrite app_assoc_reverse in Ant1.
apply (LJId _ _ Ant1).

(*Bot*)
subst.
apply dis_not_bot in Fal.
rewrite in_app_comm in Fal.
pose (in_app_add _ _ [Dis F E] Fal) as Fal1.
rewrite app_assoc_reverse in Fal1.
rewrite in_app_comm in Fal1.
rewrite app_assoc_reverse in Fal1.
apply (LJBot _ _ Fal1).

(*Inductive*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- app_comm_cons in *.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L1 R1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite! app_assoc in *.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite! app_assoc_reverse in *.
apply (LJImpL _ _ _ L1 R1).

(*ImpR*)
subst.
rewrite app_comm_cons in I.
pose (H _ (le_n _) _ _ _ _ _ I) as I1.
apply (LJImpR I1).

(*ConL1*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- app_comm_cons in *.
pose (H _ (le_n _) _ _ _ _ _ L) as L1.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJConL1 _ _ _ _ L1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite! app_assoc in *.
pose (H _ (le_n _) _ _ _ _ _ L) as L1.
rewrite! app_assoc_reverse in *.
apply (LJConL1 _ _ _ _ L1).

(*ConL2*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- app_comm_cons in *.
pose (H _ (le_n _) _ _ _ _ _ R) as R1.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJConL2 _ _ _ _ R1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite! app_assoc in *.
pose (H _ (le_n _) _ _ _ _ _ R) as R1.
rewrite! app_assoc_reverse in *.
apply (LJConL2 _ _ _ _ R1).

(*ConR*)
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
apply (LJConR L1 R1).

(*DisL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.

subst.
rewrite PeanoNat.Nat.max_comm.
apply (LJDisL _ _ _ _ R L).

inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- app_comm_cons in *.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJDisL _ _ _ _ L1 R1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.

subst.
rewrite PeanoNat.Nat.max_comm.
apply (LJDisL _ _ _ _ R L).


inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite! app_assoc in *.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite! app_assoc_reverse in *.
apply (LJDisL _ _ _ _ L1 R1).

(*DisR1*)
subst.
pose (H _ (le_n _) _ _ _ _ _ L) as L1.
apply (LJDisR1 _ L1).

(*DisR2*)
subst.
pose (H _ (le_n _) _ _ _ _ _ R) as R1.
apply (LJDisR2 _ R1).
Qed.


Lemma strong_conj: forall n E F Γ1 Γ2 Δ (D : (Γ1 ++ E :: F :: Γ2) |- Δ >> n),
  exists m, m <= S n /\ LJ m (Γ1 ++ (Con E F) :: Γ2) Δ.
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Id*)
subst.

apply in_app_iff in Ant.
destruct Ant as [Ant | Ant].

exists 0.
split.

apply (le_S _ _ (le_n _ )).

apply (LJId _ _ (in_app_add _ _ (Con E F :: Γ2) Ant)).

destruct Ant as [Ant | Ant].

subst.
exists 1.
split.

apply le_n.

apply (LJConL1 _ F _ _ (LJId A (Γ1 ++ # A :: Γ2) (in_elt _ _ _))).

destruct Ant as [Ant | Ant].

subst.
exists 1.
split.

apply le_n.

apply (LJConL2 E _ _ _ (LJId A (Γ1 ++ # A :: Γ2) (in_elt _ _ _))).

exists 0.
split.

apply (le_S _ _ (le_n _ )).

rewrite <- (app_nil_l _).
apply move_R_L.
rewrite <- (app_nil_r _).
rewrite app_comm_cons.
rewrite app_assoc_reverse.
rewrite app_assoc_reverse.
apply swap_L.
rewrite (app_nil_r _).
apply (LJId _ _ (in_app_add _ _ (Con E F :: Γ1) Ant)).

(*Bot*)
subst.

apply in_app_iff in Fal.
destruct Fal as [Fal | Fal].

exists 0.
split.

apply (le_S _ _ (le_n _ )).

apply (LJBot _ _ (in_app_add _ _ (Con E F :: Γ2) Fal)).

destruct Fal as [Fal | Fal].

subst.
exists 1.
split.

apply le_n.

pose (LJBot Δ (Γ1 ++ Bot :: Γ2) (in_elt _ _ _)) as I1.
apply (LJConL1 _ F _ _ I1).

destruct Fal as [Fal | Fal].

subst.
exists 1.
split.

apply le_n.

pose (LJBot Δ (Γ1 ++ Bot :: Γ2) (in_elt _ _ _)) as I1.
apply (LJConL2 E _ _ _ I1).

exists 0.
split.

apply (le_S _ _ (le_n _ )).

rewrite <- (app_nil_l _).
apply move_R_L.
rewrite <- (app_nil_r _).
rewrite app_comm_cons.
rewrite app_assoc_reverse.
rewrite app_assoc_reverse.
apply swap_L.
rewrite (app_nil_r _).
apply (LJBot _ _ (in_app_add _ _ ([Con E F]++Γ1) Fal)).

(*Inductive*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.

admit.

destruct l.

inversion Z2.
subst.
admit.

inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- !app_comm_cons in *.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _).
rewrite PeanoNat.Nat.succ_max_distr.
apply (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1).

rewrite !app_comm_cons in *.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L2 R2).

destruct l.

inversion Z2.
subst.
admit.

inversion Z2.
subst.
rewrite !app_comm_cons in *.
rewrite !app_assoc in *.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _).
rewrite PeanoNat.Nat.succ_max_distr.
apply (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1).

rewrite !app_assoc_reverse in *.
rewrite <- !app_comm_cons in *.
apply (LJImpL _ _ _ L2 R2).

(*ImpR*)
rewrite app_comm_cons in I.
destruct (H _ (le_n _) _ _ _ _ _ I) as [b [I1 I2]].

exists (S b).
split.

apply (le_n_S _ _ I1).

apply (LJImpR I2).

(*ConL1*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].

exists (S a).
split.

apply (le_n_S _ _ L1).

admit.

destruct l.

inversion Z2.
subst.
rewrite app_assoc_reverse in L.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
exists (S a).
split.

apply (le_n_S _ _ L1).

pose (LJConL1 _ B _ _ L2).
admit.

inversion Z2.
subst.
rewrite app_assoc_reverse in L.
rewrite <- !app_comm_cons in L.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
exists (S a).
split.

apply (le_n_S _ _ L1).

rewrite! app_comm_cons in *.
rewrite app_assoc in *.
apply (LJConL1 _ _ _ _ L2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
admit.

destruct l.

inversion Z2.
subst.
rewrite cons_single_app in L.
rewrite app_assoc in L.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
exists (S a).
split.

apply (le_n_S _ _ L1).

rewrite app_assoc_reverse in *.
apply (LJConL1 _ _ _ _ L2).

inversion Z2.
subst.
rewrite !app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
exists (S a).
split.

apply (le_n_S _ _ L1).

rewrite app_assoc_reverse in *.
rewrite <- !app_comm_cons in *.
apply (LJConL1 _ _ _ _ L2).

(*ConL2*)
admit.

(*ConR*)
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _).
rewrite PeanoNat.Nat.succ_max_distr.
apply (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1).

apply (LJConR L2 R2).

(*DisL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.

admit.

destruct l.

inversion Z2.
subst.
admit.

inversion Z2.
subst.
rewrite app_assoc_reverse in *.
rewrite <- !app_comm_cons in *.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _).
rewrite PeanoNat.Nat.succ_max_distr.
apply (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1).

rewrite !app_comm_cons in *.
rewrite app_assoc in *.
apply (LJDisL _ _ _ _ L2 R2).

destruct l.

inversion Z2.
subst.
admit.

inversion Z2.
subst.
rewrite !app_comm_cons in *.
rewrite app_assoc in *.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _).
rewrite PeanoNat.Nat.succ_max_distr.
apply (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1).

rewrite app_assoc_reverse in *.
rewrite <- !app_comm_cons in *.
apply (LJDisL _ _ _ _ L2 R2).

(*DisR1*)
subst.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJDisR1 B L2).

(*DisR2*)
subst.
destruct (H _ (le_n _) _ _ _ _ _ R) as [a [R1 R2]].
exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJDisR2 A R2).
Admitted.

Theorem contraction:
  forall n X Γ1 Γ2 Γ3 Δ (D : (Γ1 ++ X :: Γ2 ++ X :: Γ3) |- Δ >> n),
       exists m, m <= n /\ LJ m (Γ1 ++ X :: Γ2 ++ Γ3 ) Δ.
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
exists 0.
split.

apply le_n.

inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Id*)
subst.
apply in_double in Ant.
apply (LJId _ _ Ant).

(*Bot*)
subst.
apply in_double in Fal.
apply (LJBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (inv_ImpL _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc_reverse in L2.
destruct (H _ (le_trans L1 (PeanoNat.Nat.le_max_l _ _)) B _ _ _ _ L2) as [d [L3 L4]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) (Imp A B) _ _ _ _ R) as [e [R1 R2]].
exists (S (Nat.max d e)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ (le_trans L3 L1) (le_trans R1 (le_n _)))).

apply (LJImpL _ _ _ L4 R2).

inversion Z2 as [[Z3 Z4]].
subst.
assert (Z5 : In p (l ++ A → B :: ΓB)) by apply (in_list_eq Z4).
apply in_app_iff in Z5.
destruct Z5 as [Z5 | [Z5 | Z5]].

destruct (in_split _ _ Z5) as [l1 [l2 Z3]].
subst.
rewrite app_assoc_reverse in L.
rewrite app_comm_cons in L.
rewrite app_assoc_reverse in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) p _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc_reverse in R.
rewrite app_comm_cons in R.
rewrite app_assoc_reverse in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) p _ _ _ _ R) as [d [R1 R2]].
exists (S (Nat.max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L in L2.
apply move_R_L in R2.
rewrite app_assoc in *.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L2 R2).

subst.
rewrite app_assoc_reverse in L.
destruct (inv_ImpL _ _ _ _ L) as [c [L1 L2]].
destruct (H _ (le_trans L1 (PeanoNat.Nat.le_max_l _ _)) _ _ _ _ _ L2) as [d [L3 L4]].
rewrite app_assoc_reverse in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [e [R1 R2]].
exists (S (Nat.max d e)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ (le_trans L3 L1) (le_trans R1 (le_n _)))).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L in L4.
apply move_R_L in R2.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L4 R2).

destruct (in_split _ _ Z5) as [l1 [l2 Z1]].
subst.
rewrite app_assoc_reverse in L.
rewrite app_comm_cons in L.
rewrite (app_assoc (p :: l)) in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc_reverse in R.
rewrite <- app_comm_cons in R.
rewrite app_assoc in R.
rewrite app_assoc in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (Nat.max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L in L2.
apply move_R_L in R2.
rewrite! app_assoc_reverse in *.
rewrite app_assoc in *.
apply (LJImpL _ _ _ L2 R2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (inv_ImpL _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc_reverse in L2.
destruct (H _ ((le_trans L1 (PeanoNat.Nat.le_max_l _ _))) _ _ _ _ _ L2) as [d [L3 L4]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [e [R1 R2]].
exists (S (Nat.max d e)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ (le_trans L3 L1) (le_trans R1 (le_n _)))).

apply (LJImpL _ _ _ L4 R2).

inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite! app_assoc in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (Nat.max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite! app_assoc_reverse in *.
apply (LJImpL _ _ _ L2 R2).

(*ImpR*)
subst.
rewrite app_comm_cons in I.
destruct (H _ (le_n _) _ _ _ _ _ I) as [b [I1 I2]].
exists (S b).
split.

apply (le_n_S _ _ I1).

apply (LJImpR I2).

(*ConL1*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (inv_ConL _ _ _ _ L) as [a [L1 L2]].
rewrite app_assoc_reverse in L2.
destruct (H _ L1 _ _ _ _ _ L2) as [b [L3 L4]].
apply move_R_L in L4.
rewrite app_assoc in L4.
destruct (strong_conj _ _ _ _ L4) as [c [L5 L6]].
exists c.
split.

apply (le_trans L5 (le_n_S _ _ (le_trans L3 L1))).

rewrite app_assoc_reverse in L6.
rewrite cons_single_app.
apply swap_L.
assumption.

inversion Z2 as [[Z3 Z4]].
subst.
assert (Z5 : In p (l ++ Con A B :: ΓB)) by apply (in_list_eq Z4).
apply in_app_iff in Z5.
destruct Z5 as [Z5 | [Z5 | Z5]].

destruct (in_split _ _ Z5) as [l1 [l2 Z3]].
subst.
rewrite app_assoc_reverse in L.
rewrite app_comm_cons in L.
rewrite app_assoc_reverse in L.
destruct (H _ (le_n _) p _ _ _ _ L) as [a [L1 L2]].
exists (S a).
split.

apply (le_n_S _ _ L1).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L in L2.
rewrite app_assoc in *.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJConL1 _ _ _ _ L2).

subst.
rewrite app_assoc_reverse in L.
rewrite <- app_comm_cons in L.
destruct (inv_ConL _ _ _ _ L) as [a [L1 L2]].
rewrite app_comm_cons in L2.
destruct (H _ L1 _ _ _ _ _ L2) as [b [L3 L4]].
destruct (strong_conj _ _ _ _ L4) as [c [L5 L6]].
exists c.
split.

apply (le_trans L5 (le_n_S _ _ (le_trans L3 L1))).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L in L6.
assumption.

destruct (in_split _ _ Z5) as [l1 [l2 Z1]].
subst.
rewrite app_assoc_reverse in L.
rewrite app_comm_cons in L.
rewrite (app_assoc (p :: l)) in L.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
exists (S a).
split.

apply (le_n_S _ _ L1).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L in L2.
rewrite! app_assoc_reverse in *.
rewrite app_assoc in *.
apply (LJConL1 _ _ _ _ L2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (inv_ConL _ _ _ _ L) as [a [L1 L2]].
rewrite app_assoc_reverse in L2.
destruct (H _ L1 _ _ _ _ _ L2) as [b [L3 L4]].
apply move_R_L in L4.
rewrite app_assoc in L4.
destruct (strong_conj _ _ _ _ L4) as [c [L5 L6]].
exists c.
split.

apply (le_trans L5 (le_n_S _ _ (le_trans L3 L1))).

rewrite cons_single_app.
apply swap_L.
rewrite app_assoc.
assumption.

inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
exists (S a).
split.

apply (le_n_S _ _ L1).

rewrite! app_assoc_reverse in *.
apply (LJConL1 _ _ _ _ L2).

(*ConL2*)
subst.
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
rewrite app_comm_cons in R.
rewrite app_assoc in R.
destruct (inv_ConL _ _ _ _ R) as [a [R1 R2]].
rewrite app_assoc_reverse in R2.
rewrite (cons_single_app A) in R2.
rewrite <- app_comm_cons in R2.
rewrite app_assoc in R2.
destruct (H _ R1 _ _ _ _ _ R2) as [b [R3 R4]].
rewrite app_assoc_reverse in R4.
apply move_R_L in R4.
rewrite app_assoc in R4.
apply exchange_L in R4.
destruct (strong_conj _ _ _ _ R4) as [c [R5 R6]].
exists c.
split.

apply (le_trans R5 (le_n_S _ _ (le_trans R3 R1))).

rewrite app_assoc_reverse in R6.
rewrite cons_single_app.
apply swap_L.
assumption.

inversion Z2 as [[Z3 Z4]].
subst.
assert (Z5 : In p (l ++ Con A B :: ΓB)) by apply (in_list_eq Z4).
apply in_app_iff in Z5.
destruct Z5 as [Z5 | [Z5 | Z5]].

destruct (in_split _ _ Z5) as [l1 [l2 Z3]].
subst.
rewrite app_assoc_reverse in R.
rewrite app_comm_cons in R.
rewrite app_assoc_reverse in R.
destruct (H _ (le_n _) p _ _ _ _ R) as [a [R1 R2]].
exists (S a).
split.

apply (le_n_S _ _ R1).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L in R2.
rewrite app_assoc in *.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJConL2 _ _ _ _ R2).

subst.
rewrite app_assoc_reverse in R.
rewrite <- app_comm_cons in R.
destruct (inv_ConL _ _ _ _ R) as [a [R1 R2]].
rewrite cons_single_app in R2.
rewrite app_assoc in R2.
destruct (H _ R1 _ _ _ _ _ R2) as [b [R3 R4]].
rewrite app_assoc_reverse in R4.
destruct (strong_conj _ _ _ _ R4) as [c [R5 R6]].
exists c.
split.

apply (le_trans R5 (le_n_S _ _ (le_trans R3 R1))).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L in R6.
assumption.

destruct (in_split _ _ Z5) as [l1 [l2 Z1]].
subst.
rewrite app_assoc_reverse in R.
rewrite app_comm_cons in R.
rewrite (app_assoc (p :: l)) in R.
destruct (H _ (le_n _) _ _ _ _ _ R) as [a [R1 R2]].
exists (S a).
split.

apply (le_n_S _ _ R1).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L in R2.
rewrite! app_assoc_reverse in *.
rewrite app_assoc in *.
apply (LJConL2 _ _ _ _ R2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
rewrite app_comm_cons in R.
rewrite app_assoc in R.
destruct (inv_ConL _ _ _ _ R) as [a [R1 R2]].
rewrite app_assoc_reverse in R2.
rewrite (cons_single_app A) in R2.
rewrite <- app_comm_cons in R2.
rewrite app_assoc in R2.
destruct (H _ R1 _ _ _ _ _ R2) as [b [R3 R4]].
apply move_R_L in R4.
rewrite app_assoc_reverse in R4.
rewrite app_assoc in R4.
destruct (strong_conj _ _ _ _ R4) as [c [R5 R6]].
exists c.
split.

apply (le_trans R5 (le_n_S _ _ (le_trans R3 R1))).

rewrite cons_single_app.
apply swap_L.
rewrite app_assoc.
assumption.

inversion Z2.
subst.
rewrite app_comm_cons in R.
rewrite app_assoc in R.
destruct (H _ (le_n _) _ _ _ _ _ R) as [a [R1 R2]].
exists (S a).
split.

apply (le_n_S _ _ R1).

rewrite! app_assoc_reverse in *.
apply (LJConL2 _ _ _ _ R2).

(*ConR*)
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

apply (LJConR L2 R2).

(*DisL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
destruct (inv_DisL _ _ _ _ L) as [[c [L1 L2]] _].
destruct (inv_DisL _ _ _ _ R) as [_ [e [R1 R2]]].
rewrite app_assoc_reverse in *.
destruct (H _ (le_trans L1 (PeanoNat.Nat.le_max_l _ _)) _ _ _ _ _ L2) as [d [L3 L4]].
destruct (H _ (le_trans R1 (PeanoNat.Nat.le_max_r _ _)) _ _ _ _ _ R2) as [f [R3 R4]].
exists (S (max d f)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ (le_trans L3 L1) (le_trans R3 R1))).

apply (LJDisL _ _ _ _ L4 R4).

inversion Z2 as [[Z3 Z4]].
subst.
assert (Z5 : In p (l ++ Dis A B :: ΓB)) by apply (in_list_eq Z4).
apply in_app_iff in Z5.
destruct Z5 as [Z5 | [Z5 | Z5]].

destruct (in_split _ _ Z5) as [l1 [l2 Z3]].
subst.
rewrite app_assoc_reverse in L.
rewrite app_comm_cons in L.
rewrite app_assoc_reverse in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) p _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc_reverse in R.
rewrite app_comm_cons in R.
rewrite app_assoc_reverse in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) p _ _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L in L2.
apply move_R_L in R2.
rewrite app_assoc in *.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LJDisL _ _ _ _ L2 R2).

subst.
rewrite app_assoc_reverse in *.
rewrite <- app_comm_cons in *.
destruct (inv_DisL _ _ _ _ L) as [[c [L1 L2]] _].
destruct (H _ (le_trans L1 (PeanoNat.Nat.le_max_l _ _)) _ _ _ _ _ L2) as [d [L3 L4]].
destruct (inv_DisL _ _ _ _ R) as [_ [e [R1 R2]]].
destruct (H _ (le_trans R1 (PeanoNat.Nat.le_max_r _ _)) _ _ _ _ _ R2) as [f [R3 R4]].
exists (S (max d f)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ (le_trans L3 L1) (le_trans R3 R1))).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L.
apply (LJDisL _ _ _ _ L4 R4).

destruct (in_split _ _ Z5) as [l1 [l2 Z1]].
subst.
rewrite app_assoc_reverse in L.
rewrite app_comm_cons in L.
rewrite (app_assoc (p :: l)) in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc_reverse in R.
rewrite app_comm_cons in R.
rewrite (app_assoc (p :: l)) in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L in L2.
apply move_R_L in R2.
rewrite! app_assoc_reverse in *.
rewrite app_assoc in *.
apply (LJDisL _ _ _ _ L2 R2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
destruct (inv_DisL _ _ _ _ L) as [[c [L1 L2]] _].
destruct (inv_DisL _ _ _ _ R) as [_ [e [R1 R2]]].
rewrite app_assoc_reverse in *.
destruct (H _ (le_trans L1 (PeanoNat.Nat.le_max_l _ _)) _ _ _ _ _ L2) as [d [L3 L4]].
destruct (H _ (le_trans R1 (PeanoNat.Nat.le_max_r _ _)) _ _ _ _ _ R2) as [f [R3 R4]].
exists (S (max d f)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ (le_trans L3 L1) (le_trans R3 R1))).

apply (LJDisL _ _ _ _ L4 R4).

inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite app_comm_cons in R.
rewrite app_assoc in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite app_assoc_reverse in *.
apply (LJDisL _ _ _ _ L2 R2).

(*DisR1*)
subst.
destruct (H _ (le_n _) _ _ _ _ _ L) as [a [L1 L2]].
exists (S a).
split.

apply (le_n_S _ _ L1).

apply (LJDisR1 B L2).

(*DisR2*)
subst.
destruct (H _ (le_n _) _ _ _ _ _ R) as [a [R1 R2]].
exists (S a).
split.

apply (le_n_S _ _ R1).

apply (LJDisR2 A R2).
Qed.

Theorem cut_elimination:
  forall A n m Γ Δ (D : LJ n Γ A) (D1 : LJ m ([A] ++ Γ) Δ),
    exists k, Γ |- Δ >> k.
Proof.
intros A.
induction A.

(*PropVar*)
intros n.
induction n using strong_induction.

(*Base Case n*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Id*)
subst.
destruct (in_split _ _ Ant) as [l1 [l2 Z1]].
subst.
destruct (contraction _ [] _ _ D1) as [a [I1 I2]].
apply move_R_L in I2.
exists a.
assumption.

(*Bot*)
exists 0.
apply (LJBot _ _ Fal).

(*Inductive n*)
intros.
subst.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
rewrite app_assoc in D1.
destruct (inv_ImpL _ _ _ _ D1) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L L2) as [d L3].
exists (S (max d b)).
apply (LJImpL _ _ _ L3 R).

(*ConL1*)
subst.
rewrite app_assoc in D1.
destruct (inv_ConL _ _ _ _ D1) as [c [L1 L2]].
rewrite app_assoc_reverse in L2.
rewrite cons_single_app in L.
rewrite app_assoc in L.
pose (weakening_L (ΓA ++ [A]) _ L [B]) as L3.
rewrite app_assoc_reverse in L3.
destruct (H _ (le_n _) _ _ _ L3 L2) as [d L4].
destruct (strong_conj _ _ _ _ L4) as [e [L5 L6]].
exists e.
assumption.

(*ConL2*)
subst.
rewrite app_assoc in D1.
destruct (inv_ConL _ _ _ _ D1) as [c [R1 R2]].
rewrite app_assoc_reverse in R2.
pose (weakening_L ΓA _ R [A]) as R3.
destruct (H _ (le_n _) _ _ _ R3 R2) as [d R4].
destruct (strong_conj _ _ _ _ R4) as [e [R5 R6]].
exists e.
assumption.

(*DisL*)
subst.
rewrite app_assoc in D1.
destruct (inv_DisL _ _ _ _ D1) as [[c [L1 L2]] [d [R1 R2]]].
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L L2) as [e L3].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R R2) as [f R3].
exists (S (max e f)).
apply (LJDisL _ _ _ _ L3 R3).

(*Bot*)
intros n.
induction n using strong_induction.

(*Base Case n*)
intros.
subst.
exists 0.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Bot*)
apply (LJBot _ _ Fal).

(*Inductive n*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
rewrite app_assoc in D1.
destruct (inv_ImpL _ _ _ _ D1) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L L2) as [d L3].
exists (S (max d b)).
apply (LJImpL _ _ _ L3 R).

(*ConL1*)
subst.
rewrite app_assoc in D1.
destruct (inv_ConL _ _ _ _ D1) as [c [L1 L2]].
rewrite app_assoc_reverse in L2.
rewrite cons_single_app in L.
rewrite app_assoc in L.
pose (weakening_L (ΓA ++ [A]) _ L [B]) as L3.
rewrite app_assoc_reverse in L3.
destruct (H _ (le_n _) _ _ _ L3 L2) as [d L4].
destruct (strong_conj _ _ _ _ L4) as [e [L5 L6]].
exists e.
assumption.

(*ConL2*)
subst.
rewrite app_assoc in D1.
destruct (inv_ConL _ _ _ _ D1) as [c [R1 R2]].
rewrite app_assoc_reverse in R2.
pose (weakening_L ΓA _ R [A]) as R3.
destruct (H _ (le_n _) _ _ _ R3 R2) as [d R4].
destruct (strong_conj _ _ _ _ R4) as [e [R5 R6]].
exists e.
assumption.

(*DisL*)
subst.
rewrite app_assoc in D1.
destruct (inv_DisL _ _ _ _ D1) as [[c [L1 L2]] [d [R1 R2]]].
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L L2) as [e L3].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R R2) as [f R3].
exists (S (max e f)).
apply (LJDisL _ _ _ _ L3 R3).

(*Imp*)
intros n.
induction n using strong_induction.

(*Base Case n*)
intros.
inversion D as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Bot*)
exists 0.
apply (LJBot _ _ Fal).

(*Inductive n*)
intros m.
induction m using strong_induction.

(*Base Case m : n = n*)
intros.
inversion D1 as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*Id*)
destruct Ant as [Ant | Ant].

discriminate.

exists 0.
apply (LJId _ _ Ant).

(*Bot*)
destruct Fal as [Fal | Fal].

discriminate.

exists 0.
apply (LJBot _ _ Fal).

(*Inductive m : n = n*)
intros.
inversion D1 as [ A ΓT Ant Height EqA EqS | A ΓT Fal Height EqA EqS | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT I Height EqA EqS | a A B ΓA ΓB ΔT L Height EqS EqA | a A B ΓA ΓB ΔT R Height EqS EqA | a b A B ΓT L R Height EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT L Height EqS EqA | a A B ΓT R Height EqS EqA].

(*ImpL*)
subst.
destruct ΓA.

inversion EqS.
subst.
destruct (H0 _ (PeanoNat.Nat.le_max_r _ _) _ _ D R) as [c I1].
destruct (inv_ImpR D) as [d [I2 I3]].
destruct (IHA1 _ _ _ _ I1 I3) as [e I4].
destruct (IHA2 _ _ _ _ I4 L) as [f I5].
exists f.
assumption.

inversion EqS.
subst.
destruct (H0 _ (PeanoNat.Nat.le_max_r _ _) _ _ D R) as [c R1].
pose (weakening_L _ _ R1 [Imp A B]) as R2.
rewrite app_assoc in R2.
rewrite cons_single_app in D.
rewrite app_assoc in D.
pose (weakening_L _ _ D [B]) as L1.
rewrite app_assoc_reverse in L1.
pose (weakening_L _ _ L [Imp A B]) as L2.
destruct (H0 _ (PeanoNat.Nat.le_max_l _ _) _ _ L1 L2) as [d L3].
rewrite app_assoc in L3.
pose (LJImpL _ _ _ L3 R2) as I1.
rewrite app_assoc_reverse in I1.
destruct (contraction _ _ [] _ I1) as [e [I2 I3]].
exists e.
assumption.

(*ImpR*)
subst.
pose (weakening_L [] _ D [A]) as I1.
rewrite <- (app_nil_l (A :: [A1 → A2] ++ Γ)) in I.
apply move_R_L in I.
destruct (H0 _ (le_n _) _ _ I1 I) as [c I2].
exists (S c).
apply (LJImpR I2).

(*ConL1*)
subst.
destruct ΓA.
inversion EqS.
inversion EqS.
subst.
rewrite (cons_single_app A) in L.
rewrite app_assoc in L.
pose (weakening_L _ _ L [B]) as L1.
rewrite! app_assoc_reverse in L1.
destruct (inv_ConL _ _ _ _ D) as [a [R1 R2]].
inversion R1 as [R3 | d R3 R4].

subst.
destruct (H0 _ (le_n _) _ _ R2 L1) as [b I1].
destruct (strong_conj _ _ _ _ I1) as [c [I2 I3]].
exists c.
assumption.

destruct (H _ R3 _ _ _ R2 L1) as [b I1].
destruct (strong_conj _ _ _ _ I1) as [c [I2 I3]].
exists c.
assumption.

(*ConL2*)
subst.
destruct ΓA.
inversion EqS.
inversion EqS.
subst.
pose (weakening_L _ _ R [A]) as R1.
destruct (inv_ConL _ _ _ _ D) as [a [L1 L2]].
inversion L1 as [L3 | d L3 L4].

subst.
destruct (H0 _ (le_n _) _ _ L2 R1) as [b I1].
destruct (strong_conj _ _ _ _ I1) as [c [I2 I3]].
exists c.
assumption.

destruct (H _ L3 _ _ _ L2 R1) as [b I1].
destruct (strong_conj _ _ _ _ I1) as [c [I2 I3]].
exists c.
assumption.

(*ConR*)
subst.
destruct (H0 _ (PeanoNat.Nat.le_max_l _ _) _ _ D L) as [c L1].
destruct (H0 _ (PeanoNat.Nat.le_max_r _ _) _ _ D R) as [d R1].
exists (S (max c d)).
apply (LJConR L1 R1).

(*DisL*)
subst.
destruct ΓA.
inversion EqS.
inversion EqS.
subst.
destruct (inv_DisL _ _ _ _ D) as [[c [I1 I2]] [d [I3 I4]]].
inversion I1 as [I5 | e I5 I6].

subst.
destruct (H0 _ (PeanoNat.Nat.le_max_l _ _) _ _ I2 L) as [g I9].
inversion I3 as [I7 | f I7 I8].

subst.
destruct (H0 _ (PeanoNat.Nat.le_max_r _ _) _ _ I4 R) as [h I10].
exists (S (max g h)).
apply (LJDisL _ _ _ _ I9 I10).

destruct (H _ I7 _ _ _ I4 R) as [h I10].
exists (S (max g h)).
apply (LJDisL _ _ _ _ I9 I10).

subst.
destruct (H _ I5 _ _ _ I2 L) as [g I9].
inversion I3 as [I7 | f I7 I8].

subst.
destruct (H0 _ (PeanoNat.Nat.le_max_r _ _) _ _ I4 R) as [h I10].
exists (S (max g h)).
apply (LJDisL _ _ _ _ I9 I10).

destruct (H _ I7 _ _ _ I4 R) as [h I10].
exists (S (max g h)).
apply (LJDisL _ _ _ _ I9 I10).

(*DisR1*)
subst.
destruct (H0 _ (le_n _) _ _ D L) as [a L1].
exists (S a).
apply (LJDisR1 B L1).

(*DisR2*)
subst.
destruct (H0 _ (le_n _) _ _ D R) as [a R1].
exists (S a).
apply (LJDisR2 A R1).

(*Con*)
intros.
destruct (inv_ConR D) as [[a [L1 L2]] [b [R1 R2]]].
destruct (inv_ConL _ _ [] _ D1) as [c [I1 I2]].
pose (weakening_L [] _ L2 [A2]) as I3.
destruct (IHA1 _ _ _ _ I3 I2) as [d I4].
destruct (IHA2 _ _ _ _ R2 I4) as [e I5].
exists e.
assumption.

(*Dis*)
intros.
destruct (inv_DisL _ _ [] _ D1) as [[a [I1 I2]] [b [I3 I4]]].
destruct (inv_DisR D) as [[c [I5 I6]] | [c [I5 I6]]].

apply (IHA1 _ _ _ _ I6 I2).

apply (IHA2 _ _ _ _ I6 I4).
Admitted.