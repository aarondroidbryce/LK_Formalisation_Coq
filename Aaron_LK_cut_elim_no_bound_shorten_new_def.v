Require Export List.
Add LoadPath "../../lnt/tense-logic-in-Coq".
Require Import Strong_induction.
Set Implicit Arguments.
Export ListNotations.

Delimit Scope My_scope with M.
Open Scope My_scope.

(**Defintions**)

(*Definitaion of Propositional Variables*)
Parameter PropVars : Set.
Hypothesis Varseq_dec : forall x y:PropVars, {x = y} + {x <> y}.

(*Definition of Propositional Formulas*)
Inductive PropF : Set :=
 | Var : PropVars -> PropF
 | Bot : PropF
 | Imp : PropF -> PropF -> PropF
.

Notation "# P" := (Var P) (at level 1) : My_scope.
Notation "A → B" := (Imp A B) (at level 16, right associativity) : My_scope.
Notation "⊥" := Bot (at level 0)  : My_scope.

(* Defined connectives *)
Notation "¬ A" := (A → ⊥) (at level 1)  : My_scope.
Notation "A ∧ B" := ((A → (B → ⊥)) → ⊥) (at level 15, right associativity) : My_scope.
Notation "A ∨ B" := ((A → ⊥) → B) (at level 15, right associativity) : My_scope.

(* Valuations are maps PropVars -> bool sending ⊥ to false*)
Fixpoint TrueQ v A : bool := match A with
 | # P   => v P
 | ⊥     => false
 | B → C => (negb (TrueQ v B)) || (TrueQ v C)
end.

(* Prove that the defined connectives are correct *)

Lemma def_neg_correct (A: PropF) :
  forall v, TrueQ v (¬ A) = negb (TrueQ v A).
Proof. intros. destruct A.
       simpl. rewrite Bool.orb_false_r. trivial.
       simpl. trivial.
       simpl. rewrite Bool.orb_false_r. trivial.
Qed.

Lemma def_or_correct (A B: PropF) :
  forall v, TrueQ v (A ∨ B) = orb (TrueQ v A) (TrueQ v B).
Proof. intros. simpl. repeat rewrite Bool.orb_false_r.
       rewrite Bool.negb_involutive.
       trivial.
Qed.

Lemma def_and_correct (A B: PropF) :
  forall v, TrueQ v (A ∧ B) = andb (TrueQ v A) (TrueQ v B).
Proof. intros. simpl. repeat rewrite Bool.orb_false_r.
       repeat rewrite Bool.negb_orb.
       repeat rewrite Bool.negb_involutive.
       reflexivity.
Qed.

Fixpoint  weight p :=
    match p with
      | # q' => 0
      | Bot => 0
      | p' → q' => S (max (weight p') (weight q'))
      end.

(*Gentzen's Sequent Calculus*)

Reserved Notation "Γ |- Δ >> n" (at level 80).
Inductive LK : nat -> list PropF -> list PropF -> Prop :=
| LKId  : forall A Γ Δ, In (Var A) Δ -> In (Var A) Γ -> LK 0 Γ Δ
| LKBot : forall Γ Δ,   In ⊥ Γ  -> LK 0 Γ Δ
| LKImpL : forall n m A B Γ1 Γ2 Δ,
              LK n (Γ1++B::Γ2) Δ -> LK m (Γ1++Γ2) (A::Δ)
           -> LK (S (max n m)) (Γ1++A→B::Γ2) Δ
| LKImpR : forall n A B Γ Δ1 Δ2,
              LK n (A::Γ) (Δ1++B::Δ2)
           -> LK (S n) Γ (Δ1++A→B::Δ2)
where "Γ |- Δ >> n" := (LK (n) (Γ) (Δ)) : My_scope.

(**Auxiliary Lemmas**)

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

(*Sanity Check that Γ1,A,Γ2 |- Δ1,A,Δ2 is Deriavable *)

Lemma Id_extension : forall A Γ Δ, In A Δ -> In A Γ -> exists n, weight A <= n /\ Γ |- Δ >> n.
Proof.
intros A.
induction A.

(*PropVar*)
intros.
exists 0.
split.
apply le_n.
apply (LKId p _ _ H H0).

(*Bot*)
intros.
exists 0.
split.
apply le_n.
apply (LKBot _ _ H0).

(*Imp*)
intros.
simpl.
apply in_split in H.
destruct H as [l1 [l2 Z1]].
apply in_split in H0.
destruct H0 as [l3 [l4 Z2]].
subst.
destruct (IHA1 (A1 :: l3 ++ l4) (A1 :: l1 ++ A2 :: l2) (in_eq A1 _) (in_eq A1 _)) as [a [I1 I2]].
destruct (IHA2 ((A1 :: l3) ++ A2 :: l4) (l1 ++ A2 :: l2) (in_elt A2 _ _) (in_elt A2 _ _)) as [b [I3 I4]].
pose (LKImpL _ _ _ I4 I2) as I5.
exists (S (S (max b a))).
split.

rewrite PeanoNat.Nat.max_comm.
apply (le_n_S _ _ (le_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ I3 I1))).

apply (LKImpR _ _ _ I5).
Qed.

(*Proof of Other Structural Inferences*)

Lemma exchange_R:
  forall n Γ E F Δ1 Δ2 (D: LK n Γ (Δ1 ++ E :: F :: Δ2)), LK n Γ (Δ1 ++ F :: E :: Δ2).
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*Id*)
apply in_cons_comm in Suc.
apply (LKId _ _ _ Suc Ant).

(*Bot*)
apply (LKBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ImpL*)
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
rewrite app_comm_cons in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
apply (LKImpL _ _ _ L1 R1).

(*ImpR*)
subst.
destruct (app_eq_app _ _ _ _ EqA) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (le_n _) _ _ _ _ _ I) as I1.
rewrite (cons_single_app F) in *.
rewrite app_assoc in *.
apply (LKImpR _ _ _ I1).

destruct l.

inversion Z2.
subst.
rewrite app_assoc_reverse in I.
pose (H _ (le_n _) _ _ _ _ _ I) as I1.
apply (LKImpR _ _ _ I1).

inversion Z2.
subst.
rewrite app_assoc_reverse in I.
rewrite <- !app_comm_cons in I.
pose (H _ (le_n _) _ _ _ _ _ I) as I1.
rewrite! app_comm_cons in *.
rewrite app_assoc in *.
apply (LKImpR _ _ _ I1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (le_n _) _ _ _ _ _ I) as I1.
rewrite (cons_single_app F _).
rewrite (cons_single_app F _) in I1.
rewrite app_assoc in *.
apply (LKImpR _ _ _ I1).

inversion Z2.
subst.
rewrite app_comm_cons in I.
rewrite app_assoc in I.
pose (H _ (le_n _) _ _ _ _ _ I) as I1.
rewrite app_assoc_reverse in *.
apply (LKImpR _ _ _ I1).
Qed.

Lemma exchange_L:
  forall n E F Γ1 Γ2 Δ (D: LK n (Γ1 ++ E :: F :: Γ2) Δ), LK n (Γ1 ++ F :: E :: Γ2) Δ.
Proof.
intro n.
induction n using strong_induction.

(*Base Case*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*Id*)
apply in_cons_comm in Ant.
apply (LKId _ _ _ Suc Ant).

(*Bot*)
apply in_cons_comm in Fal.
apply (LKBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ImpL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
rewrite (cons_single_app F) in *.
rewrite app_assoc in *.
apply (LKImpL _ _ _ L1 R).

inversion Z2 as [[Z3 Z4]].
destruct l.

inversion Z4.
subst.
rewrite app_assoc_reverse in L.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
rewrite app_assoc_reverse in R.
apply (LKImpL _ _ _ L1 R).
 
inversion Z4.
subst.
rewrite app_assoc_reverse in L.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
rewrite app_assoc_reverse in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite! app_comm_cons in *.
rewrite app_assoc in *.
apply (LKImpL _ _ _ L1 R1).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
rewrite (cons_single_app F) in *.
rewrite app_assoc in *.
apply (LKImpL _ _ _ L1 R).

inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as L1.
rewrite app_assoc in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as R1.
rewrite app_assoc_reverse in *.
apply (LKImpL _ _ _ L1 R1).

(*ImpR*)
subst.
rewrite app_comm_cons in I.
pose (H _ (le_n _) _ _ _ _ _ I) as I1.
apply (LKImpR _ _ _ I1).
Qed.

(*Strengthening Exchange from Single Elements to Lists*)
(*----------------------------------------------------*)

Lemma move_R_R: forall n Γ A Δ3 Δ2 Δ1,
                LK n Γ (Δ1 ++ A :: Δ2 ++ Δ3) ->
                LK n Γ (Δ1 ++ Δ2 ++ A :: Δ3).
Proof.
intros n Γ A Δ3 Δ2.
induction Δ2.

intros.
assumption.

intros.
rewrite cons_single_app. 
rewrite app_assoc_reverse.
rewrite app_assoc.
apply IHΔ2.
rewrite app_assoc_reverse.
apply exchange_R. 
assumption.
Qed.

Lemma swap_R:
  forall n Γ Δ2 Δ3 Δ1 Δ4,
    LK n Γ (Δ1 ++ Δ2 ++ Δ3 ++ Δ4) ->
    LK n Γ (Δ1 ++ Δ3 ++ Δ2 ++ Δ4).
Proof.
intros n Γ Δ2 Δ3.
induction Δ2.

intros.
assumption.

intros.
apply move_R_R.
rewrite cons_single_app.
rewrite app_assoc.
rewrite cons_single_app in H.
rewrite app_assoc_reverse in H.
rewrite app_assoc in H.
apply (IHΔ2 _ _ H).
Qed.

Lemma move_R_L:
  forall n Δ A Γ3 Γ2 Γ1,
    LK n (Γ1 ++ A :: Γ2 ++ Γ3) Δ ->
    LK n (Γ1 ++ Γ2 ++ A :: Γ3) Δ.
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
    LK n (Γ1 ++ Γ2 ++ Γ3 ++ Γ4) Δ->
    LK n (Γ1 ++ Γ3 ++ Γ2 ++ Γ4) Δ.
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

(*-----------------------------------------*)
(*Return to Proofs of Structural Inferneces*)

Lemma weakening_R:
  forall n Γ Δ1 Δ2 (D: LK n Γ (Δ1 ++ Δ2)),
    forall W, (LK n Γ (Δ1 ++ W ++ Δ2)).
Proof.
intro n.
induction n using strong_induction.

(*Base Case*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*Id*)
rewrite in_app_comm in Suc.
apply (in_app_add _ _ W) in Suc.
rewrite app_assoc_reverse in Suc.
rewrite in_app_comm in Suc.
rewrite app_assoc_reverse in Suc.
apply (LKId _ _ _ Suc Ant).

(*Bot*)
apply (LKBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ImpL*)
subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L W) as L1.
rewrite app_comm_cons in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R W) as R1.
apply (LKImpL _ _ _ L1 R1).

(*ImpR*)
subst.
rewrite <- app_nil_r.
rewrite! app_assoc_reverse.
apply swap_R.
rewrite app_assoc.
rewrite <- EqA.
rewrite app_assoc_reverse.
rewrite <- app_nil_r in I.
pose (H _ (le_n _) _ _ _ I W) as I1.
rewrite! app_assoc_reverse in I1.
apply (LKImpR _ _ _ I1).
Qed.

Lemma weakening_L:
    forall n Γ1 Γ2 Δ (D: LK n (Γ1 ++ Γ2) Δ),
      forall W, LK n (Γ1 ++ W ++ Γ2) Δ.
Proof.
intro n.
induction n using strong_induction.

(*Base Case*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*Id*)
rewrite in_app_comm in Ant.
apply (in_app_add _ _ W) in Ant.
rewrite app_assoc_reverse in Ant.
rewrite in_app_comm in Ant.
rewrite app_assoc_reverse in Ant.
apply (LKId _ _ _ Suc Ant).

(*Bot*)
rewrite in_app_comm in Fal.
apply (in_app_add _ _ W) in Fal.
rewrite app_assoc_reverse in Fal.
rewrite in_app_comm in Fal.
rewrite app_assoc_reverse in Fal.
apply (LKBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ImpL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

subst.
rewrite app_assoc_reverse in L.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L W) as L1.
rewrite app_assoc_reverse in R.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R W) as R1.
rewrite! app_assoc in *.
apply (LKImpL _ _ _ L1 R1).

subst.
pose (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L W) as L1.
pose (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R W) as R1.
rewrite app_assoc_reverse.
apply swap_L.
rewrite <- Z2.
rewrite app_assoc in *.
apply (LKImpL _ _ _ L1 R1).

(*ImpR*)
subst.
rewrite app_comm_cons in I.
pose (H _ (le_n _) _ _ _ I W) as I1.
apply (LKImpR _ _ _ I1).
Qed.

(* Implication left derives one sequent from two previously derived sequents
   so inversion is split into two lemmas, one for each of the sequents    *)

Lemma inv_ImpL1 :
  forall n E F Γ1 Γ2 Δ (D: LK n (Γ1 ++ E→F :: Γ2) Δ),
    (exists m, m <= n /\ LK m (Γ1 ++ Γ2) (E::Δ)).
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
exists 0.
split.

apply le_n.

inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*Id*)
apply imp_not_var in Ant.
pose (in_app_add _ Δ [E] Suc) as Suc1.
apply in_app_comm in Suc1.
apply (LKId _ _ _ Suc1 Ant).

(*Bot*)
apply imp_not_bot in Fal.
apply (LKBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ImpL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
exists b.
split.

apply (le_S _ _ (PeanoNat.Nat.le_max_r _ _)).

assumption.

inversion Z2.
subst.
rewrite app_assoc_reverse in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc_reverse in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

pose (exchange_R _ _ [] _ R2) as R3.
rewrite app_assoc in *.
apply (LKImpL _ _ _ L2 R3).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
exists b.
split.

apply (le_S _ _ (PeanoNat.Nat.le_max_r _ _)).

assumption.

inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

pose (exchange_R _ _ [] _ R2) as R3.
rewrite app_assoc_reverse in *.
apply (LKImpL _ _ _ L2 R3).

(*ImpR*)
subst.
rewrite app_comm_cons in I.
destruct (H _ (le_n _) _ _ _ _ _ I) as [b [I1 I2]].
exists (S b).
split.

apply (le_n_S _ _ I1).

rewrite app_comm_cons in *.
apply (LKImpR _ _ _ I2).
Qed.

Lemma inv_ImpL2:
  forall n E F Γ1 Γ2 Δ (D: LK n (Γ1 ++ (E→F) :: Γ2) Δ),
    (exists m, m <= n /\ LK m (Γ1 ++ F :: Γ2) Δ).
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
exists 0.
split.

apply le_n.

inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*Id*)
apply imp_not_var in Ant.
apply in_app_comm in Ant.
apply (in_app_add _ _ [F] ) in Ant.
rewrite app_assoc_reverse in Ant.
apply in_app_comm in Ant.
rewrite app_assoc_reverse in Ant.
apply (LKId _ _ _ Suc Ant).

(*Bot*)
apply imp_not_bot in Fal.
apply in_app_comm in Fal.
apply (in_app_add _ _ [F] ) in Fal.
rewrite app_assoc_reverse in Fal.
apply in_app_comm in Fal.
rewrite app_assoc_reverse in Fal.
apply (LKBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

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
apply (LKImpL _ _ _ L2 R2).

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
rewrite app_assoc in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (Nat.max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite app_assoc_reverse in *.
apply (LKImpL _ _ _ L2 R2).

(*ImpR*)
subst.
rewrite app_comm_cons in I.
destruct (H _ (le_n _) _ _ _ _ _ I) as [b [I1 I2]].
exists (S b).
split.

apply (le_n_S _ _ I1).

apply (LKImpR _ _ _  I2).
Qed.

Lemma inv_ImpR:
  forall n E F Δ1 Δ2 Γ (D : LK n Γ (Δ1++E→F::Δ2)),
   (exists m, m <= n /\ LK m (E::Γ) (Δ1++F::Δ2)).
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
subst.
exists 0.
split.

apply le_n.

inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ID*)
apply imp_not_var in Suc.
apply in_app_comm in Suc.
apply (in_app_add _ _ [F] ) in Suc.
rewrite app_assoc_reverse in Suc.
apply in_app_comm in Suc.
rewrite app_assoc_reverse in Suc.
apply (in_app_add _ _ [E]) in Ant.
rewrite in_app_comm in Ant.
apply (LKId _ _ _ Suc Ant).

(*Bot*)
apply (in_app_add Bot Γ [E]) in Fal.
apply in_app_comm in Fal.
apply (LKBot _ _ Fal).

(*Inductive*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ImpL*)
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ _ _ L) as [c [L1 L2]].
rewrite app_comm_cons in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ _ _ R) as [d [R1 R2]].
exists (S (Nat.max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite app_comm_cons in L2.
apply (LKImpL _ _ _ L2 R2).

(*ImpR*)
subst.
destruct (app_eq_app _ _ _ _ EqA) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
exists n.
split.

apply (le_S _ _ (le_n _)).

assumption.

inversion Z2.
subst.
rewrite app_assoc_reverse in I.
destruct (H _ (le_n _) _ _ _ _ _ I) as [b [I1 I2]].
exists (S b).
split.

apply (le_n_S _ _ I1).

rewrite <- (app_nil_l (E :: A :: Γ)) in I2.
apply exchange_L in I2.
rewrite app_comm_cons in *.
rewrite app_assoc in *.
apply (LKImpR _ _ _ I2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
exists n.
split.

apply (le_S _ _ (le_n _)).

assumption.

inversion Z2.
subst.
rewrite app_comm_cons in I.
rewrite app_assoc in I.
destruct (H _ (le_n _) _ _ _ _ _ I) as [b [I1 I2]].
exists (S b).
split.

apply (le_n_S _ _ I1).

rewrite <- (app_nil_l (E :: A :: Γ)) in I2.
apply exchange_L in I2.
rewrite app_assoc_reverse in *.
apply (LKImpR _ _ _ I2).
Qed.

Theorem contraction:
  forall n X,
    (forall Γ1 Γ2 Γ3 Δ (D : (Γ1 ++ X :: Γ2 ++ X :: Γ3) |- Δ >> n),
       exists m, m <= n /\ LK m (Γ1 ++ X :: Γ2 ++ Γ3 ) Δ) /\
    (forall Δ1 Δ2 Δ3 Γ (D : Γ |- Δ1 ++ X :: Δ2 ++ X :: Δ3 >> n),
       exists m, m <= n /\ LK m Γ (Δ1 ++ X :: Δ2 ++ Δ3)).
Proof.
intros n.
induction n using strong_induction.

(*Base Case*)
intros.
split.

(*Left*)
intros.
exists 0.
split.

apply le_n.

inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*Id*)
subst.
apply in_double in Ant.
apply (LKId A _ _ Suc Ant).

(*Bot*)
subst.
apply in_double in Fal.
apply (LKBot _ _ Fal).

(*Right*)
intros.
exists 0.
split.

apply le_n.

inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*Id*)
apply in_double in Suc.
apply (LKId _ _ _ Suc Ant).

(*Bot*)
apply (LKBot _ _ Fal).

(*Inductive*)
intros.
split.

(*Left*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ImpL*)
subst.
destruct (app_eq_app _ _ _ _ EqS) as [l [ [Z1 Z2] | [Z1 Z2] ]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (inv_ImpL2 _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc_reverse in L2.
destruct (H _ (le_trans L1 (PeanoNat.Nat.le_max_l _ _)) B) as [X1 _].
destruct (X1 _ _ _ _ L2) as [d [L3 L4]].
rewrite app_assoc in R.
destruct (inv_ImpL1 _ _ _ _ R) as [e [R1 R2]].
rewrite app_assoc_reverse in R2.
destruct (H _ (le_trans R1 (PeanoNat.Nat.le_max_r _ _)) A) as [_ Y2].
destruct (Y2 [] [] _ _ R2) as [f [R3 R4]].
exists (S (Nat.max d f)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ (le_trans L3 L1) (le_trans R3 R1))).

apply (LKImpL _ _ _ L4 R4).

inversion Z2 as [[Z3 Z4]].
subst.
assert (Z5 : In p (l ++ A → B :: ΓB)) by apply (in_list_eq Z4).
apply in_app_iff in Z5.
destruct Z5 as [Z5 | [Z5 | Z5]].

destruct (in_split _ _ Z5) as [l1 [l2 Z3]].
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) p) as [X1 _].
rewrite app_assoc_reverse in L.
rewrite app_comm_cons in L.
rewrite app_assoc_reverse in L.
destruct (X1 _ _ _ _ L) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) p) as [Y1 _].
rewrite app_assoc_reverse in R.
rewrite app_comm_cons in R.
rewrite app_assoc_reverse in R.
destruct (Y1 _ _ _ _ R) as [d [R1 R2]].
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
apply (LKImpL _ _ _ L2 R2).

subst.
rewrite app_assoc_reverse in L.
destruct (inv_ImpL2 _ _ _ _ L) as [c [L1 L2]].
destruct (H _ (le_trans L1 (PeanoNat.Nat.le_max_l _ _)) B) as [X1 _].
destruct (X1 _ _ _ _ L2) as [d [L3 L4]].
rewrite app_assoc_reverse in R.
destruct (inv_ImpL1 _ _ _ _ R) as [e [R1 R2]].
destruct (H _ (le_trans R1 (PeanoNat.Nat.le_max_r _ _)) A) as [_ Y2].
destruct (Y2 [] [] _ _ R2) as [f [R3 R4]].
exists (S (Nat.max d f)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ (le_trans L3 L1) (le_trans R3 R1))).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L in L4.
rewrite app_assoc in *.
apply (LKImpL _ _ _ L4 R4).

destruct (in_split _ _ Z5) as [l1 [l2 Z1]].
subst.
rewrite app_assoc_reverse in L.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) p) as [X1 _].
rewrite app_comm_cons in L.
rewrite (app_assoc (p :: l)) in L.
destruct (X1 _ _ _ _ L) as [c [L1 L2]].
rewrite app_assoc_reverse in R.
rewrite <- app_comm_cons in R.
rewrite app_assoc in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) p) as [Y1 _].
destruct (Y1 _ _ _ _ R) as [d [R1 R2]].
exists (S (Nat.max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite cons_single_app.
apply swap_L.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_L in L2.
apply move_R_L in R2.
rewrite app_assoc_reverse in *.
rewrite app_assoc in *.
apply (LKImpL _ _ _ L2 R2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (inv_ImpL2 _ _ _ _ L) as [c [L1 L2]].
destruct (H _ ((le_trans L1 (PeanoNat.Nat.le_max_l _ _))) B) as [X1 _].
rewrite app_assoc_reverse in L2.
destruct (X1 _ _ _ _ L2) as [d [L3 L4]].
rewrite app_assoc in R.
destruct (inv_ImpL1 _ _ _ _ R) as [e [R1 R2]].
destruct (H _ (le_trans R1 (PeanoNat.Nat.le_max_r _ _)) A) as [_ Y2].
destruct (Y2 [] [] _ _ R2) as [f [R3 R4]].
exists (S (Nat.max d f)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ (le_trans L3 L1) (le_trans R3 R1))).

rewrite app_assoc_reverse in R4.
apply (LKImpL _ _ _ L4 R4).

inversion Z2.
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) X) as [X1 _].
rewrite app_comm_cons in L.
rewrite app_assoc in L.
destruct (X1 _ _ _ _ L) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) X) as [Y1 _].
rewrite app_assoc in R.
destruct (Y1 _ _ _ _ R) as [d [R1 R2]].
exists (S (Nat.max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

rewrite app_assoc_reverse in L2.
rewrite app_assoc_reverse in R2.
rewrite app_assoc_reverse.
apply (LKImpL _ _ _ L2 R2).

(*ImpR*)
subst.
destruct (H _ (le_n _) X) as [X1 _].
rewrite app_comm_cons in I.
destruct (X1 _ _ _ _ I) as [b [I1 I2]].
exists (S b).
split.

apply (le_n_S _ _ I1).

apply (LKImpR _ _ _ I2).

(*Right*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ImpL*)
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) X) as [_ X2].
destruct (X2 _ _ _ _ L) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_r _ _) X) as [_ Y2].
rewrite app_comm_cons in R.
destruct (Y2 _ _ _ _ R) as [d [R1 R2]].
exists (S (Nat.max c d)).
split.

apply (le_n_S _ _ (PeanoNat.Nat.max_le_compat _ _ _ _ L1 R1)).

apply (LKImpL _ _ _ L2 R2).

(*ImpR*)
subst.
destruct (app_eq_app _ _ _ _ EqA) as [l [[Z1 Z2] | [Z1 Z2]]].

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
rewrite app_comm_cons in I.
rewrite app_assoc in I.
destruct (inv_ImpR _ _ _ _ I) as [b [I1 I2]].
destruct (H _ I1 A) as [X1 _].
destruct (X1 [] [] _ _ I2) as [c [I3 I4]].
destruct (H _ (le_trans I3 I1) B) as [_ Y2].
rewrite app_assoc_reverse in I4.
destruct (Y2 _ _ _ _ I4) as [d [I5 I6]].
exists (S d).
split.

apply (le_n_S _ _ (le_trans I5 (le_trans I3 I1))).

apply (LKImpR _ _ _ I6).

inversion Z2 as [[Z3 Z4]].
subst.
assert (Z5 : In p (l ++ A → B :: ΔB)) by apply (in_list_eq Z4).
apply in_app_iff in Z5.
destruct Z5 as [Z5 | [Z5 |Z5]].

destruct (in_split _ _ Z5) as [l1 [l2 Z6]].
subst.
rewrite app_assoc_reverse in I.
rewrite <- app_comm_cons in I.
rewrite app_assoc_reverse in I.
destruct (H _ (le_n _) p) as [_ X2].
destruct (X2 _ _ _ _ I) as [b [I1 I2]].
exists (S b).
split.

apply (le_n_S _ _ I1).

rewrite cons_single_app.
apply swap_R.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_R in I2.
rewrite app_comm_cons in I2.
rewrite! app_assoc in *.
apply (LKImpR _ _ _ I2).

subst.
rewrite app_assoc_reverse in I.
destruct (inv_ImpR _ _ _ _ I) as [b [I1 I2]].
destruct (H _ I1 A) as [X1 _].
destruct (X1 [] [] _ _ I2) as [c [I3 I4]].
destruct (H _ (le_trans I3 I1) B) as [_ Y2].
destruct (Y2 _ _ _ _ I4) as [d [I5 I6]].
exists (S d).
split.

apply (le_n_S _ _ (le_trans I5 (le_trans I3 I1))).

rewrite cons_single_app.
apply swap_R.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_R in I6.
rewrite app_assoc in *.
apply (LKImpR _ _ _ I6).

destruct (in_split _ _ Z5) as [l1 [l2 Z3]].
subst.
destruct (H _ (le_n _) p) as [_ X2].
rewrite app_assoc_reverse in I.
rewrite app_comm_cons in I.
rewrite <- app_comm_cons in I.
rewrite app_assoc in I.
destruct (X2 _ _ _ _ I) as [b [I1 I2]].
exists (S b).
split.

apply (le_n_S _ _ I1).

rewrite cons_single_app.
apply swap_R.
rewrite <- cons_single_app.
rewrite Z4.
apply move_R_R in I2.
rewrite app_assoc_reverse in I2.
rewrite app_assoc in *.
apply (LKImpR _ _ _ I2).

destruct l.

rewrite app_nil_r in Z1.
inversion Z2.
subst.
rewrite app_comm_cons in I.
rewrite app_assoc in I.
destruct (inv_ImpR _ _ _ _ I) as [b [I1 I2]].
destruct (H _ I1 A) as [X1 _].
destruct (X1 [] [] _ _ I2) as [c [I3 I4]].
destruct (H _ (le_trans I3 I1) B) as [_ Y2].
rewrite app_assoc_reverse in I4.
destruct (Y2 _ _ _ _ I4) as [d [I5 I6]].
exists (S d).
split.

apply (le_n_S _ _ (le_trans I5 (le_trans I3 I1))).

apply (LKImpR _ _ _ I6).

inversion Z2.
subst.
destruct (H _ (le_n _) X) as [_ X2].
rewrite app_comm_cons in I.
rewrite app_assoc in I.
destruct (X2 _ _ _ _ I) as [b [ I1 I2]].
exists (S b).
split.

apply (le_n_S _ _ I1).

rewrite app_assoc_reverse in I2.
rewrite app_assoc_reverse.
apply (LKImpR _ _ _ I2).
Qed.

(*Case Bashing Belonging in Multiple Lists with Known First Value*)
(*Used for Id Case in Cut When Avoiding Contraction*)

Lemma cut_gax:
  forall (A A0 A1 : PropF) (L1 L2 : list PropF),
       In A0 L1 -> In A0 ([A] ++ L2)
    -> In A1 L2 -> In A1 ([A] ++ L1)
    -> In A0 L1 /\ In A0 L2 \/ In A1 L1 /\ In A1 L2.
Proof.
intros.
destruct H0.

destruct H2.

subst.
firstorder.

firstorder.

firstorder.
Qed.


Theorem cut_elimination_no_contraction:
  forall A n m Γ Δ (D : LK n Γ ([A] ++ Δ)) (D1 : LK m ([A] ++ Γ) Δ),
    exists k, Γ |- Δ >> k.
Proof.
intros A.
induction A.

(*PropVar*)
intros n.
induction n using strong_induction.

(*Base Case n*)
intros m.
induction m using strong_induction.

(*Base Case m : n = 0*)
intros.
subst.
exists 0.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*Id*)
subst.
inversion D1 as [ DA DΓT DΔT DSuc DAnt DHeight DEqS DEqA | DΓT DΔT DFal DEqS DEqA | Da Db DA DB DΓA DΓB DΔT DL DR DHeight DEqS DEqA | Da DA DB DΓT DΔA DΔB DI DHeight DEqS DEqA].


(*Id : Id*)
destruct (cut_gax Ant Suc DSuc DAnt) as [[Ant1 Suc1] | [Ant1 Suc1]].

apply (LKId _ _ _ Suc1 Ant1).

apply (LKId _ _ _ Suc1 Ant1).

(*Id : Bot*)
destruct Suc as [Suc | Suc].

destruct DFal as [DFal | DFal].

discriminate.

apply (LKBot _ _ DFal).

apply (LKId _ _ _ Suc Ant).

(*Bot*)
apply (LKBot _ _ Fal).

(*Inductive m : n = 0*)
intros.
subst.
inversion D1 as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ImpL*)
subst.
destruct ΓA.

inversion EqS.

inversion EqS.
subst.
destruct (inv_ImpL2 _ _ _ _ D) as [c [L1 L2]].
inversion L1.
subst.
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ L2 L) as [c L3].
destruct (inv_ImpL1 _ _ _ _ D) as [d [R1 R2]].
inversion R1.
subst.
rewrite cons_single_app in R2.
rewrite <- app_nil_l in R2.
apply swap_R in R2.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ R2 R) as [d R3].
exists (S (max c d)).
apply (LKImpL _ _ _ L3 R3).

(*ImpR*)
subst.
rewrite app_assoc in D.
destruct (inv_ImpR _ _ _ _ D) as [b [I1 I2]].
inversion I1.
subst.
rewrite cons_single_app in I.
rewrite <- (app_nil_l ( [A] ++ [# p] ++ Γ)) in I.
apply swap_L in I.
destruct (H _ (le_n _) _ _ I2 I) as [c I3].
exists (S c).
apply (LKImpR _ _ _ I3).

(*Inductive n*)
intros.
subst.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ImpL*)
subst.
rewrite app_assoc in D1.
destruct (inv_ImpL2 _ _ _ _ D1) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L L2) as [d L3].
destruct (inv_ImpL1 _ _ _ _ D1) as [e [R1 R2]].
rewrite cons_single_app in R.
rewrite <- app_nil_l in R.
apply swap_R in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R R2) as [f R3].
exists (S (max d f)).
apply (LKImpL _ _ _ L3 R3).

(*ImpR*)
destruct ΔA.

inversion EqA.

inversion EqA.
subst.
destruct (inv_ImpR _ _ _ _ D1) as [b [I1 I2]].
rewrite cons_single_app in I2.
rewrite <- (app_nil_l ( [A] ++ [# p] ++ Γ)) in I2.
apply swap_L in I2.
destruct (H _ (le_n _) _ _ _ I I2) as [c I3].
exists (S c).
apply (LKImpR _ _ _ I3).

(*Bot*)
intros n.
induction n using strong_induction.

(*Base Case n*)
intros.
subst.
exists 0.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*Id*)
destruct Suc as [Suc | Suc].

inversion Suc.

apply (LKId _ _ _ Suc Ant).

(*Bot*)
apply (LKBot _ _ Fal).

(*Inductive n*)
intros.
subst.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ImpL*)
subst.
rewrite app_assoc in D1.
destruct (inv_ImpL2 _ _ _ _ D1) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L L2) as [d L3].
destruct (inv_ImpL1 _ _ _ _ D1) as [e [R1 R2]].
rewrite <- app_nil_l in R.
apply exchange_R in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R R2) as [f R3].
exists (S (max d f)).
apply (LKImpL _ _ _ L3 R3).

(*ImpR*)
destruct ΔA.

inversion EqA.

inversion EqA.
subst.
destruct (inv_ImpR _ _ _ _ D1) as [b [I1 I2]].
rewrite <- (app_nil_l ( A :: [Bot] ++ Γ)) in I2.
apply exchange_L in I2.
destruct (H _ (le_n _) _ _ _ I I2) as [c I3].
exists (S c).
apply (LKImpR _ _ _ I3).

(*Imp*)
intros.
subst.
destruct (inv_ImpR _ _ [] _ D) as [a [I1 I2]].
destruct (inv_ImpL1 _ _ [] _ D1) as [b [I3 I4]].
rewrite cons_single_app in I4.
pose (weakening_R _ _ I4 [A2]) as I5.
destruct (IHA1  _ _ _ _ I5 I2) as [c I6].
destruct (inv_ImpL2 _ _ [] _ D1) as [d [I7 I8]].
destruct (IHA2 _ _ _ _ I6 I8) as [e I9].
exists e.
assumption.
Qed.

Theorem cut_elimination_with_contraction:
  forall A n m Γ Δ (D : LK n Γ ([A] ++ Δ)) (D1 : LK m ([A] ++ Γ) Δ),
    exists k, Γ |- Δ >> k.
Proof.
intros A.
induction A.

(*PropVar*)
intros n.
induction n using strong_induction.

(*Base Case n*)
intros.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*Id*)
destruct Suc as [Suc | Suc].

subst.
rewrite <- Suc in Ant.
destruct (in_split _ _ Ant) as [l1 [l2 Z1]].
subst.
destruct (contraction m #p) as [X1 _].
destruct (X1 [] _ _ _ D1) as [a [I1 I2]].
apply move_R_L in I2.
exists a.
assumption.

exists 0.
apply (LKId _ _ _ Suc Ant).

(*Bot*)
exists 0.
apply (LKBot _ _ Fal).

(*Inductive n*)
intros.
subst.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ImpL*)
subst.
rewrite app_assoc in D1.
destruct (inv_ImpL2 _ _ _ _ D1) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L L2) as [d L3].
destruct (inv_ImpL1 _ _ _ _ D1) as [e [R1 R2]].
rewrite cons_single_app in R.
rewrite <- app_nil_l in R.
apply swap_R in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R R2) as [f R3].
exists (S (max d f)).
apply (LKImpL _ _ _ L3 R3).

(*ImpR*)
destruct ΔA.

inversion EqA.

inversion EqA.
subst.
destruct (inv_ImpR _ _ _ _ D1) as [b [I1 I2]].
rewrite cons_single_app in I2.
rewrite <- (app_nil_l ( [A] ++ [# p] ++ Γ)) in I2.
apply swap_L in I2.
destruct (H _ (le_n _) _ _ _ I I2) as [c I3].
exists (S c).
apply (LKImpR _ _ _ I3).

(*Bot*)
intros n.
induction n using strong_induction.

(*Base Case n*)
intros.
subst.
exists 0.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*Id*)
destruct Suc as [Suc | Suc].

inversion Suc.

apply (LKId _ _ _ Suc Ant).

(*Bot*)
apply (LKBot _ _ Fal).

(*Inductive n*)
intros.
subst.
inversion D as [ A ΓT ΔT Suc Ant Height EqS EqA | ΓT ΔT Fal EqS EqA | a b A B ΓA ΓB ΔT L R Height EqS EqA | a A B ΓT ΔA ΔB I Height EqS EqA].

(*ImpL*)
subst.
rewrite app_assoc in D1.
destruct (inv_ImpL2 _ _ _ _ D1) as [c [L1 L2]].
destruct (H _ (PeanoNat.Nat.le_max_l _ _) _ _ _ L L2) as [d L3].
destruct (inv_ImpL1 _ _ _ _ D1) as [e [R1 R2]].
rewrite <- app_nil_l in R.
apply exchange_R in R.
destruct (H _ (PeanoNat.Nat.le_max_r _ _) _ _ _ R R2) as [f R3].
exists (S (max d f)).
apply (LKImpL _ _ _ L3 R3).

(*ImpR*)
destruct ΔA.

inversion EqA.

inversion EqA.
subst.
destruct (inv_ImpR _ _ _ _ D1) as [b [I1 I2]].
rewrite <- (app_nil_l ( A :: [Bot] ++ Γ)) in I2.
apply exchange_L in I2.
destruct (H _ (le_n _) _ _ _ I I2) as [c I3].
exists (S c).
apply (LKImpR _ _ _ I3).

(*Imp*)
intros.
subst.
destruct (inv_ImpR _ _ [] _ D) as [a [I1 I2]].
destruct (inv_ImpL1 _ _ [] _ D1) as [b [I3 I4]].
rewrite cons_single_app in I4.
pose (weakening_R _ _ I4 [A2]) as I5.
destruct (IHA1  _ _ _ _ I5 I2) as [c I6].
destruct (inv_ImpL2 _ _ [] _ D1) as [d [I7 I8]].
destruct (IHA2 _ _ _ _ I6 I8) as [e I9].
exists e.
assumption.
Qed.