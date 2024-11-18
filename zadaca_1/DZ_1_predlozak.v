Set Implicit Arguments.
Require Import List.
Import ListNotations.
(*Require Import Omega.*)
Require Import Coq.Bool.Bool.
Require Import Lia.
(*ZADATAK 1.*)
Theorem zad1_bool_a :
  forall X Y : bool, 
    (andb X (negb Y)) || (andb (negb X) (negb Y)) || (andb (negb X) Y) = negb (andb X Y).
Proof.
  intros X Y.
  destruct X, Y; simpl; reflexivity.
Qed.


Theorem zad1_bool_b:
  forall X Y Z : bool,
    negb (negb X && Y && Z) && negb(X && Y && negb Z) && (X && negb Y && Z) = X && negb Y && Z.
Proof.
  intros X Y Z.
  destruct X, Y, Z; simpl; reflexivity.
Qed.


(* Bit *)

Inductive B : Type :=
  | O : B
  | I : B.

Definition And (x y : B) : B :=
match x with
  | O => O
  | I => y
end.

Definition Or (x y : B) : B :=
match x with
  | O => y
  | I => I
end.

Definition Not (x : B) : B :=
match x with
  | O => I
  | I => O
end.

Definition Add (x y c : B) : B :=
match x, y with
  | O, O => c
  | I, I => c
  | _, _ => Not c
end.

Definition Rem (x y c : B) : B :=
match x, y with
  | O, O => O
  | I, I => I
  | _, _ => c
end.

(* List *)

Fixpoint AndL (x y : list B) : list B :=
match x, y with
| [], _ => []
| _, [] => []
| x :: xs, y :: ys => And x y :: AndL xs ys
end.

Fixpoint OrL (x y : list B) : list B :=
match x, y with
| [], _ => []
| _, [] => []
| x :: xs, y :: ys => Or x y :: OrL xs ys
end.

Fixpoint NotL (x : list B) : list B :=
match x with
  | [] => []
  | x :: xs => Not x :: NotL xs
end.

Fixpoint AddLr (x y : list B) (c : B) : list B :=
match x, y with
| [], _ => []
| _, [] => []
| x :: xs, y :: ys => Add x y c :: AddLr xs ys (Rem x y c)
end.

Definition AddL (x y : list B) : list B := rev (AddLr (rev x) (rev y) O).

Fixpoint IncLr (x : list B) (c : B) : list B :=
match x with
| [] => []
| x :: xs => Add x I c :: IncLr xs (Rem x I c)
end.

Definition IncL (x : list B) : list B := rev (IncLr (rev x) O).

(* ALU *)

Definition flag_zx (f : B) (x : list B) : list B :=
match f with
| I => repeat O (length x)
| O => x
end.

Definition flag_nx (f : B) (x : list B) : list B :=
match f with
| I => NotL x
| O => x
end.

Definition flag_f (f : B) (x y : list B) : list B :=
match f with
| I => AddL x y
| O => AndL x y
end.

Definition ALU (x y : list B) (zx nx zy ny f no : B) : list B := 
  flag_nx no (flag_f f (flag_nx nx (flag_zx zx x)) (flag_nx ny (flag_zx zy y))).

(* Teoremi *)

Lemma ALU_zero (x y : list B) :
  length x = length y -> ALU x y I O I O I O = repeat O (length x).
Proof. Abort.

Lemma ALU_minus_one (x y : list B) : 
  length x = length y -> ALU x y I I I O I O = repeat I (length x).
Proof. Abort.

Lemma ALU_x (x y : list B) : 
  length x = length y -> ALU x y O O I I O O = x.
Proof. Abort.

Lemma ALU_y (x y : list B) : 
  length x = length y -> ALU x y I I O O O O = y.
Proof. Abort.

Lemma ALU_Not_x (x y : list B) : 
  length x = length y -> ALU x y O O I I O I = NotL x.
Proof. Abort.

Lemma ALU_Not_y (x y : list B) : 
  length x = length y -> ALU x y I I O O O I = NotL y.
Proof. Abort.

Lemma ALU_Add (x y : list B) : 
  length x = length y -> ALU x y O O O O I O = AddL x y.
Proof. Abort.

Lemma ALU_And (x y : list B) : 
  length x = length y -> ALU x y O O O O O O = AndL x y.
Proof. Admitted.

Lemma ALU_Or (x y : list B) : 
  length x = length y -> ALU x y O I O I O I = OrL x y.
Proof. Admitted.

(*Lemma ALU_One (n : nat) (x y : list B) :
  length x = n /\ length y = n /\ n <> 0 -> ALU x y I I I I I I = repeat O (pred n) ++ [I].
Proof.
  intros H. destruct H. destruct H0.
   simpl. rewrite H. rewrite H0. simpl.
  assert(pomoc1: forall k, NotL (repeat O k) = repeat I k).
  {
    induction k. 
    - simpl. reflexivity.
    - simpl. rewrite IHk. reflexivity.
  }
  assert(pomoc2: forall k, rev (repeat I k) = repeat I k). {
      induction k.
      - simpl. reflexivity.
      - simpl. rewrite IHk.
      assert(pomoc_za_pomoc: forall kk, repeat I kk ++ [I] = I :: repeat I kk). {
         induction kk.
         - simpl. reflexivity.
         - simpl. rewrite IHkk. reflexivity.
      }
      rewrite pomoc_za_pomoc. reflexivity.
      
  }
  assert(pomoc3: forall k, (AddLr (repeat I k ++ [I]) (repeat I k ++ [I]) O) =). {
   }
  
  induction n,x,y.
  - simpl. destruct H1. reflexivity.
  - simpl. destruct H1. reflexivity.
  - simpl. destruct H1. reflexivity.
  - simpl. destruct H1. reflexivity.
  - rewrite <- H. simpl. rewrite H in IHn. simpl in H. 
    exfalso. apply H1. rewrite H. reflexivity. 
  - destruct H1. simpl in H. rewrite H. reflexivity.
  - destruct H1. simpl in H0. rewrite H0. reflexivity.
  - simpl. simpl in IHn. simpl in H. simpl in H0. rewrite pomoc1. rewrite pomoc1 in IHn.
    unfold AddL. simpl. rewrite pomoc2. unfold AddL in IHn. simpl in IHn. rewrite pomoc2 in IHn.
Abort.*)
Lemma ALU_One (n : nat) (x y : list B) :
  length x = n /\ length y = n /\ n <> 0 -> ALU x y I I I I I I = repeat O (pred n) ++ [I].
Proof.
  intros H. destruct H. destruct H0.
   simpl. rewrite H. rewrite H0. simpl.
  assert(pomoc1: forall k, NotL (repeat O k) = repeat I k).
  {
    induction k. 
    - simpl. reflexivity.
    - simpl. rewrite IHk. reflexivity.
  }
  assert(pomoc2: forall k, rev (repeat I k) = repeat I k). {
      induction k.
      - simpl. reflexivity.
      - simpl. rewrite IHk.
      assert(pomoc_za_pomoc: forall kk, repeat I kk ++ [I] = I :: repeat I kk). {
         induction kk.
         - simpl. reflexivity.
         - simpl. rewrite IHkk. reflexivity.
      }
      rewrite pomoc_za_pomoc. reflexivity.
  }
  assert(pomoc3: forall k,k<>0 -> AddLr (repeat I k) (repeat I k) O = O :: repeat I (Nat.pred k)). {
    intros.
    induction k.
    - simpl. destruct H2. reflexivity.
    - simpl. f_equal. simpl in IHk.
    (*-- reflexivity.
    -- simpl. f_equal. rewrite IHk0.
    --- reflexivity.
    --- simpl. intros s. apply H2. rewrite s. discriminate.
    --- intros. des*)
    assert (forall kk,AddLr (repeat I kk) (repeat I kk) I = repeat I kk).
    {
       induction kk.
       - simpl. reflexivity.
       - simpl. f_equal. rewrite IHkk. reflexivity.
    }
    apply H3.
  }
  assert(pomoc4: forall k,  NotL (repeat I k ++ [O]) = repeat O k ++ [I]). {
    simpl. intros. induction k.
    - simpl. reflexivity.
    - simpl. f_equal. rewrite IHk.
    --  reflexivity.
    }
  rewrite pomoc1. unfold AddL. rewrite pomoc2. rewrite pomoc3.
  - simpl. rewrite pomoc2. destruct n.
  -- simpl. reflexivity.
  -- simpl. rewrite pomoc4. reflexivity. 
  - intros d. apply H1. apply d.
Qed.






























