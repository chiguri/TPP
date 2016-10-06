(*
TPPmark 2016

Written by Sosuke Moriguchi, Kwansei Gakuin University
*)

Require Import List.
Import ListNotations.
Require Import Omega.

(* From depndent type spec *)
Module Dependent.

(* 依存型の取り方は、listの長さから自然数を制限するか、自然数からlistの長さを制限するか、の二つがある。どちらでも、destructで展開するとほぼ同じになる。 *)

(* 今回はlistを先に取り、自然数に制約を与える *)


Section nth.

Context {A : Type}.

Definition nth_d : forall l : list A, {n : nat | n < length l} -> A.
(* 再帰は非依存型で行う *)
fix 1.
intro l; destruct l as [| a l']; simpl; intro x; destruct x as [x H].
 elimtype False; omega.
 destruct x.
  exact a.
  apply nth_d with l'.
   econstructor.
    apply lt_S_n in H.
     exact H.
Defined.


Lemma nth_d_eq : forall (l : list A) (x x' : {n : nat | n < length l}),
 proj1_sig x = proj1_sig x' -> nth_d l x = nth_d l x'.
induction l; intros x x' He; destruct x as [x H]; destruct x' as [x' H'].
 simpl in H; omega.
 simpl in *; subst.
  destruct x'.
   now auto.
   apply IHl; simpl; now auto.
Qed.


End nth.

Extraction nth_d.



Section replace.

Context {A : Type}.

(* 返し値に条件を書くと長くなるため、またそれを慌てて作る理由もないため一度普通の関数として作る。条件を示せば最後に合成するのは簡単。 *)
Definition replace_d : forall (l : list A), A -> {n : nat | n < length l} -> list A.
fix 1.
intros l a; destruct l as [| a' l']; simpl; intro x; destruct x as [x H].
 elimtype False; omega.
 destruct x.
  exact (a :: l').
  refine (cons a' _).
   apply replace_d with l'.
    exact a.
    econstructor.
     apply lt_S_n in H.
      exact H.
Defined.


Lemma replace_d_length_eq :
 forall (l : list A) (a : A) (x : {n : nat | n < length l}),
  length l = length (replace_d l a x).
induction l as [| a' l' IHl]; intros a x; destruct x as [x H].
 simpl in H; omega.
 destruct x.
  simpl; now auto.
  simpl.
   f_equal; now auto.
Qed.



Lemma replace_d_nth :
 forall (l : list A) (a : A) (x : {n : nat | n < length l}) (x' : {n : nat | n < length (replace_d l a x)}),
  proj1_sig x = proj1_sig x' -> nth_d (replace_d l a x) x' = a.
induction l as [| a' l' IHl]; intros a x x' He; destruct x as [x H]; destruct x' as [x' H']; simpl in He.
 simpl in H; omega.
 destruct x.
  subst; simpl; now auto.
  destruct x'.
   now inversion He.
   inversion He; subst.
    simpl.
     simpl in H; simpl in H'.
      apply IHl.
       simpl; now auto.
Qed.


Definition replace_d_nat_translate :
 forall (l : list A) (a : A) (x : {n : nat | n < length l}),
  {m : nat | m < length l} -> {m : nat | m < length (replace_d l a x)}.
intros l a x x'; destruct x as [x H]; destruct x' as [x' H'].
 rewrite (replace_d_length_eq l a (exist _ x H)) in H'.
  econstructor.
   exact H'.
Defined.


Lemma replace_d_nat_translate_proj_eq :
 forall (l : list A) (a : A) (x : {n : nat | n < length l}) (x' : {m : nat | m < length l}),
   proj1_sig x' = proj1_sig (replace_d_nat_translate l a x x').
unfold replace_d_nat_translate; intros l a x x'; destruct x; destruct x'; simpl; now auto.
Qed.


Lemma replace_d_nth_exists :
 forall (l : list A) (a : A) (x : {n : nat | n < length l}),
  exists x' : {n : nat | n < length (replace_d l a x)}, proj1_sig x = proj1_sig x' /\ nth_d (replace_d l a x) x' = a.
intros l a x.
 exists (replace_d_nat_translate l a x x); split.
  now apply replace_d_nat_translate_proj_eq.
  apply replace_d_nth.
   now apply replace_d_nat_translate_proj_eq.
Qed.


Lemma replace_d_nth_not :
 forall (l : list A) (a : A) (x : {n : nat | n < length l}) (x' : {n : nat | n < length l}) (x'' : {n : nat | n < length (replace_d l a x)}),
  proj1_sig x <> proj1_sig x' ->
   proj1_sig x' = proj1_sig x'' -> nth_d l x' = nth_d (replace_d l a x) x''.
induction l as [| a' l' IHl]; intros a x x' x'' Hne He; destruct x as [x H]; destruct x' as [x' H']; destruct x'' as [x'' H'']; simpl in He, Hne.
 simpl in H; omega.
 subst; destruct x.
  destruct x''.
   elim Hne; now auto.
   simpl.
    apply nth_d_eq; simpl; now auto.
  destruct x''.
   simpl; now auto.
   simpl.
    eapply IHl.
     simpl; intro.
      apply Hne; subst; now auto.
     simpl; now auto.
Qed.


Lemma replace_d_nth_not_exists :
 forall (l : list A) (a : A) (x : {n : nat | n < length l}) (x' : {n : nat | n < length l}),
  proj1_sig x <> proj1_sig x' ->
   exists x'' : {n : nat | n < length (replace_d l a x)}, proj1_sig x' = proj1_sig x'' /\ nth_d l x' = nth_d (replace_d l a x) x''.
intros l a x x' Hne.
 exists (replace_d_nat_translate l a x x').
  split.
   now apply replace_d_nat_translate_proj_eq.
   apply replace_d_nth_not.
    now auto.
    now apply replace_d_nat_translate_proj_eq.
Qed.


(* 結果の合成 *)
Definition replace_d' (l : list A) (a : A) (x : {n : nat | n < length l})
 : {l' : list A |
     length l = length l'
     /\ forall (x' : {n : nat | n < length l}) (x'' : {n : nat | n < length l'}),
         proj1_sig x' = proj1_sig x''
         -> (proj1_sig x = proj1_sig x' -> nth_d l' x'' = a)
            /\ (proj1_sig x <> proj1_sig x' -> nth_d l x' = nth_d l' x'')}.
refine (existT _ (replace_d l a x) _).
 split.
  apply replace_d_length_eq.
  intros x' x'' He; split; intro Hp.
   apply replace_d_nth.
    rewrite Hp; now auto.
   apply replace_d_nth_not; now auto.
Defined.


End replace.

Extraction replace_d.
Extraction replace_d_nat_translate.
Recursive Extraction replace_d'. (* インライン展開とパターンマッチ展開するとreplace_dを呼ぶだけになる。 *)



Section remove.

Context {A : Type}.

Definition remove_d : forall (l : list A), {n : nat | n < length l} -> list A.
fix 1.
intro l; destruct l as [| a' l']; simpl; intro x; destruct x as [x H].
 elimtype False; omega.
 destruct x.
  exact l'.
  refine (cons a' _).
   apply remove_d with l'.
    econstructor.
     apply lt_S_n in H.
      exact H.
Defined.


Lemma remove_d_length_S_eq :
 forall (l : list A) (x : {n : nat | n < length l}),
  length l = S (length (remove_d l x)).
induction l as [| a' l' IHl]; intro x; destruct x as [x H].
 simpl in H; omega.
 destruct x.
  simpl; now auto.
  simpl.
   f_equal; now auto.
Qed.



Lemma remove_d_nth_lt :
 forall (l : list A) (x x' : {n : nat | n < length l}) (x'' : {n : nat | n < length (remove_d l x)}),
  proj1_sig x > proj1_sig x'' -> proj1_sig x' = proj1_sig x'' -> nth_d l x' = nth_d (remove_d l x) x''.
induction l as [| a' l' IHl]; intros x x' x'' Hgt He; destruct x as [x H]; destruct x' as [x' H']; destruct x'' as [x'' H'']; simpl in He; subst.
 simpl in H; omega.
 destruct x.
  simpl in Hgt; omega.
  destruct x''.
   simpl; now auto.
   simpl in *.
    apply IHl.
     simpl; apply gt_S_n; now auto.
     simpl; now auto.
Qed.


(* translateやexistsは示せない（長さ1のリストから要素を削除すると、n < 0となるnがないため）。細かな情報を付けてもいいが、それ自体はあまりいらないので放置。 *)
(* 問題はgeの場合でltだけなら示せるが *)
(*
Definition remove_d_nat_translate (l : list A) (x x' : {n : nat | n < length l}) : {n : nat | n < length (remove_d l x)}.
destruct x as [x H]; destruct x' as [x' H']; destruct le_gt_dec with x x'.
*)


Lemma remove_d_nth_ge :
 forall (l : list A) (x : {n : nat | n < length l}) (x' : {n : nat | n < length l}) (x'' : {n : nat | n < length (remove_d l x)}),
  proj1_sig x <= proj1_sig x'' ->
   proj1_sig x' = S (proj1_sig x'') -> nth_d l x' = nth_d (remove_d l x) x''.
induction l as [| a' l' IHl]; intros x x' x'' Hle He; destruct x as [x H]; destruct x' as [x' H']; destruct x'' as [x'' H'']; simpl in He; subst.
 simpl in H; omega.
 destruct x.
  destruct x''; simpl; apply nth_d_eq; simpl; now auto.
  destruct x''; simpl; simpl in Hle.
   omega.
   apply IHl; simpl.
    apply le_S_n; now auto.
    now auto.
Qed.


Definition remove_d' (l : list A) (x : {n : nat | n < length l})
 : {l' : list A |
     length l = S (length l')
     /\ forall (x' : {n : nat | n < length l}) (x'' : {n : nat | n < length l'}),
         (proj1_sig x > proj1_sig x'' -> proj1_sig x' = proj1_sig x'' -> nth_d l x' = nth_d l' x'')
         /\ (proj1_sig x <= proj1_sig x'' -> proj1_sig x' = S (proj1_sig x'') -> nth_d l x' = nth_d l' x'')}.
refine (existT _ (remove_d l x) _).
 split.
  apply remove_d_length_S_eq.
  intros x' x''; split; intros Hc He.
   apply remove_d_nth_lt; now auto.
   apply remove_d_nth_ge; now auto.
Defined.


End remove.

Extraction remove_d.
Recursive Extraction remove_d'.


Section dep.

Context {A : Type}.

Definition remove_lst (lst : list (list A)) (i : {n : nat | n < length lst}) (j : {n : nat | n < length (nth_d lst i)}) : list (list A) :=
 replace_d lst (remove_d (nth_d lst i) j) i.


Theorem remove_lst_i :
 forall (lst : list (list A)) (i : {n : nat | n < length lst}) (j : {n : nat | n < length (nth_d lst i)}),
  exists i' : {n : nat | n < length (remove_lst lst i j)}, proj1_sig i = proj1_sig i' /\ length (nth_d lst i) = S (length (nth_d (remove_lst lst i j) i')).
unfold remove_lst.
 intros lst i j.
  exists (replace_d_nat_translate lst (remove_d (nth_d lst i) j) i i).
   split.
    now apply replace_d_nat_translate_proj_eq.
    rewrite replace_d_nth.
     now apply remove_d_length_S_eq.
     now apply replace_d_nat_translate_proj_eq.
Qed.


Theorem remove_lst_i' :
 forall (lst : list (list A)) (i : {n : nat | n < length lst}) (j : {n : nat | n < length (nth_d lst i)}) (i' : {n : nat | n < length lst}),
  proj1_sig i <> proj1_sig i'
  -> exists i'' : {n : nat | n < length (remove_lst lst i j)}, proj1_sig i' = proj1_sig i'' /\ nth_d lst i' = nth_d (remove_lst lst i j) i''.
unfold remove_lst.
 intros lst i j i' Hne.
  exists (replace_d_nat_translate lst (remove_d (nth_d lst i) j) i i').
   split.
    now apply replace_d_nat_translate_proj_eq.
    apply replace_d_nth_not.
     now auto.
     now apply replace_d_nat_translate_proj_eq.
Qed.


Definition remove_lst' (lst : list (list A)) (i : {n : nat | n < length lst}) (j : {n : nat | n < length (nth_d lst i)})
 : {lst' : list (list A) |
     (exists i' : {n : nat | n < length lst'},
       proj1_sig i = proj1_sig i' /\ length (nth_d lst i) = S (length (nth_d lst' i')))
     /\ forall i' : {n : nat | n < length lst},
         proj1_sig i <> proj1_sig i' ->
          exists i'' : {n : nat | n < length lst'},
           proj1_sig i' = proj1_sig i'' /\ nth_d lst i' = nth_d lst' i''}.
refine (existT _ (remove_lst lst i j) _).
 split.
  now apply remove_lst_i.
  now apply remove_lst_i'.
Defined.


Definition remove_lst'' (lst : list (list A)) (i : {n : nat | n < length lst}) (j : {n : nat | n < length (nth_d lst i)})
 : {lst' : list (list A) |
     (exists i' : {n : nat | n < length lst'},
       proj1_sig i = proj1_sig i'
       /\ forall (j' : {n : nat | n < length (nth_d lst i)}) (j'' : {n : nat | n < length (nth_d lst' i')}),
           (proj1_sig j > proj1_sig j'' -> proj1_sig j' = proj1_sig j'' -> nth_d (nth_d lst i) j' = nth_d (nth_d lst' i') j'')
           /\ (proj1_sig j <= proj1_sig j'' -> proj1_sig j' = S (proj1_sig j'') -> nth_d (nth_d lst i) j' = nth_d (nth_d lst' i') j''))
     /\ forall i' : {n : nat | n < length lst},
         proj1_sig i <> proj1_sig i' ->
          exists i'' : {n : nat | n < length lst'},
           proj1_sig i' = proj1_sig i'' /\ nth_d lst i' = nth_d lst' i''}.
refine (existT _ (remove_lst lst i j) _).
 unfold remove_lst; split.
  exists (replace_d_nat_translate lst (remove_d (nth_d lst i) j) i i).
   split.
    now apply replace_d_nat_translate_proj_eq.
    rewrite (replace_d_nth lst (remove_d (nth_d lst i) j) i (replace_d_nat_translate lst (remove_d (nth_d lst i) j) i i)).
     intros j' j''.
      split; intros Hcmp He.
       apply remove_d_nth_lt; now auto.
       apply remove_d_nth_ge; now auto.
     now apply replace_d_nat_translate_proj_eq.
  now apply remove_lst_i'.
Defined.



End dep.

Recursive Extraction remove_lst.
Extraction remove_lst'.
Extraction remove_lst''.


End Dependent.






(* From logic spec *)
Module Predicate.

Section nth.

Context {A : Type}.

Inductive Nth : list A -> nat -> A -> Prop :=
| Nth_O : forall l a, Nth (a :: l) 0 a
| Nth_S : forall l n a a', Nth l n a -> Nth (a' :: l) (S n) a.


Lemma Nth_length_n :
 forall (l : list A) (n : nat) (a : A),
  Nth l n a -> n < length l.
intros; induction H; simpl; omega.
Qed.


Lemma Nth_n_exists :
 forall (l : list A) (n : nat),
  n < length l -> exists a : A, Nth l n a.
intros l n; revert l; induction n; intros.
 destruct l.
  simpl in H; omega.
  exists a; now constructor.
 destruct l.
  simpl in H; omega.
  simpl in H; apply lt_S_n in H; apply IHn in H.
   destruct H as [a' H]; exists a'; constructor; now auto.
Qed.


Lemma Nth_unique :
 forall (l : list A) (n : nat) (a1 a2 : A),
  Nth l n a1 -> Nth l n a2 -> a1 = a2.
intros l n; revert l; induction n; intros.
 inversion H; subst; inversion H0; subst; now auto.
 inversion H; subst; inversion H0; subst.
  now eauto.
Qed.


End nth.


Section replace.

Context {A : Type}.

Variable a : A.

Inductive Replace : list A -> nat -> list A -> Prop :=
| Replace_O : forall l a', Replace (a' :: l) O (a :: l)
| Replace_S : forall l n a' l', Replace l n l' -> Replace (a' :: l) (S n) (a' :: l').


Lemma Replace_length_eq :
 forall (l : list A) (n : nat) (l' : list A),
  Replace l n l' -> length l = length l'.
intros.
induction H; simpl; now auto.
Qed.


Lemma Replace_length_n :
 forall (l : list A) (n : nat) (l' : list A),
  Replace l n l' -> n < length l.
intros l n; revert l; induction n; intros.
 inversion H; subst.
  simpl; omega.
 inversion H; subst.
  apply IHn in H2.
   simpl; omega.
Qed.


Lemma Replace_n_exists :
 forall (l : list A) (n : nat),
  n < length l -> exists l' : list A, Replace l n l'.
intros l n; revert l; induction n; intros.
 destruct l; simpl in H.
  omega.
  exists (a :: l); now constructor.
 destruct l; simpl in H.
  omega.
  apply lt_S_n in H.
   apply IHn in H.
    destruct H as [l' H].
     exists (a0 :: l'); constructor; now auto.
Qed.


Lemma Replace_unique :
 forall (l : list A) (n : nat) (l1 l2 : list A),
  Replace l n l1 -> Replace l n l2 -> l1 = l2.
intros l n; revert l; induction n; intros.
 inversion H; subst; inversion H0; subst; now auto.
 inversion H; subst; inversion H0; subst.
  f_equal; now eauto.
Qed.


Lemma Replace_mth :
 forall (l : list A) (n : nat) (l' : list A) (m : nat) (a1 a2 : A),
  Replace l n l' -> n <> m -> Nth l m a1 -> Nth l' m a2 -> a1 = a2.
intros l n l' m a1 a2 H; revert m; induction H; intros.
 inversion H0; subst.
  elim H; now auto.
  inversion H1; subst.
   apply Nth_unique with l n; now auto.
 inversion H1; subst.
  inversion H2; subst; now auto.
  inversion H2; subst; now eauto.
Qed.


Lemma Replace_nth :
 forall (l : list A) (n : nat) (l' : list A),
  Replace l n l' -> Nth l' n a.
intros; induction H; simpl.
 now constructor.
 constructor; now auto.
Qed.


End replace.


Section remove.

Context {A : Type}.

Inductive Remove : list A -> nat -> list A -> Prop :=
| Remove_O : forall l a, Remove (a :: l) O l
| Remove_S : forall l n a l', Remove l n l' -> Remove (a :: l) (S n) (a :: l').


Lemma Remove_length_S :
 forall (l : list A) (n : nat) (l' : list A),
  Remove l n l' -> length l = S (length l').
intros; induction H; simpl; now auto.
Qed.


Lemma Remove_length_n :
 forall (l : list A) (n : nat) (l' : list A),
  Remove l n l' -> n < length l.
intros l n; revert l; induction n; intros.
 inversion H; subst.
  simpl; omega.
 inversion H; subst.
  apply IHn in H2.
   simpl; omega.
Qed.


Lemma Remove_n_exists :
 forall (l : list A) (n : nat),
  n < length l -> exists l' : list A, Remove l n l'.
intros l n; revert l; induction n; intros.
 destruct l; simpl in H.
  omega.
  exists l; now constructor.
 destruct l; simpl in H.
  omega.
  apply lt_S_n in H.
   apply IHn in H.
    destruct H as [l' H].
     exists (a :: l'); constructor; now auto.
Qed.


Lemma Remove_unique :
 forall (l : list A) (n : nat) (l1 l2 : list A),
  Remove l n l1 -> Remove l n l2 -> l1 = l2.
intros l n; revert l; induction n; intros.
 inversion H; subst; inversion H0; subst; now auto.
 inversion H; subst; inversion H0; subst.
  f_equal; now eauto.
Qed.


Lemma Remove_mth_ge :
 forall (l : list A) (n : nat) (l' : list A) (m : nat) (a1 a2 : A),
  Remove l n l' -> n <= m -> Nth l (S m) a1 -> Nth l' m a2 -> a1 = a2.
intros l n l' m a1 a2 H; revert m; induction H; intros.
 inversion H0; subst.
  eapply Nth_unique; now eauto.
 inversion H2; subst.
  omega.
  inversion H1; subst.
   inversion H2; subst.
    apply le_S_n in H0.
     now eauto.
Qed.


Lemma Remove_mth_lt :
 forall (l : list A) (n : nat) (l' : list A) (m : nat) (a1 a2 : A),
  Remove l n l' -> m < n -> Nth l m a1 -> Nth l' m a2 -> a1 = a2.
intros l n l' m a1 a2 H; revert m; induction H; intros.
 omega.
 destruct m.
  inversion H1; subst; inversion H2; subst; now auto.
  inversion H1; subst; inversion H2; subst.
   apply lt_S_n in H0; now eauto.
Qed.


End remove.


Section pred.

Context {A : Type}.

Definition Remove_i_j (lst : list (list A)) (i j : nat) (lst' : list (list A)) : Prop :=
 exists l l' : list A, Nth lst i l /\ Remove l j l' /\ Replace l' lst i lst'.


(* Uniqueness *)
Theorem Remove_i_j_unique :
 forall (lst : list (list A)) (i j : nat) (lst1 lst2 : list (list A)),
  Remove_i_j lst i j lst1 -> Remove_i_j lst i j lst2 -> lst1 = lst2.
unfold Remove_i_j; intros.
 destruct H as [l1 [l1' [H11 [H12 H13]]]].
  destruct H0 as [l2 [l2' [H21 [H22 H23]]]].
   assert (l1 = l2).
    eapply Nth_unique; now eauto.
   subst.
   assert (l1' = l2').
    eapply Remove_unique; now eauto.
   subst.
   eapply Replace_unique; now eauto.
Qed.


(* Length specificatoin 1 *)
Theorem Remove_i_j_length_i :
 forall (lst : list (list A)) (i j : nat) (lst' : list (list A)),
  Remove_i_j lst i j lst' -> exists l l' : list A, Nth lst i l /\ Nth lst' i l' /\ length l = S (length l').
unfold Remove_i_j; intros.
 destruct H as [l [l' [H1 [H2 H3]]]].
  exists l, l'; intuition.
   apply Replace_nth with lst; now auto.
   apply Remove_length_S with j; now auto.
Qed.


(* Length specificatoin 2' *)
Theorem Remove_i_j_eq_k :
 forall (lst : list (list A)) (i j : nat) (lst' : list (list A)) (k : nat),
  Remove_i_j lst i j lst' -> i <> k -> k < length lst -> exists l : list A, Nth lst k l /\ Nth lst' k l.
unfold Remove_i_j; intros.
 destruct H as [l [l' [H2 [H3 H4]]]].
  destruct (Nth_n_exists lst k H1) as [l1 H5].
   exists l1; split.
    now auto.
    destruct (Nth_n_exists lst' k).
     erewrite <- Replace_length_eq; now eauto.
     erewrite Replace_mth; now eauto.
Qed.

(* Length specificatoin 2 *)
Corollary Remove_i_j_length_k :
 forall (lst : list (list A)) (i j : nat) (lst' : list (list A)) (k : nat),
  Remove_i_j lst i j lst' -> i <> k -> k < length lst -> exists l l' : list A, Nth lst k l /\ Nth lst' k l' /\ length l = length l'.
intros.
 destruct (Remove_i_j_eq_k _ _ _ _ _ H H0 H1) as [l [Hx Hy]].
  exists l, l; now auto.
Qed.


End pred.

End Predicate.
