(* -------------------------------------------------------------------- *)
Require Import ssreflect ssrbool List.
Require Import Nat.

Set Implicit Arguments.

Axiom todo : forall {A}, A.
Ltac todo := by apply: todo.

(* ==================================================================== *)
(* This template contains incomplete definitions that you have to       *)
(* fill. We always used the keyword `Definition` for all of them but    *)
(* you are free to change for a `Fixpoint` or an `Inductive`.           *)
(*                                                                      *)
(* If needed, it is perfectly fine to add intermediate definitions and  *)
(* local lemmas.                                                        *)

(* ==================================================================== *)
(* In this project, we are going to develop and prove correct an        *)
(* algorithm for deciding the membership of a word w.r.t. a given       *)
(* regular language - all these terms are going to be defined below     *)

(* This project lies in the domain of *formal languages*. The study     *)
(* of formal languages is a branch of theoretical computer science and  *)
(* is about that is interested in the purely syntactical aspects of     *)
(* of languages and as applications in different domains, ranging from  *)
(* the definition of  the grammar of programming languages to the field *)
(* of automated translation.                                            *)

(* As with natural languages, we first need to fix an alphabet. In our  *)
(* case, we are simply going to declare a type `A : Type` - i.e. we     *)
(* will use the same alphabet for all the formal languages we are going *)
(* to study. Inhabitants of `A` are called `letters`.                   *)

Parameter (A : Type).

(* -------------------------------------------------------------------- *)
(* A `word` is then simply a finite sequence of letters of `A`. We      *)
(* denote by A* the set of words over `A`. In Coq, we are going to      *)
(* represent words as lists whose elements are inhabitants of `A`. This *)
(* naturally leads to the following definition:                         *)

Notation word := (list A).

(* -------------------------------------------------------------------- *)
(* In this setting, a `language` is simply a subset of A*. Assuming     *)
(* that `x` & `y` are letters of A, we can define the following         *)
(* languages:                                                           *)
(*                                                                      *)
(*  - the empty language: `L = ∅`;                                      *)
(*                                                                      *)
(*  - the language that contains only the empty word ε (i.e. the only   *)
(*    (word of length 0): L = {ε}`;                                     *)
(*                                                                      *)
(*  - the language that contains all the words solely composed of the   *)
(*    letter `x`: L = { ε, x, xx, xxx, ... } = { xⁿ | n ∈ ℕ } (here,    *)
(*    xⁿ stands for the word x…x, where x is repeated n times);         *)
(*                                                                      *)
(*  - the language that contains all the words of the form xⁿyⁿ:        *)
(*    L = { xⁿyⁿ | n ∈ ℕ };                                             *)
(*                                                                      *)
(*  - if we assume that A contains the letter '[' & ']', we can         *)
(*    define the language of well-balanced words for '[' & ']':         *)
(*    L = { w ∈ { [, ] }* | s.t. P(w) && Q(w) }, where                  *)
(*      - P(w) = any prefix of w contain no more ]'s then ['s           *)
(*      - Q(w) = the number of ['s and ]'s of w are equal.              *)

(* -------------------------------------------------------------------- *)
(* We can also combine languages to form other languages. For example,  *)
(* if L and G are languages, we can define:                             *)
(*                                                                      *)
(*  - the union of L & G            L ∪ G                               *)
(*  - the concatenation of L & G    { w1 · w2 | w1 ∈ L, w2 ∈ G }        *)
(*  - the intersection of L & G     L ∩ G                               *)
(*  - the complement of L           A* \ L                              *)
(*  - the Kleene closure of L       L* = { wⁿ | w ∈ L, n ∈ ℕ }          *)
(*  - the mirror of L               rev(L) = { rev(w) | w ∈ L }         *)

(* -------------------------------------------------------------------- *)
(* To define languages in Coq, we need a way to represent subsets       *)
(* of A*, i.e. subsets of the set of `word`'s. To that end, we are      *)
(* going to represent a set using its indicator function. (We remind    *)
(* that, given a subset F of an ambient set E, the indicator function   *)
(* of F is the function f_E from E to { ⊤, ⊥ } s.t.                     *)
(*                                                                      *)
(*                     f_E(x) = ⊤ iff x ∈ E                             *)

(* In Coq, the codomain of its indicator function is going to be a      *)
(* proposition: given a function `F : E -> Prop`, we say that x belongs *)
(* to `x` iff `f x` holds.                                              *)

Notation language := (word -> Prop).

(* -------------------------------------------------------------------- *)
(* From now use, we assume that L, G, H denote languages, x, y denote   *)
(* letters and that and w denotes a word.                               *)

Implicit Types (L G H : language) (x y : A) (w : word).

(*We define the languages.*)

Definition lang0 : language :=
  fun w => False.

Definition lang1 : language :=
  fun w => w = nil.

Definition langW w0 : language := 
  fun w => w = w0.

Definition langF (ws : list word) : language := 
  fun w => (In w ws).

Definition langA x : language :=
  fun w => w = (x::nil).

Definition langU L G : language := 
  fun w => ((L w) \/ (G w)).

Definition langI L G : language :=
  fun w => ((L w) /\ (G w)).

Definition langS L G : language :=
  fun w => (exists w1 w2, (L w1) /\ (G w2) /\ (w = w1 ++ w2)).

Inductive langK L: language:=
| Knil : langK L nil
(*| KL w: (L w) -> langK L w*)
| Krec w1 w2: (L w1) -> (langK L w2) -> langK L (w1++w2).

Definition langM L : language := 
  fun w => (L (rev w)).

(*We now define equality between two languages*)
(*match w , exist w1 in L, n integer : w=w1++w1 n times *)
Definition eqL L G := forall w, L w <-> G w.

Infix "=L" := eqL (at level 90).

(* Q2. Prove the following equivalances:                                *)

Lemma concat0L L : langS lang0 L =L lang0.
(* Here we check for every word that it is true: induction *)
Proof.
move => w.
induction w; split; try done; simpl.

+unfold langS.
 unfold lang0.
 move => H.
 destruct H.
 destruct H.
 destruct H.
 apply H.

+unfold lang0.
 unfold langS.
 move=>H.
 destruct H.
 destruct H.
 destruct H.
 apply H.

Qed.

Lemma concatL0 L : langS L lang0 =L lang0.
(*We proceed using the same method as before *)
Proof.
unfold langS.
unfold lang0.
move=> w.
split.

+move=>H1.
 destruct H1 .
 destruct H.
 destruct H.
 destruct H0.
 apply H0.

(*Obvious False -> Prop is always true *)
+done.

Qed.

Lemma concat1L L : langS lang1 L =L L.
Proof. 
unfold langS.
unfold lang1.
move=>w.
split.
(* First implication *)
 +move=>H.
 destruct H.
 destruct H.
 destruct H.
 destruct H0.
 rewrite H in H1.
 rewrite H1.
 simpl.
 apply H0.
(* Second implication *)
+move=>Lw.
 exists nil.
 exists w.
 done.

Qed.

Lemma concatL1 L : langS L lang1 =L L.
Proof.

unfold langS.
unfold lang1.
move=>w.
split.
(* First implication *)
+move=>h.
 destruct h.
 destruct H.
 destruct H.
 destruct H0.
 rewrite H0 in H1.
 rewrite H1.
 rewrite ( app_nil_r x).
 apply H.
(* Second implication *)
+move=>lw.
 exists w.
 exists nil.
 rewrite (app_nil_r w).
 split.
 apply lw.
 split; try done.
Qed.

Lemma concatA L G H : langS (langS L G) H =L langS L (langS G H).
(* Lang S is transitive *)
(* We move a word and then check existentials *)
Proof. 
move=>w.
split.
(* First implication *)
+move=>h.
 destruct h, H0, H0.
 case:H0.
 move=> w1 h.
 destruct h.
 unfold langS.
 exists w1. exists (x1++x0).
 split.
  ++apply H0.
  ++split.
    exists x1.
    exists x0.
    split.
    +++apply H0.
    +++destruct H1, H0, H3.
       split.
       apply H1.
       done. 
    +++destruct H1.
       rewrite H2.
       destruct H0, H3.
       rewrite H4.
       symmetry.
       apply app_assoc.
+move=>h.
 destruct h, H0, H0, H1.
 case:H1.
 move=>x1 Ih.
 unfold langS.
 destruct Ih.
 exists (x++x1). exists x2.
 split.
 ++exists x. exists x1.
   split;try assumption.
   split;try assumption.
   apply H1.
   reflexivity.
 ++split.
 +++apply H1.
 +++destruct H1, H3.
    rewrite app_assoc_reverse.
    rewrite H2.
    rewrite H4.
    reflexivity.

Qed.

Lemma unionC L G : langU L G =L langU G L.
(* The Union of two languages is a symmetric relation *)
Proof. 
unfold langU.
split.
+move => [a|b].
 right. done. left. done.
+move => [a|b].
right. done. left. done.

Qed.

Lemma interC L G : langI L G =L langI G L.
(* The Intersection of two languages is a symmetric relation *)
Proof.
unfold langI.
split.
+move => a.
 destruct a.
 split.
 assumption.
 assumption.
+move => a.
 destruct a.
 split.
 assumption.
 assumption.

Qed.

Lemma langKKaux L : forall w1 w2, (langK L w1) -> (langK L w2) -> (langK L (w1++w2)).
(* The Kleene closure is transitive *)
Proof.
move => w1 w2 p1 p2.
induction p1.
+rewrite (app_nil_l w2).
 apply p2.
+rewrite (app_assoc_reverse w1 w0 w2).
 apply Krec.
 apply H.
 assumption.

Qed.

Lemma KL L w: (L w) -> (langK L w).
(* L is in the Kleene closure of itself *)
Proof.
move => p.
rewrite (app_nil_end w).
apply Krec.
+assumption.
+apply Knil.

Qed.

Lemma langKK L : langK (langK L) =L langK L.
(* As it is an infinite union langk -n times- =lang k *)
Proof.
split.
+move =>p.
 induction p.
 apply Knil.
 apply langKKaux; assumption.
+move => p.
 apply KL. assumption.

Qed.


(* Note that, since languages are represented as indicator functions    *)
(* over `Prop`, we cannot assess that `L =L G` implies `L = G`.         *)

(* ==================================================================== *)
(*                          REGULAR LANGUAGES                           *)

(* We are now interested in a subclass of languages called regular     *)
(* languages: a language `L` is said to be regular iff one of the      *)
(* following holds:                                                     *)
(*                                                                      *)
(*  - L = ∅ or L = {ε} or L = {x} for some x ∈ A ;                      *)
(*  - L = L1 ∪ L2 for L1, L2 regular languages ;                        *)
(*  - L = L1 · L2 for L1, L2 regular languages ;                        *)
(*  - L = G* for G a regular language.                                  *)

(* This kind of inductive definitions can be encoded in Coq using       *)
(* an inductive predicate `regular : language -> Prop` s.t.             *)
(*                                                                      *)
(*             L is regular iff `regular L` holds                       *)

(* Q3. complete the following definition of the predicate `regular`:    *)

Inductive regular : language -> Prop :=
| REq L G of regular L & G =L L : regular G
| REmpty : regular lang0
| REnil : regular lang1
| RE1 x : regular (langA x)
| REU L G: regular L -> regular G -> regular (langU L G)
| RES L G: regular L -> regular G -> regular (langS L G)
| REK L: (regular L) -> (regular (langK L))
.

(* -------------------------------------------------------------------- *)
(* Q4. prove that `langW w` is regular.                                 *)
Lemma regW_aux x w: (langW (x::w)) =L (langS (langA x) (langW w)).
(* We use this Lemma  to make the next proof  clearer *)
Proof.
split.
+move => p.
 unfold langW in p.
 unfold langS.
 exists (x::nil).
 exists w; split; done.
+move => p.
 unfold langW in p.
 unfold langW.
 unfold langS in p.
 unfold langA in p.
 destruct p. destruct H. destruct H. destruct H0.
 rewrite H in H1. rewrite H0 in H1.
 apply H1.

Qed.

Lemma regularW w : regular (langW w).
Proof.
induction w.
apply REnil.
apply REq with (langS (langA a) (langW w)).
apply RES.
apply RE1.
apply IHw.
apply (regW_aux a w).
Qed.

Lemma regularM_aux L G: L =L G -> (langM L) =L (langM G).
(* The reverse maintains equivalence relation *)
Proof.
unfold eqL.
split; apply H.
Qed.

Lemma revx x: (rev (x::nil)) = (x::nil).
(* Obvious but not present in coq *)
Proof.
done.
Qed.

(* -------------------------------------------------------------------- *)
(* Q5. prove that `langM L` is regular, given that L is regular.        *)
Lemma regularM L : regular L -> regular (langM L).
(* The reverse of a regular language is regular *)
(* We proceed by induction over the cases of regular *)
Proof.
move => reg.
induction reg.
+apply regularM_aux in H.
apply REq with (langM L).
apply IHreg. apply H.
+apply REmpty.
+apply REq with (lang1).
apply REnil.
split.
unfold langM, lang1. move => ass.
have: rev (rev w) = nil by rewrite ass.
move => p.
rewrite rev_involutive in p.
apply p.
unfold langM, lang1.
move => ass.
have: (rev w) = (rev nil) by rewrite ass.
move => p.
apply p.
+apply REq with (langA x).
apply RE1.
unfold langM, langA.
split.
move => ass.
have: (rev (rev w)) = (x::nil) by rewrite ass.
move => p.
rewrite rev_involutive in p.
apply p.
move=> ass.
have: (rev w) = (rev (x::nil)) by rewrite ass.
move => p.
apply p.
+apply REq with (langU (langM L) (langM G)).
apply REU.
apply IHreg1. apply IHreg2.
unfold langM, langU.
done.
+apply REq with (langS (langM G) (langM L)).
apply RES.
apply IHreg2. apply IHreg1.
unfold langM, langS.
split.
move => p. destruct p. destruct H.
exists (rev x0). exists (rev x). rewrite rev_involutive. rewrite rev_involutive.
destruct H. destruct H0.
split. assumption. split. assumption.
have: (rev (rev w)) = rev(x ++ x0) by rewrite H1.
move => p.
rewrite rev_involutive in p.
rewrite (rev_app_distr x x0) in p.
apply p.
move => p. destruct p. destruct H. destruct H. destruct H0.
exists (rev x0). exists (rev x).
split. assumption. split. assumption.
have: (rev w) = (rev (x ++ x0)) by rewrite H1.
move => p.
rewrite (rev_app_distr x x0) in p.
apply p.
+apply REq with (langK (langM L)). 
apply REK.
apply IHreg.
split.
unfold langM.
move => p.
rewrite -[w]rev_involutive.
move: (rev w) p.
move => {w}.
move => w p.
induction p.
apply Knil.
rewrite rev_app_distr.
apply langKKaux.
assumption.
apply KL.
rewrite rev_involutive. assumption.
unfold langM.
move => p.
rewrite -[w]rev_involutive.
move: w p.
move => w1 p.
induction p.
apply Knil.
rewrite rev_involutive.
rewrite rev_app_distr.
apply langKKaux.
rewrite rev_involutive in IHp.
assumption.
apply KL. assumption.
Qed.

(* ==================================================================== *)
(*                        REGULAR EXPRESSIONS                           *)

(* Related to regular languages is the notion of regular expressions.   *)
(* A regular expression is a formal, syntactic expression that can      *)
(* latter be interpreted as a regular language. Regular expressions are *)
(* pervasive in computer science, e.g. for searching for some text in   *)
(* a file, as it is possible with the `grep` command line tool.         *)
(*                                                                      *)
(* For instance, the command:                                           *)
(*                                                                      *)
(*    grep -E 'ab*a' foo.txt                                            *)
(*                                                                      *)
(* is going to print all the lines of `foo.txt` that contains a word    *)
(* of the form ab⋯ba (where the letter b can be repeated 0, 1 or more   *)
(* time. I.e., grep is going to find all the lines of `foo.txt` that    *)
(* contains a word that belongs in the formal language:                 *)
(*                                                                      *)
(*    L = { abⁿa | n ∈ ℕ }                                              *)
(*                                                                      *)
(* If you need to convince yourself that L is regular, note that:       *)
(*                                                                      *)
(*    L = { a } ∪ { b }* ∪ { a }                                        *)
(*                                                                      *)
(* In some sense, a regular expression is just a compact way to         *)
(* represent a regular language, and its definition is going to be      *)
(* close to the one of regular languages.                               *)
(*                                                                      *)
(* A regular expression is either:                                      *)
(*                                                                      *)
(*  - the constant ∅ or the constant ε or one letter from A             *)
(*  - the disjunction r1 | r2 of two regular expressions                *)
(*  - the concatenation r1 · r2 of two regular expressions              *)
(*  - the Kleene r* of some regular expression                          *)

(* We can represent regular expressions as a inductive type in Coq.     *)

(* Q6. complete the following definition:                               *)

Inductive regexp : Type :=
| RE_Empty : regexp
| RE_Void  : regexp
| RE_Atom  : A -> regexp
| RE_Disj  : regexp -> regexp -> regexp
| RE_Conc  : regexp -> regexp -> regexp
| RE_Kleene: regexp -> regexp.


Implicit Types (r : regexp).

(* We now have to formally related regular expressions to regular       *)
(* languages. For that purpose, we are going to interpret a regular     *)
(* expression as a languages. If r is a regular expression, then we     *)
(* denote by language [r] as follows:                                   *)
(*                                                                      *)
(*   - [∅]       = ∅                                                    *)
(*   - [ε]       = ε                                                    *)
(*   - [a]       = { a } for a ∈ A                                      *)
(*   - [r₁ ∪ r₂] = [r₁] ∪ [r₂]                                          *)
(*   - [r₁ · r₂] = [r₁] · [r₂]                                          *)
(*   - [r*]      = [r]*                                                 *)

(* Q7. implement the Coq counterpart of the above definition:           *)

Fixpoint interp (r : regexp) {struct r} : language :=
(* regular expressions are a compact way to represent regular languages  *)
  match r with
  | RE_Empty => lang0
  | RE_Void  => lang1
  | RE_Atom x => (langW (cons x nil))
  | RE_Disj r1 r2 => (langU (interp r1) (interp r2))
  | RE_Conc r1 r2  => (langS (interp r1) (interp r2))
  | RE_Kleene r => (langK (interp r))
  end.

(* Q8. show that the interpretation of a regular expression is a        *)
(*     regular language:                                                *)
Lemma regular_regexp r : regular (interp r).
(* We proceed by induction over the cases of regular expressions *)
Proof.
induction r; simpl.
apply REmpty.
apply REnil.
apply RE1.
apply REU.
apply IHr1.
apply IHr2.
apply RES; auto.
apply REK.
apply IHr.
Qed.

(* Q9. show that any regular language can be interpreted as a           *)
(*     regular expression:                                              *)

Lemma regexp_regular L : regular L -> exists r, L =L interp r.
Proof.
(* We proceed by induction on the cases of languages *)
(* We just have to match the correct existentials *)
move => regL.
induction regL.
  +destruct IHregL.
   exists x.
   move=>w.
   rewrite H .
   apply H0.
  +exists RE_Empty;simpl;try done.
  +exists RE_Void;simpl;try done.
  +exists (RE_Atom x);simpl; unfold langA; unfold langW;done.
  +destruct IHregL1.
   destruct IHregL2.
   exists (RE_Disj x x0);simpl.
   unfold langU.
   move=>w.
   rewrite H.
   rewrite H0.
   done.
  +destruct IHregL1.
   destruct IHregL2.
   exists( RE_Conc x x0);simpl.
   unfold langS .
   move=>w.
   split.
   move=> Hp .
   destruct Hp.
   destruct H1.
   exists x1.
   exists x2.
   split.
   unfold eqL in H.
   apply H.
   apply H1.
   split.
   unfold eqL in H0.
   apply H0.
   apply H1.
   apply H1.
   move=>hp.
   destruct hp.
   destruct H1.
   destruct H1.
   destruct H2.
   exists x1.
   exists x2.
   split.
   unfold eqL in H.
   apply H.
   apply H1.
   unfold eqL in H0.
   split.
   apply H0.
   apply H2.
   apply H3.
  +destruct IHregL.
   exists (RE_Kleene x);simpl.
   split.
   move=>H2.
   unfold eqL in H.
   induction H2.
   apply Knil.
   apply Krec.
   apply H.
   apply H0.
   apply IHlangK.
   unfold eqL in H.
   move=>H1.
   induction H1.
   apply Knil.
   apply Krec.
   apply H.
   apply H0.
   apply IHlangK.
Qed.

(* Of course, it may happen that two regular expressions represent      *)
(* the same language: r1 ~ r2 iff [r1] = [r2].                          *)

(* Q10. write a binary predicate eqR : regexp -> regexp -> Prop s.t.    *)
(*      eqR r1 r2 iff r1 and r2 are equivalent regexp.                  *)

Definition eqR (r1 r2 : regexp) : Prop := (interp r1) =L (interp r2).

Infix "~" := eqR (at level 90).

(* Q11. state and prove the following regexp equivalence:               *)
(*           (a|b)* ~ ( a*b* )*                                         *)

Lemma small_eq r1 r2: 
(RE_Kleene (RE_Disj (r1) (r2))) 
~ (RE_Kleene (RE_Conc (RE_Kleene (r1)) (RE_Kleene (r2)))).
(* We proceed by induction over the cases *)
Proof.
split.
+move => int.
  induction int.
  apply Knil.
  simpl. simpl in H. simpl in int. simpl in IHint.
  apply Krec.
  destruct H.
  unfold langS.
  exists w1. exists nil.
  split. apply KL. assumption. 
  split. apply Knil.
  rewrite app_nil_r. done.
  unfold langS.
  exists nil. exists w1.
  split. apply Knil.
  split. apply KL. assumption.
  done.
  assumption.
+move => int.
  induction int.
  apply Knil.
  simpl in H, int, IHint. simpl.
  apply langKKaux; last done.
  case: H => [w11][w12][H1][H2] ->.
  apply langKKaux.
  induction H1.
  apply Knil.
  apply Krec.
  left. assumption.
  assumption.
  induction H2.
  apply Knil.
  apply Krec.
  right. assumption.
  assumption.
Qed.

(* ==================================================================== *)
(*                          REGEXP MATCHING                             *)

(* We now want to write a algorithm for deciding if a given word `w`    *)
(* matches a regular expression `r`, i.e. for deciding wether `w ∈ [r]` *)
(*                                                                      *)
(* For that purpose, we are going to use Brzozowski's derivatives.      *)
(*                                                                      *)
(* The idea of the algorithm is the following:                          *)
(*                                                                      *)
(* Given a letter `x` and an regular expression `r`, the Brzozowski's   *)
(* derivatives of `x` w.r.t. `r` is a regular expression x⁻¹·r s.t.     *)
(*                                                                      *)
(*    x · w ∈ [r] ⇔ w ∈ [x⁻¹·r]                                         *)
(*                                                                      *)
(* Assuming that we can compute a Brzozowski's derivative for any       *)
(* letter `x` and regular expression `r`, one can check that a word `w` *)
(* matches a regexp `r` as follows:                                     *)
(*                                                                      *)
(*   - if w = x · w' for some letter x and word w', we recursively      *)
(*     check that `w` matches `x⁻¹·r`; otherwise                        *)
(*   - if w = ε, then we directly check that [r] contains the empty     *)
(*     word - a property that is deciable.                              *)

(* Q12. write a nullity test `contains0` : regexp -> bool s.t.          *)
(*                                                                      *)
(*      ∀ r, contains0 r ⇔ ε ∈ [e]                                      *)

Fixpoint contains0 (r : regexp) : bool := 
  match r with
  | RE_Empty      => false
  | RE_Void       => true
  | RE_Atom a     => false
  | RE_Disj r1 r2 => (contains0 r1) || (contains0 r2)
  | RE_Conc r1 r2 => (contains0 r1) && (contains0 r2)
  | RE_Kleene r   => true
  end.

(* Q13. prove that your definition of `contains0` is correct:           *)

Lemma contains0_ok r : contains0 r <-> interp r nil.
(* To show that the definition is correct we check it for each r *)
Proof.
split.
move => cont.
+induction r.
++discriminate.
++done.
++discriminate.
++simpl.
  unfold langU.
  simpl in cont.
  move/orP: cont=>[cont|cont].
  left.
  apply IHr1.
  apply cont.
  right.
  apply IHr2.
  apply cont.
++simpl in cont.
  move/andP: cont=>cont.
  simpl.
  unfold langS.
  exists  nil.
  exists  nil.
  split.
  apply IHr1.
  apply cont.
  split.
  apply IHr2.
  apply cont.
  trivial.
++apply Knil.
+induction r.
++simpl;done.
++simpl;done.
++simpl;done.
++simpl.
  move=>lang.
  unfold langU in lang.
  destruct lang.
  rewrite IHr1.
  apply H.
  done.
  rewrite IHr2.
  apply H.
  apply Bool.orb_true_r.
++simpl.
  move=>lang.
  unfold langS in lang.
  destruct lang.
  destruct H.
  destruct H.
  destruct H0.
  symmetry in H1.
  apply app_eq_nil in H1.
  destruct H1.
  rewrite H1  in H.
  rewrite H2 in H0.
  rewrite IHr1.
  apply H.
  rewrite Bool.andb_true_l.
  rewrite IHr2.
  apply H0.
  done.
++simpl.
  done.
Qed.

(* We give below the definition of the Brzozowski's derivative:         *)
(*                                                                      *)
(*   - x⁻¹ · x         = ε                                              *)
(*   - x⁻¹ · y         = ∅ if x ≠ y                                     *)
(*   - x⁻¹ · ε         = ∅                                              *)
(*   - x⁻¹ · ∅         = ∅                                              *)
(*   - x⁻¹ · (r₁ | r₂) = (x⁻¹ · r₁) | (x⁻¹ · r₂)                        *)
(*   - x⁻¹ · (r₁ · r₂) = (x⁻¹ · r₁) · r₂ | E(r₁) · (x⁻¹ · r₂)           *)
(*   - x⁻¹ · r*        = (x⁻¹ · r) · r*                                 *)
(*                                                                      *)
(* where E(r) = ε if ε ∈ [r] & E(r) = ∅ otherwise.                      *)

(* Q14. write a function `Brzozowski` that computes a Brzozowski's      *)
(*      derivative as defined above.                                    *)
(*                                                                      *)
(* For that purpose, you may need to have a decidable equality over     *)
(* `A`. The parameter `Aeq` along with the axioms `Aeq_dec` give        *)
(* you such a decidable equality.                                       *)

Parameter Aeq : A -> A -> bool.

(* Here, `Aeq x y` has to be read as `Aeq x y = true`                   *)
Axiom Aeq_dec : forall (x y : A), Aeq x y <-> x = y.

Fixpoint Brzozowski (x : A) (r : regexp) : regexp := 
match r with
  | RE_Empty      => RE_Empty
  | RE_Void       => RE_Empty
  | RE_Atom y      => if (Aeq x y) then RE_Void else RE_Empty
  | RE_Disj r1 r2 => (RE_Disj (Brzozowski x r1) (Brzozowski x r2))
  | RE_Conc r1 r2 => (RE_Disj (RE_Conc (Brzozowski x r1) r2) (RE_Conc (if (contains0 r1) then RE_Void else RE_Empty) (Brzozowski x r2)))
  | RE_Kleene r   => (RE_Conc (Brzozowski x r) (RE_Kleene r))
  end.

(* Q15. write a function `rmatch` s.t. `rmatch r w` checks wether a     *)
(*      word `w` matches a given regular expression `r`.                *)

Fixpoint rmatch (r : regexp) (w : word) : bool := 
match w with
  | nil   => (contains0 r)
  | x::w0 => (rmatch (Brzozowski x r) w0)
  end.

(* Q16. show that the `Brzozowski` function is correct.                 *)

Lemma Brzozowski_correct (x : A) (w : word) (r : regexp) :
  interp (Brzozowski x r) w -> interp r (x :: w).
Proof.
move=>brzo.
induction w.
+induction r.
++done.
++done.
++simpl in brzo .
  case: (Aeq x a) in brzo.
  simpl.
  simpl in brzo.
  unfold lang1 in brzo.
  unfold langW.
  
  

  
Admitted.

(* Q17. show that `rmatch` is correct.                                  *)

Lemma rmatch_correct (r : regexp) (w : word):
  rmatch r w -> interp r w.
Proof.
move=>H.
induction w.
induction r.
+done.
+done.
+done.
+simpl.
  unfold langU.
  simpl in H.
  move/orP: H => [H | H].
  left.
  apply IHr1.
  assumption. (* contains0 r is equivalent to rmatch r nil*)
  right.
  apply IHr2.
  assumption.
+simpl.
  unfold langS.
  simpl in H.
  move/andP: H=>H .
  exists nil .
  exists nil.
  split.
  ++apply IHr1.
    apply H.
  ++split.
    apply IHr2.
    apply H.
    trivial.
+simpl.
  apply Knil.
+induction r.
++simpl.
  simpl in H.
  unfold lang0.
  apply IHw.
  apply H.
++simpl.
  simpl in H.
  unfold lang1.
  apply H.
  
  
Qed.

(* Q18. (HARD - OPTIONAL) show that `rmatch` is complete.               *)

Lemma rmatch_complete (r : regexp) (w : word):
  interp r w -> rmatch r w.
Proof. todo. Qed.
