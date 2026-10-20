(** An internally beta-certified partial substitution, with conservative
    capture rejection. This file constructs numerical syntax, not a K proof. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs NumericalTraces SentenceBounds CodeDescent CodeTags
  FreshNames FreshPropagation NamedSubstitutionRules.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
From Stdlib Require Import Lia.
Unset Implicit Arguments.

Definition named_substitution M f x y v := exists r,
  named_sub_row M f x y v r /\ trace_derives M named_sub_rules r.
Definition named_substitution_formula (f x y v : term) : form :=
  ∃ (named_sub_row_formula f`[↑] x`[↑] y`[↑] v`[↑] $0 ∧
    trace_derives_formula named_sub_rules $0).
Local Opaque holds named_sub_row_formula trace_derives_formula.
Lemma named_substitution_formula_correct M rho f x y v :
  holds M rho (named_substitution_formula f x y v) <->
  named_substitution M (evalM M rho f) (evalM M rho x) (evalM M rho y) (evalM M rho v).
Proof.
  unfold named_substitution_formula,named_substitution.
  setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite named_sub_row_correct. setoid_rewrite trace_derives_formula_correct.
  unfold evalM. now setoid_rewrite eval_up.
Qed.
Lemma named_substitution_formula_bound :
  bounded 4 (named_substitution_formula $0 $1 $2 $3).
Proof. apply formula_boundb_sound;vm_compute;reflexivity. Qed.

Lemma named_substitution_leaf M f x y v :
  named_sub_leaf M f x y v -> named_substitution M f x y v.
Proof.
  intro H. destruct (named_sub_row_total M f x y v) as [r Hr].
  exists r. split;[exact Hr|]. apply trace_derives_base.
  apply named_sub_rule_base. exists f,x,y,v. auto.
Qed.
Lemma named_substitution_stop M f x y :
  named_sub_stop M f x y -> named_substitution M f x y f.
Proof. intro H. apply named_substitution_leaf. left;auto. Qed.
Theorem named_substitution_identity M f x : named_substitution M f x x f.
Proof. apply named_substitution_stop;now left. Qed.
Theorem named_substitution_zero M x y :
  named_substitution M (zeroM M) x y (zeroM M).
Proof. apply named_substitution_stop;right;now left. Qed.
Theorem named_substitution_binder_stop M x a f y :
  tagged_pair_graph M 2 x a f -> named_substitution M f x y f.
Proof. intro H. apply named_substitution_stop;right;right;now exists a. Qed.

Theorem named_substitution_atom_intro M eq a b f x y a' b' v :
  x<>y -> tagged_pair_graph M (named_atom_tag eq) a b f ->
  named_replace M x y a a' -> named_replace M x y b b' ->
  tagged_pair_graph M (named_atom_tag eq) a' b' v -> named_substitution M f x y v.
Proof.
  intros Hxy Hf Ha Hb Hv. apply named_substitution_leaf. right;split;[exact Hxy|].
  assert (H : named_sub_atom M eq f x y v) by (exists a,b,a',b';auto).
  destruct eq;tauto.
Qed.
Theorem named_substitution_unary_intro M a b f x y w v :
  x<>y -> a<>x -> a<>y -> tagged_pair_graph M 2 a b f ->
  named_substitution M b x y w -> tagged_pair_graph M 2 a w v ->
  named_substitution M f x y v.
Proof.
  intros Hxy Hax Hay Hf [p [Hp Hdp]] Hv.
  destruct (named_sub_row_total M f x y v) as [r Hr].
  exists r. split;[exact Hr|]. apply (trace_derives_unary M named_sub_rules r p Hdp).
  apply named_sub_rule_unary. exists f,x,y,v. split;[exact Hr|].
  exists a,b,w;tauto.
Qed.
Theorem named_substitution_binary_intro M a b f x y a' b' v :
  x<>y -> f<>zeroM M -> tagged_pair_graph M 0 a b f ->
  named_substitution M a x y a' -> named_substitution M b x y b' ->
  tagged_pair_graph M 0 a' b' v -> named_substitution M f x y v.
Proof.
  intros Hxy Hnz Hf [p [Hp Hdp]] [q [Hq Hdq]] Hv.
  destruct (named_sub_row_total M f x y v) as [r Hr].
  exists r. split;[exact Hr|]. apply (trace_derives_binary M named_sub_rules r p q Hdp Hdq).
  apply named_sub_rule_binary. exists f,x,y,v. split;[exact Hr|].
  exists a,b,a',b';tauto.
Qed.

Theorem named_substitution_cases M f x y v : named_substitution M f x y v ->
  named_sub_leaf M f x y v \/
  (exists a b w,x<>y /\ a<>x /\ a<>y /\ tagged_pair_graph M 2 a b f /\
    named_substitution M b x y w /\ tagged_pair_graph M 2 a w v) \/
  (exists a b a' b',x<>y /\ f<>zeroM M /\ tagged_pair_graph M 0 a b f /\
    named_substitution M a x y a' /\ named_substitution M b x y b' /\
    tagged_pair_graph M 0 a' b' v).
Proof.
  intros [r [Hr Htrace]].
  destruct (trace_derives_inv M named_sub_rules r Htrace)
    as [Hb|[[p [Hp Hu]]|[p [q [Hp [Hq Hb]]]]]].
  - apply named_sub_rule_base in Hb. destruct Hb as [f' [x' [y' [v' [Hr' Hleaf]]]]].
    destruct (named_sub_row_injective M f x y v f' x' y' v' r Hr Hr') as [-> [-> [-> ->]]].
    now left.
  - apply named_sub_rule_unary in Hu. destruct Hu as [f' [x' [y' [v' [Hr' Hcase]]]]].
    destruct (named_sub_row_injective M f x y v f' x' y' v' r Hr Hr') as [-> [-> [-> ->]]].
    destruct Hcase as [a [b [w [Hxy [Hax [Hay [Hf [Hrow Hv]]]]]]]].
    right;left;exists a,b,w. repeat split;try assumption. exists p;auto.
  - apply named_sub_rule_binary in Hb. destruct Hb as [f' [x' [y' [v' [Hr' Hcase]]]]].
    destruct (named_sub_row_injective M f x y v f' x' y' v' r Hr Hr') as [-> [-> [-> ->]]].
    destruct Hcase as [a [b [a' [b' [Hxy [Hnz [Hf [Hrowa [Hrowb Hv]]]]]]]]].
    right;right;exists a,b,a',b'. repeat split;try assumption.
    + exists p;auto.
    + exists q;auto.
Qed.

Definition named_substitution_total_formula : form :=
  ∀∀ (formula_fresh_formula $2 $0 → ∃ named_substitution_formula $3 $2 $1 $0).
Local Opaque formula_fresh_formula named_substitution_formula.
Lemma named_substitution_total_definable M : Definable1 M
  (fun f => forall x y,formula_fresh M f y -> exists v,named_substitution M f x y v).
Proof.
  exists named_substitution_total_formula,(fun _ => zeroM M).
  intro f. unfold named_substitution_total_formula.
  repeat setoid_rewrite holds_all. setoid_rewrite holds_imp. setoid_rewrite holds_ex.
  setoid_rewrite formula_fresh_formula_correct. setoid_rewrite named_substitution_formula_correct.
  reflexivity.
Qed.

Theorem named_substitution_fresh_total M f x y :
  formula_fresh M f y -> exists v,named_substitution M f x y v.
Proof.
  revert f x y. apply (formula_code_induction M
    (fun f => forall x y,formula_fresh M f y -> exists v,named_substitution M f x y v)).
  - apply named_substitution_total_definable.
  - intros x y _. exists (zeroM M). apply named_substitution_zero.
  - intros a b f Hf x y _.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + exists f;apply named_substitution_identity.
    + destruct (named_replace_total M x y a) as [a' Ha].
      destruct (named_replace_total M x y b) as [b' Hb].
      destruct (tagged_pair_total M 1 a' b') as [v Hv].
      exists v. exact (named_substitution_atom_intro M false a b f x y a' b' v Hxy Hf Ha Hb Hv).
  - intros a b f Hf x y _.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + exists f;apply named_substitution_identity.
    + destruct (named_replace_total M x y a) as [a' Ha].
      destruct (named_replace_total M x y b) as [b' Hb].
      destruct (tagged_pair_total M 3 a' b') as [v Hv].
      exists v. exact (named_substitution_atom_intro M true a b f x y a' b' v Hxy Hf Ha Hb Hv).
  - intros a b f Hnz Hf IHa IHb x y Hfresh.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + exists f;apply named_substitution_identity.
    + destruct (formula_fresh_implication_tagged M a b f y Hnz Hf Hfresh) as [Hfa Hfb].
      destruct (IHa x y Hfa) as [a' Ha]. destruct (IHb x y Hfb) as [b' Hb].
      destruct (tagged_pair_total M 0 a' b') as [v Hv].
      exists v. exact (named_substitution_binary_intro M a b f x y a' b' v Hxy Hnz Hf Ha Hb Hv).
  - intros a b f Hf IHb x y Hfresh.
    destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
      (fun ax H rho => axioms M ax rho H) x y) as [->|Hxy].
    + exists f;apply named_substitution_identity.
    + destruct (@Peano.D_eq_dec (carrier M) (raw_interpretation M)
        (fun ax H rho => axioms M ax rho H) a x) as [->|Hax].
      * exists f;eapply named_substitution_binder_stop;exact Hf.
      * destruct (formula_fresh_universal_tagged M a b f y Hf Hfresh) as [Hay Hfb].
        destruct (IHb x y Hfb) as [w Hw]. destruct (tagged_pair_total M 2 a w) as [v Hv].
        exists v. exact (named_substitution_unary_intro M a b f x y w v Hxy Hax Hay Hf Hw Hv).
Qed.
