(** Absence of a named binder, defined over internally finite syntax paths.
    A name may occur freely while satisfying this predicate. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  NumericalProofs CodeDescent CodeTags FreshNames FreshPropagation
  NamedSubstitutionRules NamedSubstitution.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Definition named_binder_absent M f y := forall g b,
  formula_reaches M f g -> ~tagged_pair_graph M 2 y b g.
Definition named_binder_absent_formula (f y : term) : form :=
  ∀∀ (formula_reaches_formula (code_lift2 f) $1 →
    ¬ tagged_pair_formula 2 (code_lift2 y) $0 $1).
Local Opaque holds formula_reaches_formula tagged_pair_formula.
Lemma named_binder_absent_formula_correct M rho f y :
  holds M rho (named_binder_absent_formula f y) <->
  named_binder_absent M (evalM M rho f) (evalM M rho y).
Proof.
  unfold named_binder_absent_formula,named_binder_absent.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite formula_reaches_formula_correct. setoid_rewrite tagged_pair_formula_correct.
  setoid_rewrite code_eval_lift2. reflexivity.
Qed.
Lemma named_binder_absent_child M f a y :
  formula_edge M f a -> named_binder_absent M f y -> named_binder_absent M a y.
Proof.
  intros He H g b Hg. apply (H g b). exact (formula_reaches_step M f a g He Hg).
Qed.
Lemma named_binder_absent_root M a b f y :
  tagged_pair_graph M 2 a b f -> named_binder_absent M f y -> a<>y.
Proof. intros Hf H ->. exact (H f b (formula_reaches_self M f) Hf). Qed.
Lemma named_formula_fresh_binder_absent M f y :
  formula_fresh M f y -> named_binder_absent M f y.
Proof.
  intros Hfresh g b Hreach Hb. apply (Hfresh y);[|reflexivity].
  exists g. split;[exact Hreach|]. exists y,b. right;auto.
Qed.

Local Opaque named_binder_absent_formula named_substitution_formula.
Lemma named_substitution_binder_total_definable M : Definable1 M
  (fun f => forall x y,named_binder_absent M f y -> exists v,named_substitution M f x y v).
Proof.
  exists (∀∀ (named_binder_absent_formula $2 $0 → ∃ named_substitution_formula $3 $2 $1 $0)),
    (fun _ => zeroM M).
  intro f. repeat setoid_rewrite holds_all. setoid_rewrite holds_imp. setoid_rewrite holds_ex.
  setoid_rewrite named_binder_absent_formula_correct. setoid_rewrite named_substitution_formula_correct.
  reflexivity.
Qed.

Theorem named_substitution_binder_absent_total M f x y :
  named_binder_absent M f y -> exists v,named_substitution M f x y v.
Proof.
  revert f x y. apply (formula_code_induction M
    (fun f => forall x y,named_binder_absent M f y -> exists v,named_substitution M f x y v)).
  - apply named_substitution_binder_total_definable.
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
    + assert (Hfa : named_binder_absent M a y).
      { apply (named_binder_absent_child M f a y);[|exact Hfresh]. exists a,b;left;auto. }
      assert (Hfb : named_binder_absent M b y).
      { apply (named_binder_absent_child M f b y);[|exact Hfresh]. exists a,b;left;auto. }
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
      * pose proof (named_binder_absent_root M a b f y Hf Hfresh) as Hay.
        assert (Hfb : named_binder_absent M b y).
        { apply (named_binder_absent_child M f b y);[|exact Hfresh]. exists a,b;right;auto. }
        destruct (IHb x y Hfb) as [w Hw]. destruct (tagged_pair_total M 2 a w) as [v Hv].
        exists v. exact (named_substitution_unary_intro M a b f x y w v Hxy Hax Hay Hf Hw Hv).
Qed.
