(** Instantiation of an outer de Bruijn binder by one variable. The graph
    existentially hides the beta representation of its one-entry prefix. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SentenceBounds SetFormulaCodes SourceBounded StandardModel
  NumericalSubstitutionMaps NumericalSubstitution SubstitutionSource
  SourceSubstitutionBounds.
From FOL Require Import FullSyntax Arithmetics.
From Undecidability.FOL Require Import Syntax.BinSig Sets.Signatures.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Definition numerical_instantiation M f t g := exists b c,
  substitution_lookup M b c (succM M (zeroM M)) (zeroM M) (zeroM M) t /\
  numerical_substitution M f b c (succM M (zeroM M)) (zeroM M) g.

Definition numerical_instantiation_formula (f t g : term) : form :=
  ∃∃ (substitution_lookup_formula $1 $0 (σ zero) zero zero (t`[↑]`[↑]) ∧
    numerical_substitution_formula (f`[↑]`[↑]) $1 $0 (σ zero) zero (g`[↑]`[↑])).

Local Opaque holds substitution_lookup_formula numerical_substitution_formula.
Lemma numerical_instantiation_formula_correct M rho f t g :
  holds M rho (numerical_instantiation_formula f t g) <->
  numerical_instantiation M (evalM M rho f) (evalM M rho t) (evalM M rho g).
Proof.
  unfold numerical_instantiation_formula,numerical_instantiation.
  repeat setoid_rewrite holds_ex. setoid_rewrite holds_and.
  setoid_rewrite substitution_lookup_formula_correct.
  setoid_rewrite numerical_substitution_formula_correct.
  unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Lemma numerical_instantiation_formula_bound :
  bounded 3 (numerical_instantiation_formula $0 $1 $2).
Proof. apply formula_boundb_sound. vm_compute. reflexivity. Qed.

Theorem numerical_instantiation_total M f t : exists g, numerical_instantiation M f t g.
Proof.
  destruct (substitution_singleton_total M t) as [b [c [Hhead _]]].
  destruct (numerical_substitution_total M f b c (succM M (zeroM M)) (zeroM M)) as [g Hg].
  exists g,b,c. auto.
Qed.

Lemma substitution_singletons_equivalent M b c d e t :
  substitution_lookup M b c (succM M (zeroM M)) (zeroM M) (zeroM M) t ->
  substitution_lookup M d e (succM M (zeroM M)) (zeroM M) (zeroM M) t ->
  substitution_equivalent M b c (succM M (zeroM M)) d e (succM M (zeroM M)) (zeroM M).
Proof.
  intros Hb Hd i v.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [Ei|[i' Ei]]; subst i.
  - split; intro Hv.
    + assert (E : v=t) by (eapply substitution_lookup_functional; eassumption).
      now subst v.
    + assert (E : v=t) by (eapply substitution_lookup_functional; eassumption).
      now subst v.
  - split; intro Hv.
    + assert (E : v=i').
      { eapply substitution_lookup_functional; [exact Hv|apply substitution_singleton_tail]. }
      subst v. apply substitution_singleton_tail.
    + assert (E : v=i').
      { eapply substitution_lookup_functional; [exact Hv|apply substitution_singleton_tail]. }
      subst v. apply substitution_singleton_tail.
Qed.

Theorem numerical_instantiation_functional M f t g h :
  numerical_instantiation M f t g -> numerical_instantiation M f t h -> g=h.
Proof.
  intros [b [c [Hb Hg]]] [d [e [Hd Hh]]].
  apply (numerical_substitution_functional_equivalent M f b c (succM M (zeroM M))
    d e (succM M (zeroM M)) (zeroM M) g h); [|exact Hg|exact Hh].
  exact (substitution_singletons_equivalent M b c d e t Hb Hd).
Qed.

Theorem numerical_instantiation_bounded M f t g k :
  source_bounded M f (succM M k) -> coding_lt M t k ->
  numerical_instantiation M f t g -> source_bounded M g k.
Proof.
  intros Hf Ht [b [c [Hhead Hg]]].
  exact (numerical_substitution_singleton_bound M f b c t k g Hf Ht Hhead Hg).
Qed.

Theorem numerical_instantiation_standard_exact (phi : sf_form) (t : sf_term) g :
  numerical_instantiation natModel (sf_encode phi) (sf_index t) g <->
  g=sf_encode (subst_form (t .: var) phi).
Proof.
  split.
  - intros [b [c [Hhead Hg]]].
    exact (proj1 (standard_singleton_substitution_exact phi t b c g Hhead) Hg).
  - intro E. destruct (substitution_singleton_total natModel (sf_index t)) as [b [c [Hhead _]]].
    exists b,c. split; [exact Hhead|].
    exact (proj2 (standard_singleton_substitution_exact phi t b c g Hhead) E).
Qed.

Print Assumptions numerical_instantiation_formula_correct.
Print Assumptions numerical_instantiation_formula_bound.
Print Assumptions numerical_instantiation_total.
Print Assumptions numerical_instantiation_functional.
Print Assumptions numerical_instantiation_bounded.
Print Assumptions numerical_instantiation_standard_exact.
