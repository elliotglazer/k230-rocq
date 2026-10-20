(** Instantiating a de Bruijn binder is equivalent to quoting its matrix
    with the selected value prepended to the environment. Both quotations
    here use the same fresh-name base. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs
  SourceBounded NumericalEnvironments NumericalSubstitutionMaps SubstitutionSource
  NumericalInstantiation NumericalQuotation QuotationSubstitution
  SubstitutionEnvironment.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma instantiation_environment_agreement M sb sc t eb ec en y fb fc fn bound :
  substitution_lookup M sb sc (succM M (zeroM M)) (zeroM M) (zeroM M) t ->
  environment_lookup M eb ec en t y -> environment_cons M eb ec en y fb fc fn ->
  substitution_environment_agreement M sb sc (succM M (zeroM M)) (zeroM M)
    eb ec en fb fc fn bound.
Proof.
  intros Hhead Hy HE i u v w Hi Hiu Huv Hiw.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho => axioms M ax rho H) i) as [->|[j ->]].
  - assert (u=t) by
      (exact (substitution_lookup_functional M sb sc (succM M (zeroM M))
        (zeroM M) (zeroM M) u t Hiu Hhead)).
    subst u. assert (v=y) by
      (exact (environment_lookup_functional M eb ec en t v y Huv Hy)).
    subst v. symmetry.
    exact (proj1 (environment_cons_head M eb ec en y fb fc fn w HE) Hiw).
  - assert (u=j) by
      (exact (substitution_lookup_functional M sb sc (succM M (zeroM M))
        (zeroM M) (succM M j) u j Hiu (substitution_singleton_tail M sb sc j))).
    subst u.
    apply (proj1 (environment_cons_tail M eb ec en y fb fc fn j w HE)) in Hiw.
    exact (environment_lookup_functional M eb ec en j v w Huv Hiw).
Qed.

Theorem quotation_instantiation_cons M f t g bound eb ec en y fb fc fn fresh domain v w :
  source_bounded M f bound -> numerical_instantiation M f t g ->
  environment_lookup M eb ec en t y -> environment_cons M eb ec en y fb fc fn ->
  numerical_quotation M f fb fc fn fresh domain v ->
  numerical_quotation M g eb ec en fresh domain w -> v=w.
Proof.
  intros HB [sb [sc [Hhead Hsubst]]] Hy HE Hv Hw.
  apply (numerical_quotation_substitution M f bound sb sc (succM M (zeroM M))
    (zeroM M) eb ec en fb fc fn fresh domain g v w HB).
  - exact (instantiation_environment_agreement M sb sc t eb ec en y fb fc fn bound
      Hhead Hy HE).
  - exact Hsubst.
  - exact Hv.
  - exact Hw.
Qed.

Print Assumptions instantiation_environment_agreement.
Print Assumptions quotation_instantiation_cons.
