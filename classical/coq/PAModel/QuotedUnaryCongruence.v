(** Quoted source predicates respect deqv in their selected element. The
    remaining environment entries stay literally identical; no quotient
    reflexivity assumption is needed for those parameters. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions
  NumericalEnvironments NumericalQuotation QuotationHygiene SourceBounded
  SupportedQuotientEnvironments StableContextSupport RawQuotientAtomCongruence
  ActualMixedQuotationCongruence ContextualEquivalence.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Theorem supported_quotient_environments_cons_related M eb ec en fb fc fn bound t cb cc cn
    x y xb xc xn yb yc yn :
  supported_quotient_environments M eb ec en fb fc fn bound t cb cc cn ->
  supported_quotient_pair M cb cc cn t x y ->
  environment_cons M eb ec en x xb xc xn -> environment_cons M fb fc fn y yb yc yn ->
  supported_quotient_environments M xb xc xn yb yc yn (succM M bound) t cb cc cn.
Proof.
  intros HE HP HX HY i u v Hi HU HV.
  destruct (@Peano.zero_or_succ (carrier M) (raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H) i) as [->|[j ->]].
  - apply (proj1 (environment_cons_head M eb ec en x xb xc xn u HX)) in HU.
    apply (proj1 (environment_cons_head M fb fc fn y yb yc yn v HY)) in HV.
    now subst u v.
  - exact (HE j u v (proj1 (coding_lt_succ_cancel M j bound) Hi)
      (proj1 (environment_cons_tail M eb ec en x xb xc xn j u HX) HU)
      (proj1 (environment_cons_tail M fb fc fn y yb yc yn j v HY) HV)).
Qed.

Theorem quoted_unary_congruence M phi count eb ec en x y xb xc xn yb yc yn
    k l t cb cc cn marker marker_name f g :
  source_bounded M phi (succM M count) ->
  raw_empty_marker_graph M t marker_name marker -> stable_context_support M cb cc cn marker ->
  supported_quotient_pair M cb cc cn t x y ->
  environment_cons M eb ec en x xb xc xn -> environment_cons M eb ec en y yb yc yn ->
  quotation_safe M xb xc xn k t -> quotation_safe M yb yc yn l t ->
  numerical_quotation M phi xb xc xn k t f -> numerical_quotation M phi yb yc yn l t g ->
  contextual_equivalence M cb cc cn f g.
Proof.
  intros HB HMarker HM HP HX HY HK HL HF HG.
  apply (actual_mixed_quotation_congruence M cb cc cn t marker marker_name HMarker HM
    phi (succM M count) xb xc xn yb yc yn k l f g HB HK HL);[|exact HF|exact HG].
  exact (supported_quotient_environments_cons_related M eb ec en eb ec en count t cb cc cn
    x y xb xc xn yb yc yn (supported_quotient_environments_refl M eb ec en count t cb cc cn) HP HX HY).
Qed.

Print Assumptions supported_quotient_environments_cons_related.
Print Assumptions quoted_unary_congruence.
