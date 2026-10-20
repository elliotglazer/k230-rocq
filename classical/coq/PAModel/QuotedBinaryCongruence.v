(** The two selected arguments of a quoted binary source predicate may be
    replaced by supported quotient-equivalent representatives. All parameter
    entries are held fixed. Variable 0 is the output and variable 1 the input. *)
From PAModel Require Import Model FiniteCoding CodeExpressions
  NumericalEnvironments NumericalQuotation QuotationHygiene SourceBounded
  SupportedQuotientEnvironments StableContextSupport RawQuotientAtomCongruence
  ActualMixedQuotationCongruence ContextualEquivalence QuotedUnaryCongruence.
Unset Implicit Arguments.

Theorem supported_quotient_environments_prepend_two M
    eb ec en fb fc fn count t cb cc cn
    input input' output output'
    ib ic il ib' ic' il' ob oc ol ob' oc' ol' :
  supported_quotient_environments M eb ec en fb fc fn count t cb cc cn ->
  supported_quotient_pair M cb cc cn t input input' ->
  supported_quotient_pair M cb cc cn t output output' ->
  environment_cons M eb ec en input ib ic il ->
  environment_cons M fb fc fn input' ib' ic' il' ->
  environment_cons M ib ic il output ob oc ol ->
  environment_cons M ib' ic' il' output' ob' oc' ol' ->
  supported_quotient_environments M ob oc ol ob' oc' ol'
    (succM M (succM M count)) t cb cc cn.
Proof.
  intros HT HI HO HIL HIR HOL HOR.
  apply (supported_quotient_environments_cons_related M ib ic il ib' ic' il'
    (succM M count) t cb cc cn output output' ob oc ol ob' oc' ol').
  - exact (supported_quotient_environments_cons_related M eb ec en fb fc fn
      count t cb cc cn input input' ib ic il ib' ic' il' HT HI HIL HIR).
  - exact HO.
  - exact HOL.
  - exact HOR.
Qed.

Theorem quoted_binary_congruence M phi count eb ec en
    input input' output output'
    ib ic il ib' ic' il' ob oc ol ob' oc' ol'
    k l t cb cc cn marker marker_name f g :
  source_bounded M phi (succM M (succM M count)) ->
  raw_empty_marker_graph M t marker_name marker ->
  stable_context_support M cb cc cn marker ->
  supported_quotient_pair M cb cc cn t input input' ->
  supported_quotient_pair M cb cc cn t output output' ->
  environment_cons M eb ec en input ib ic il ->
  environment_cons M eb ec en input' ib' ic' il' ->
  environment_cons M ib ic il output ob oc ol ->
  environment_cons M ib' ic' il' output' ob' oc' ol' ->
  quotation_safe M ob oc ol k t -> quotation_safe M ob' oc' ol' l t ->
  numerical_quotation M phi ob oc ol k t f ->
  numerical_quotation M phi ob' oc' ol' l t g ->
  contextual_equivalence M cb cc cn f g.
Proof.
  intros HB HMarker HM HI HO HIL HIR HOL HOR HK HL HF HG.
  apply (actual_mixed_quotation_congruence M cb cc cn t marker marker_name
    HMarker HM phi (succM M (succM M count)) ob oc ol ob' oc' ol' k l f g
    HB HK HL);[|exact HF|exact HG].
  exact (supported_quotient_environments_prepend_two M eb ec en eb ec en
    count t cb cc cn input input' output output'
    ib ic il ib' ic' il' ob oc ol ob' oc' ol'
    (supported_quotient_environments_refl M eb ec en count t cb cc cn)
    HI HO HIL HIR HOL HOR).
Qed.

Print Assumptions supported_quotient_environments_prepend_two.
Print Assumptions quoted_binary_congruence.
