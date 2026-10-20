(** Relativize an actual pure source theorem into any bounded target
    context that actually proves the required finite domain table. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalInstantiation NumericalContexts NumericalSourceFull
  SourceRelativization SourceRelativeFullTranslation SourceRelativeContexts
  SourceHypothesisTransport SourceContextTransport.
Unset Implicit Arguments.

Theorem source_pure_relative_rule M domain f :
  source_bounded M domain (code_numeral M 1) ->
  source_full_prv M (zeroM M)(zeroM M)(zeroM M) f ->
  exists bound,forall k b c n relative,
    coding_lt M bound (succM M k) ->source_context_finite_bound M b c n ->
    (forall i di,coding_lt M i k ->numerical_instantiation M domain i di ->
      source_full_prv M b c n di) ->
    source_relativization M domain f relative ->source_full_prv M b c n relative.
Proof.
  intros HD HP.
  destruct (source_full_relativized_proof M domain HD (zeroM M)(zeroM M)(zeroM M) f HP)
    as [bound HTranslate].
  exists bound. intros k b c n relative HB HC HDom HR.
  destruct (source_relative_context_total M domain (zeroM M)(zeroM M)(zeroM M) k)
    as [u [v [l HContext]]].
  apply (source_full_prv_replace_hypotheses M b c n HC l u v relative).
  - exact (HTranslate k u v l relative HB HContext HR).
  - intros h HH.
    apply (proj1 (source_relative_context_member_iff M domain (zeroM M)(zeroM M)(zeroM M)
      k u v l h HContext)) in HH.
    destruct HH as [[g [HG _]]|[i [HI HDI]]].
    + exfalso. exact (context_empty M (zeroM M)(zeroM M) g HG).
    + exact (HDom i h HI HDI).
Qed.

Print Assumptions source_pure_relative_rule.
