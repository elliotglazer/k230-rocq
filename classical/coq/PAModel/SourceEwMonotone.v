(** Uniform monotonicity of the reflection witness requirement Ew.
    All matrices and free names may be nonstandard PA-model elements. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
  SourceBounded NumericalContexts NumericalEnvironments NumericalSourceFull SourceRawSubset
  SourceBoundedExistsMonotone SourceD0Recipe SourceRelativizationRules
  SourceRelativizationFunctionality SourceContextProofHelpers SourceDerivedRules.
Unset Implicit Arguments.

Definition source_ew_at M domain matrix z out := exists atom left right,
  sf_relation M SFMember (zeroM M)(succM M z) atom /\
  sr_quantifier M false domain matrix left /\sr_quantifier M false atom matrix right /\
  sf_relation M SFImpl left right out.

Theorem source_ew_recipe_at_zero M domain matrix out :
  source_ew_recipe M domain matrix out <->source_ew_at M domain matrix (zeroM M) out.
Proof. reflexivity. Qed.

Theorem source_full_ew_monotone M b c n k domain matrix x y subset ewX ewY :
  context_bounded M b c n k ->source_bounded M domain (succM M k) ->
  source_bounded M matrix (succM M k) ->coding_lt M x k ->coding_lt M y k ->
  source_raw_subset_graph M x y subset ->source_ew_at M domain matrix x ewX ->
  source_ew_at M domain matrix y ewY ->source_full_prv M b c n subset ->
  source_full_prv M b c n ewX ->source_full_prv M b c n ewY.
Proof.
  intros HC HD HM HX HY HS (atomX&left&rightX&HAX&HLeftX&HRightX&HEWX)
    (atomY&left'&rightY&HAY&HLeftY&HRightY&HEWY) PS PX.
  pose proof(sr_quantifier_functional M false domain matrix left left' HLeftX HLeftY) as E. subst left'.
  assert (HLeft:source_bounded M left k) by exact(source_guarded_exists_bounded M domain matrix left k HD HM HLeftX).
  destruct HRightX as (bodyX&HBX&HEX).
  destruct HRightY as (bodyY&HBY&HEY).
  assert (HAYB:source_bounded M atomY (succM M k)).
  { apply(proj2(source_bounded_accept_atom M SFMember _ _ atomY (succM M k) (or_introl eq_refl) HAY)).
    split;[apply coding_zero_lt_succ|]. apply(proj2(FiniteCRT.coding_lt_succ_cancel M y k)),HY. }
  assert (HBodyY:source_bounded M bodyY (succM M k)).
  { exact(proj2(source_bounded_accept_binary M SFAnd atomY matrix bodyY (succM M k)
      (or_introl eq_refl) HBY)(conj HAYB HM)). }
  assert (HRight:source_bounded M rightY k).
  { exact(proj2(source_bounded_accept_unary M SFEx bodyY rightY k (or_intror eq_refl) HEY) HBodyY). }
  assert (HEW:source_bounded M ewY k).
  { exact(proj2(source_bounded_accept_binary M SFImpl left rightY ewY k
      (or_intror(or_intror eq_refl)) HEWY)(conj HLeft HRight)). }
  destruct(environment_cons_total M b c n left) as (ub&uc&un&HCons).
  assert(HBranch:context_bounded M ub uc un k).
  { exact(proj2(context_bounded_cons M b c n left ub uc un k HCons)(conj HLeft HC)). }
  pose proof(source_full_cons_weaken M b c n left ub uc un k ewX HCons HBranch PX) as PWX.
  pose proof(source_full_cons_head M b c n left ub uc un k HCons HLeft HBranch) as PL.
  pose proof(source_full_modus_ponens M ub uc un left rightX ewX HEWX PWX PL) as PRX.
  pose proof(source_full_cons_weaken M b c n left ub uc un k subset HCons HBranch PS) as PSubset.
  pose proof(source_full_bounded_exists_monotone M ub uc un k x y matrix subset
    atomX atomY bodyX bodyY rightX rightY HBranch HM HX HY HS HAX HAY HBX HBY HEX HEY PSubset PRX) as PRY.
  exact(full_source_II M b c n left rightY ewY ub uc un
    (ex_intro _ k (conj HEW HC)) PRY HCons HEWY).
Qed.

Print Assumptions source_full_ew_monotone.
