(** Finite source theorems can be instantiated at arbitrary PA-model names
    in their same closed axiom context. No fresh proof-context collection
    is needed for each different role assignment. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes FixedSourceBounds
 SourceBounded NumericalContexts NumericalContextRenaming NumericalRenamingMaps NumericalRenaming
 NumericalSourceFull SourceProofRenaming SourceRenamingIdentity SourceFiniteParameters SourceFiniteNameParameters.
From Stdlib Require Import Arith.PeanoNat Lia.
Unset Implicit Arguments.
Theorem source_full_finite_parameter_closed_context M phi count rho out b c n:
 context_bounded M b c n(zeroM M) ->source_full_prv M b c n(code_numeral M(sf_encode phi)) ->
 code_relation M rho(source_parameter_expression(source_finite_parameter_names count)phi)out ->
 source_full_prv M b c n out.
Proof.
 intros HC HP HO. destruct(source_finite_names_total M count rho(zeroM M))as(rb&rc&HNames).
 assert(HRename:numerical_renaming M(code_numeral M(sf_encode phi))rb rc(code_numeral M count)(zeroM M)out).
 { apply(source_finite_parameter_renaming M phi(source_finite_parameter_names count)rho rb rc(code_numeral M count)(zeroM M)out);[|exact HO].
   intros i x HX. unfold source_finite_parameter_names in HX.
   destruct(Nat.ltb_spec i count)as[HI|HI].
   - change(x=rho i)in HX. subst x. exact(HNames i HI).
   - change(x=code_numeral M i)in HX. subst x.
     apply(proj2(renaming_lookup_outside M rb rc(code_numeral M count)(zeroM M)(code_numeral M i)(code_numeral M i)
      ltac:(intro H;apply(proj1(fixed_source_numeral_lt_iff M i count))in H;lia))).
     symmetry. apply coding_add_zero_r. }
 assert(HContext:context_renaming M b c n rb rc(code_numeral M count)(zeroM M)b c).
 { intros i f g HI HF HG. assert(E:g=f)by(eapply beta_unique;eassumption). subst g.
   apply(numerical_renaming_identity_on_bound M f rb rc(code_numeral M count)(zeroM M)(zeroM M)
    (HC f(ex_intro _ i(conj HI HF)))).
   intros j HJ. exfalso. exact(coding_not_lt_zero M j HJ). }
 exact(source_full_prv_renaming M b c n(code_numeral M(sf_encode phi))rb rc(code_numeral M count)(zeroM M)b c out HP HContext HRename).
Qed.
Print Assumptions source_full_finite_parameter_closed_context.
