(** Any externally finite list of model-valued source variable names has a
    genuine internally coded renaming. No choice is needed. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes FixedSourceBounds
  NumericalEnvironments NumericalRenamingMaps SourceFiniteParameters SourceFiniteParameterProofs
  SourceDescriptorProvability.
From Stdlib Require Import Arith.PeanoNat Lia.
Unset Implicit Arguments.

Theorem source_finite_names_total M count :forall rho delta,exists b c,forall i,
  (i<count)%nat ->renaming_lookup M b c(code_numeral M count) delta(code_numeral M i)(rho i).
Proof.
  induction count as [|count IH];intros rho delta.
  - exists(zeroM M),(zeroM M). intros i HI. lia.
  - destruct(IH(fun i=>rho(S i)) delta) as (b&c&HP).
    destruct(environment_cons_total M b c(code_numeral M count)(rho 0)) as (d&e&n&HCons).
    assert(EN:n=code_numeral M(S count)) by exact(proj1 HCons). subst n.
    exists d,e. intros [|i] HI.
    + apply(proj2(renaming_lookup_inside M d e(code_numeral M(S count)) delta
        (zeroM M)(rho 0)(coding_zero_lt_succ M(code_numeral M count)))).
      apply(proj1(environment_lookup_inside M d e(code_numeral M(S count))(zeroM M)(rho 0)
        (coding_zero_lt_succ M(code_numeral M count)))). exact(proj1(proj2 HCons)).
    + assert(HI':(i<count)%nat) by lia.
      pose proof(proj2(fixed_source_numeral_lt_iff M i count) HI') as HOldLt.
      pose proof(proj2(fixed_source_numeral_lt_iff M(S i)(S count)) HI) as HNewLt.
      apply(proj2(renaming_lookup_inside M d e _ delta _ _ HNewLt)).
      apply(proj1(environment_lookup_inside M d e _ _ _ HNewLt)).
      apply(proj2(proj2 HCons)).
      apply(proj2(environment_lookup_inside M b c _ _ _ HOldLt)).
      exact(proj1(renaming_lookup_inside M b c _ delta _ _ HOldLt)(HP i HI')).
Qed.

Definition source_finite_parameter_names count i :=if Nat.ltb i count then CEvar i else CEconst i.

Theorem source_descriptor_finite_parameter_proof M T phi count rho out :
  source_descriptor_provable M T(code_numeral M(sf_encode phi)) ->
  code_relation M rho(source_parameter_expression(source_finite_parameter_names count) phi) out ->
  source_descriptor_provable M T out.
Proof.
  intros HP HO.
  destruct(source_finite_names_total M count rho(zeroM M)) as (b&c&HNames).
  apply(source_descriptor_parameter_proof M T phi(source_finite_parameter_names count) rho
    b c(code_numeral M count)(zeroM M) out HP);[|exact HO].
  intros i x HX. unfold source_finite_parameter_names in HX.
  destruct(Nat.ltb_spec i count) as [HI|HI].
  - change(x=rho i) in HX. subst x. exact(HNames i HI).
  - change(x=code_numeral M i) in HX. subst x.
    assert(HOutside:~coding_lt M(code_numeral M i)(code_numeral M count)).
    { intro H. apply(proj1(fixed_source_numeral_lt_iff M i count)) in H. lia. }
    apply(proj2(renaming_lookup_outside M b c(code_numeral M count)(zeroM M)
      (code_numeral M i)(code_numeral M i) HOutside)). symmetry. apply coding_add_zero_r.
Qed.

Print Assumptions source_finite_names_total.
Print Assumptions source_descriptor_finite_parameter_proof.
