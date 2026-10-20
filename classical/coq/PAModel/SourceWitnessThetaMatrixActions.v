(** Actual diagonal/positive-point matrix alignment. A diagonal substitution
    sends theta's four roles to p; under its existential binder the matrix
    is precisely phi[output0,input(p+1),parameter-tail(delta+1)]. The positive
    point uses the same matrix, by checked substitution composition. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions
  SourceBounded NumericalRenamingMaps NumericalSubstitutionMaps NumericalSubstitution
  RenamingSubstitution SourceSubstitutionComposition SourceWitnessThetaRecipe SourceFiniteCutoffShift.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.

Lemma witness_iter_add M count i :source_succ_iter M count i=addM M(code_numeral M count) i.
Proof. induction count;cbn[source_succ_iter code_numeral];[symmetry;apply Arithmetic.add_zero|].
  now rewrite Arithmetic.add_succ,IHcount. Qed.
Lemma witness_iter_outside M count i :~coding_lt M(source_succ_iter M count i)(code_numeral M count).
Proof.
  induction count;cbn[source_succ_iter code_numeral].
  - exact(coding_not_lt_zero M i).
  - intro H. exact(IHcount(proj1(coding_lt_succ_cancel M _ _) H)).
Qed.
Lemma witness_substitution_tail M b c count base i :substitution_lookup M b c(code_numeral M count) base
  (source_succ_iter M count i)(addM M base i).
Proof. right. split;[apply witness_iter_outside|]. exists i. split;[apply witness_iter_add|reflexivity]. Qed.
Lemma witness_theta_lookup_tail M inside i :renaming_lookup M
  (code_numeral M(witness_theta_dividend inside))(code_numeral M 1)(code_numeral M 2)
  (code_numeral M(witness_theta_delta inside))(succM M(succM M i))
  (source_succ_iter M (witness_theta_tail inside) i).
Proof.
  apply renaming_lookup_outside;[exact(witness_iter_outside M 2 i)|].
  destruct inside;cbn[witness_theta_tail witness_theta_delta source_succ_iter code_numeral];
    rewrite Arithmetic.add_comm;repeat rewrite Arithmetic.add_succ;rewrite Arithmetic.add_zero;reflexivity.
Qed.

Theorem source_witness_theta_negative_matrix_action M phi bound b eb ec delta p lb lc ln rb rc out :
  source_bounded M phi bound ->source_witness_theta_matrix M true phi b ->
  substitution_lookup M eb ec(code_numeral M 4) delta(code_numeral M 1) p ->
  substitution_lift M eb ec(code_numeral M 4) delta lb lc ln ->
  substitution_lookup M rb rc(code_numeral M 2)(succM M delta)(zeroM M)(zeroM M) ->
  substitution_lookup M rb rc(code_numeral M 2)(succM M delta)(code_numeral M 1)(succM M p) ->
  numerical_substitution M b lb lc ln(succM M delta) out ->
  numerical_substitution M phi rb rc(code_numeral M 2)(succM M delta) out.
Proof.
  intros HB HR HOne HL HC0 HC1 HS.
  pose proof(proj1 HL) as EN. change(ln=code_numeral M 5) in EN. subst ln.
  apply(numerical_substitution_composition M phi bound (code_numeral M 2)(code_numeral M 1)
    (code_numeral M 2)(addM M(code_numeral M 2)(code_numeral M 3))
    lb lc(code_numeral M 5)(succM M delta) rb rc(code_numeral M 2)(succM M delta) b out HB).
  - exact(proj1(numerical_renaming_substitution M phi _ _ _ _ b) HR).
  - exact HS.
  - intros i j v _ HA HV.
    apply(proj2(renaming_substitution_lookup M (code_numeral M 2)(code_numeral M 1)
      (code_numeral M 2)(code_numeral M 3) i j)) in HA.
    destruct(@Peano.zero_or_succ (carrier M)(raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i) as[E|[i' E]];subst i.
    + pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HA(witness_theta_lookup_zero M true)) as E. subst j.
      apply(proj1(substitution_lift_head M eb ec(code_numeral M 4) delta lb lc(code_numeral M 5) v HL)) in HV.
      now subst v.
    + destruct(@Peano.zero_or_succ (carrier M)(raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) i') as[E|[i'' E]];subst i'.
      * pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HA(witness_theta_lookup_one M true)) as E. subst j.
        pose proof(proj2(proj2 HL)(code_numeral M 1) p HOne) as HHead.
        pose proof(substitution_lookup_functional M lb lc(code_numeral M 5)(succM M delta)
          (code_numeral M 2) v (succM M p) HV HHead) as E. now subst v.
      * pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HA(witness_theta_lookup_tail M true i'')) as E. subst j.
        pose proof(substitution_lookup_functional M lb lc(code_numeral M 5)(succM M delta) _ v _ HV
          (witness_substitution_tail M lb lc 5(succM M delta) i'')) as E. subst v.
        exact(witness_substitution_tail M rb rc 2(succM M delta) i'').
Qed.

Theorem source_witness_theta_positive_matrix_action M phi bound a eb ec delta p rb rc out :
  source_bounded M phi bound ->source_witness_theta_matrix M false phi a ->
  substitution_lookup M eb ec(code_numeral M 4)(succM M delta)(zeroM M)(zeroM M) ->
  substitution_lookup M eb ec(code_numeral M 4)(succM M delta)(code_numeral M 1)(succM M p) ->
  substitution_lookup M rb rc(code_numeral M 2)(succM M delta)(zeroM M)(zeroM M) ->
  substitution_lookup M rb rc(code_numeral M 2)(succM M delta)(code_numeral M 1)(succM M p) ->
  numerical_substitution M a eb ec(code_numeral M 4)(succM M delta) out ->
  numerical_substitution M phi rb rc(code_numeral M 2)(succM M delta) out.
Proof.
  intros HB HR HZero HOne HC0 HC1 HS.
  apply(numerical_substitution_composition M phi bound (code_numeral M 4)(code_numeral M 1)
    (code_numeral M 2)(addM M(code_numeral M 2)(code_numeral M 2))
    eb ec(code_numeral M 4)(succM M delta) rb rc(code_numeral M 2)(succM M delta) a out HB).
  - exact(proj1(numerical_renaming_substitution M phi _ _ _ _ a) HR).
  - exact HS.
  - intros i j v _ HA HV.
    apply(proj2(renaming_substitution_lookup M (code_numeral M 4)(code_numeral M 1)
      (code_numeral M 2)(code_numeral M 2) i j)) in HA.
    destruct(@Peano.zero_or_succ (carrier M)(raw_interpretation M)
      (fun ax H rho=>axioms M ax rho H) i) as[E|[i' E]];subst i.
    + pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HA(witness_theta_lookup_zero M false)) as E. subst j.
      pose proof(substitution_lookup_functional M eb ec(code_numeral M 4)(succM M delta)
        (zeroM M) v (zeroM M) HV HZero) as E. now subst v.
    + destruct(@Peano.zero_or_succ (carrier M)(raw_interpretation M)
        (fun ax H rho=>axioms M ax rho H) i') as[E|[i'' E]];subst i'.
      * pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HA(witness_theta_lookup_one M false)) as E. subst j.
        pose proof(substitution_lookup_functional M eb ec(code_numeral M 4)(succM M delta)
          (code_numeral M 1) v (succM M p) HV HOne) as E. now subst v.
      * pose proof(renaming_lookup_functional M _ _ _ _ _ j _ HA(witness_theta_lookup_tail M false i'')) as E. subst j.
        pose proof(substitution_lookup_functional M eb ec(code_numeral M 4)(succM M delta) _ v _ HV
          (witness_substitution_tail M eb ec 4(succM M delta) i'')) as E. subst v.
        exact(witness_substitution_tail M rb rc 2(succM M delta) i'').
Qed.

Print Assumptions source_witness_theta_negative_matrix_action.
Print Assumptions source_witness_theta_positive_matrix_action.
