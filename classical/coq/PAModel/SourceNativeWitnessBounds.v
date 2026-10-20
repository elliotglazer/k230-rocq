(** Literal name bounds for the native witness matrix and reflected request. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceWitnessThetaInstances SourceWitnessThetaMatrixActions SourceFiniteCutoffShift SourceSubstitutionBounds
 SourceReflectedRequestLink SourceRelativizationBounds SourceRelativizationRules SourceSetRelativizationRules
 NumericalSubstitutionMaps NumericalSubstitution SourceQuantifierRules SourceTraceMatrixAlignment.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Theorem source_native_witness_matrix_bound M phi n rb rc matrix k:
 source_bounded M phi(succM M(succM M n))->source_witness_matrix_map M(zeroM M)(code_numeral M 3)rb rc->
 numerical_substitution M phi rb rc(code_numeral M 2)(code_numeral M 4)matrix->
 (forall j,coding_lt M j n->coding_lt M(addM M j(code_numeral M 2))k)->
 source_bounded M matrix(succM M(succM M k)).
Proof.
 intros BP HM HSub HNames. apply(numerical_substitution_preserves_bound M phi rb rc(code_numeral M 2)
  (code_numeral M 4)matrix(succM M(succM M n))(succM M(succM M k))BP HSub).
 intros i name HI HName. destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
  (fun ax H rho=>axioms M ax rho H)i)as[->|[i' ->]].
 - pose proof(substitution_lookup_functional M _ _ _ _ _ name _ HName(HM 0 ltac:(auto)))as E;subst name. apply coding_zero_lt_succ.
 - destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)
    (fun ax H rho=>axioms M ax rho H)i')as[->|[j ->]].
   + pose proof(substitution_lookup_functional M _ _ _ _ _ name _ HName(HM 1 ltac:(auto)))as E;subst name.
     apply(proj2(coding_lt_succ_cancel M(zeroM M)(succM M k))). apply coding_zero_lt_succ.
   + pose proof(substitution_lookup_functional M _ _ _ _ _ name _ HName
      (witness_substitution_tail M rb rc 2(code_numeral M 4)j))as E;subst name.
     apply(proj1(coding_lt_succ_cancel M _ _))in HI. apply(proj1(coding_lt_succ_cancel M _ _))in HI.
     pose proof(HNames j HI)as HJ. cbn[code_numeral]. repeat rewrite Arithmetic.add_succ.
     repeat rewrite Arithmetic.add_zero. apply(proj2(coding_lt_succ_cancel M _ _)). apply(proj2(coding_lt_succ_cancel M _ _)).
     rewrite Arithmetic.add_comm in HJ. cbn[code_numeral]in HJ. repeat rewrite Arithmetic.add_succ in HJ.
     repeat rewrite Arithmetic.add_zero in HJ. exact HJ.
Qed.
Theorem source_reflected_request_bound M domain carrier matrix request k:
 source_bounded M domain(code_numeral M 1)->source_bounded M matrix(succM M k)->coding_lt M carrier k->
 source_reflected_request_recipe M domain carrier matrix request->source_bounded M request k.
Proof.
 intros HD BM HY(left&some&bounded&HL&HSome&HBounded&HOut).
 pose proof(source_relativization_preserves_bound M matrix domain(succM M k)left HD BM HL)as BL.
 destruct HSome as(body&HAnd&HEx). destruct HBounded as(guard&pair&HMember&HPair&HBoundEx).
 assert(BGuard:source_bounded M guard(succM M k)).
 { apply(proj2(source_bounded_accept_atom M SFMember(zeroM M)(succM M carrier)guard(succM M k)(or_introl eq_refl)HMember)).
   exact(conj(coding_zero_lt_succ M k)(proj2(coding_lt_succ_cancel M carrier k)HY)). }
 pose proof(sr_domain_bound_succ M domain k HD)as BD.
 pose proof(proj2(source_bounded_accept_binary M SFAnd domain left body(succM M k)(or_introl eq_refl)HAnd)(conj BD BL))as BBody.
 pose proof(proj2(source_bounded_accept_binary M SFAnd guard left pair(succM M k)(or_introl eq_refl)HPair)(conj BGuard BL))as BPair.
 exact(proj2(source_bounded_accept_binary M SFImpl some bounded request k(or_intror(or_intror eq_refl))HOut)
  (conj(proj2(source_bounded_accept_unary M SFEx body some k(or_intror eq_refl)HEx)BBody)
   (proj2(source_bounded_accept_unary M SFEx pair bounded k(or_intror eq_refl)HBoundEx)BPair))).
Qed.
Print Assumptions source_native_witness_matrix_bound.
Print Assumptions source_reflected_request_bound.
