(** Exact two-witness successor syntax for the fresh-leading invariant. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceNumeralLift SourceBounded
 NumericalRenaming SourceQuantifierRules SourceFiniteCutoffShift SourceCutoffShiftConstructors SourceCutoffPropositional
 SourceCutoffQuantifiers SourceDefinabilityPrimitives SourceDefinabilityStep SourceEnvFDomainWitnessFixed
 SourceNumFClosureSyntax SourceFunctionalityShells SourceLeastOrdinalWitness.
Unset Implicit Arguments.
Local Opaque source_def_extension021 ew_extension032 ew_extension143.
Theorem source_envf_witness_structure M p e:
 source_def_step M true p e->exists p1 p2 p3 shifted body shiftedBody envShift,
 source_cutoff_shift M 1 p p1 /\source_cutoff_shift M 1 p1 p2 /\source_cutoff_shift M 1 p2 p3 /\
 source_formula_shift M p3 shifted /\
 sf_relation M SFAnd p3(code_numeral M(sf_encode ew_extension032))body /\sf_relation M SFEx body(zeroM M)envShift /\
 source_formula_shift M e envShift /\
 sf_relation M SFAnd shifted(code_numeral M(sf_encode ew_extension143))shiftedBody /\source_formula_shift M body shiftedBody.
Proof.
 intro HStep. destruct(source_def_step_graph M true p e HStep)as(p2&oldbody&(p1&H1&H2)&HOldBody&HOldEx).
 destruct(source_cutoff_shift_total M 1 p2)as(p3&H3).
 destruct(sf_relation_total M SFAnd p3(code_numeral M(sf_encode ew_extension032)))as(body&HBody).
 destruct(sf_relation_total M SFEx body(zeroM M))as(envShift&HEnvShift).
 destruct(numerical_renaming_total M p3(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shifted&HShifted).
 destruct(sf_relation_total M SFAnd shifted(code_numeral M(sf_encode ew_extension143)))as(shiftedBody&HShiftedBody).
 assert(HFixed:source_cutoff_shift M 1(code_numeral M(sf_encode source_def_extension021))(code_numeral M(sf_encode ew_extension032))).
 { exact(source_cutoff_shift_fixed_source M 1(fun _=>zeroM M)source_def_extension021 _ _
    (source_formula_numeral_graph M source_def_extension021)(source_formula_numeral_graph M ew_extension032)). }
 pose proof(source_cutoff_shift_binary M 1 SFAnd p2(code_numeral M(sf_encode source_def_extension021))oldbody
  p3(code_numeral M(sf_encode ew_extension032))body(or_introl eq_refl)HOldBody HBody H3 HFixed)as HBodyCutoff.
 pose proof(source_cutoff_zero_is_shift M e envShift(source_cutoff_quantifier_join M 0 false oldbody body e envShift HOldEx HEnvShift HBodyCutoff))as HES.
 pose proof(source_formula_shift_conjunction M p3(code_numeral M(sf_encode ew_extension032))body shifted
  (code_numeral M(sf_encode ew_extension143))shiftedBody HBody HShiftedBody HShifted(source_formula_numeral_shift M ew_extension032))as HBS.
 exists p1,p2,p3,shifted,body,shiftedBody,envShift. repeat split;assumption.
Qed.
Print Assumptions source_envf_witness_structure.

