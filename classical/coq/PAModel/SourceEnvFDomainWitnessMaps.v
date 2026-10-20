(** The commuting square needed when the fresh numeral witness is inserted
    before an internally long EnvF parameter block. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions SourceBounded
 NumericalSubstitutionMaps NumericalSubstitution NumericalRenamingMaps NumericalRenaming NumericalContextRenaming
 SourceQuantifierRules SourceRenamingSquare SourceFiniteCutoffShift SourceCutoffShiftCommutation SourceBoundedMapComposition
 SourceD0Recipe SourceQfFunctionality SourceDescriptorProvability SourceDescriptorClosure SourceSetTheoryDescriptors SourceZFRProvability.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
Theorem source_shift_cutoff_one_two M f first shifted out k:
 source_bounded M f k->source_cutoff_shift M 1 f first->source_formula_shift M f shifted->
 source_formula_shift M first out->source_cutoff_shift M 2 shifted out.
Proof.
 intros HB(sb&sc&sn&HSM&HS)HR HT. destruct(source_cutoff_shift_map_total M 2)as(ub&uc&un&HUM).
 exists ub,uc,un. split;[exact HUM|].
 apply(numerical_source_renaming_square M f k sb sc sn(code_numeral M 2)
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
  (zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
  ub uc un(code_numeral M 3)first shifted out HB HS HR HT).
 intros i j l m HI HSJ HTM HRL. apply context_shift_lookup in HTM,HRL. subst l m.
 destruct(@Peano.zero_or_succ(carrier M)(raw_interpretation M)(fun ax H rho=>axioms M ax rho H)i)as[E|[idx E]];subst i.
 - assert(E:j=zeroM M)by(exact(substitution_lookup_functional M sb sc sn(code_numeral M 2)(zeroM M)j _ HSJ
    (source_cutoff_shift_map_fixed_lookup M 1 sb sc sn HSM 0))). subst j.
   exact(source_cutoff_shift_map_fixed_lookup M 2 ub uc un HUM 1).
 - assert(E:j=succM M(succM M idx))by(exact(substitution_lookup_functional M sb sc sn(code_numeral M 2)(succM M idx)j _ HSJ
    (source_cutoff_shift_map_tail_lookup M 1 sb sc sn idx HSM))). subst j.
   exact(source_cutoff_shift_map_tail_lookup M 2 ub uc un idx HUM).
Qed.
Theorem source_shift_cutoff_one_thrice M f first second third shifted out k:
 source_bounded M f(succM M k)->source_cutoff_shift M 1 f first->source_cutoff_shift M 1 first second->
 source_cutoff_shift M 1 second third->source_formula_shift M f shifted->source_formula_shift M third out->
 exists middle1 middle2,source_cutoff_shift M 2 shifted middle1 /\source_cutoff_shift M 2 middle1 middle2 /\source_cutoff_shift M 2 middle2 out.
Proof.
 intros HB H1 H2 H3 HF HT.
 destruct(numerical_renaming_total M first(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(s1&HS1).
 destruct(numerical_renaming_total M second(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(s2&HS2).
 exists s1,s2. split.
 - exact(source_shift_cutoff_one_two M f first shifted s1(succM M k)HB H1 HF HS1).
 - split.
   + exact(source_shift_cutoff_one_two M first second s1 s2(succM M(succM M k))
      (source_cutoff_shift_bounded M 1 f first k HB H1)H2 HS1 HS2).
   + exact(source_shift_cutoff_one_two M second third s2 out(succM M(succM M(succM M k)))
      (source_cutoff_shift_bounded M 1 first second(succM M k)(source_cutoff_shift_bounded M 1 f first k HB H1)H2)H3 HS2 HT).
Qed.
Theorem source_zfr_cutoff_proof M depth f g:
 source_cutoff_shift M depth f g->source_zfr_provable M f->source_zfr_provable M g.
Proof.
 intros(b&c&n&HM&HG)HP. apply(proj1(source_zfr_descriptor_provable M g)).
 exact(source_descriptor_provable_renaming M ZFRSourceDescriptor f b c n(code_numeral M 1)g
  (proj2(source_zfr_descriptor_provable M f)HP)(source_cutoff_shift_map_renaming M depth f g b c n HM HG)).
Qed.
Print Assumptions source_shift_cutoff_one_two.
Print Assumptions source_shift_cutoff_one_thrice.
Print Assumptions source_zfr_cutoff_proof.
