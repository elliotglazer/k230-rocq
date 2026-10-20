(** A conjunction recipe exposes two genuine child recipes using the
    same environment and assignment guard. No standardness assumption on
    the two source matrices is used. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes
 SetSchemaConstructors SchemaConstructorBounds NumericalRenaming SourceSetRelativization
 SourceSetRelativizationFunctionality SourceRepresentationRecipe SourceDn SourceDefinabilityBounds SourceFiniteCutoffShift.
Unset Implicit Arguments.
Theorem source_representation_conjunction_children M n left right conjunction result :
 sf_relation M SFAnd left right conjunction ->source_representation_recipe M n conjunction result ->
 exists environment first shifted matrixLeft matrixRight relativeLeft relativeRight relativeAnd
   pointLeft pointRight pointAnd repLeft repRight,
 source_envf M n environment /\source_cutoff_shift M 1 environment first /\
 source_cutoff_shift M 1 first shifted /\
 numerical_renaming M left(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3) matrixLeft /\
 numerical_renaming M right(zeroM M)(zeroM M)(zeroM M)(code_numeral M 3) matrixRight /\
 source_set_relativization M(code_numeral M 2) matrixLeft relativeLeft /\
 source_set_relativization M(code_numeral M 2) matrixRight relativeRight /\
 sf_relation M SFAnd relativeLeft relativeRight relativeAnd /\
 code_relation M(representation_point_environment shifted relativeLeft)
   (E_representation_point(CEvar 0)(CEvar 1)) pointLeft /\
 code_relation M(representation_point_environment shifted relativeRight)
   (E_representation_point(CEvar 0)(CEvar 1)) pointRight /\
 code_relation M(representation_point_environment shifted relativeAnd)
   (E_representation_point(CEvar 0)(CEvar 1)) pointAnd /\
 source_dn M n pointLeft repLeft /\source_dn M n pointRight repRight /\source_dn M n pointAnd result /\
 source_representation_recipe M n left repLeft /\source_representation_recipe M n right repRight.
Proof.
 intros HAnd(environment&first&shifted&matrix&relative&point&HE&H1&H2&HM&HR&HP&HD).
 destruct(proj1(numerical_renaming_binary M SFAnd left right conjunction
   (zeroM M)(zeroM M)(zeroM M)(code_numeral M 3) matrix(or_introl eq_refl) HAnd) HM)
   as(ml&mr&HML&HMR&HMAnd).
 destruct(source_set_relativization_binary_inv M(code_numeral M 2) SFAnd ml mr matrix relative
   (or_introl eq_refl) HMAnd HR)as(rl&rr&HRL&HRR&HRAnd).
 destruct(code_relation_total M(E_representation_point(CEvar 0)(CEvar 1))
   (representation_point_environment shifted rl))as(pl&HPL).
 destruct(code_relation_total M(E_representation_point(CEvar 0)(CEvar 1))
   (representation_point_environment shifted rr))as(pr&HPR).
 destruct(source_dn_total M n pl)as(repL&HDL).
 destruct(source_dn_total M n pr)as(repR&HDR).
 exists environment,first,shifted,ml,mr,rl,rr,relative,pl,pr,point,repL,repR.
 refine(conj HE(conj H1(conj H2(conj HML(conj HMR(conj HRL(conj HRR(conj HRAnd
  (conj HPL(conj HPR(conj HP(conj HDL(conj HDR(conj HD(conj _ _))))))))))))))).
 - exists environment,first,shifted,ml,rl,pl. exact(conj HE(conj H1(conj H2(conj HML(conj HRL(conj HPL HDL)))))).
 - exists environment,first,shifted,mr,rr,pr. exact(conj HE(conj H1(conj H2(conj HMR(conj HRR(conj HPR HDR)))))).
Qed.
Print Assumptions source_representation_conjunction_children.

