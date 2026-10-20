(** The two actual minimal-ordinal instances imply equality. All cross
    substitutions are constructed from the literal RepA/RepB maps. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SetSchemaConstructors SchemaConstructorBounds
  SourceBounded NumericalContexts NumericalInstantiation NumericalSubstitutionMaps NumericalSubstitution
  NumericalSourceFull SourceInstantiationConstructors SourcePropositionalTemplates SourcePropositionalRebase
  SourceOrdinalPredicate SourceOrdinalTrichotomy SourceOrdinalCollectionRecipe SourceOrdinalCollectionPayloads
  SourceOrdinalCrossInstantiation SourceMinimalUniqueness SourceOrdinalUniquenessProgram
  SourceFilterMemberIntroduction SourceConjunctionRules SourceDerivedRules SchemaRenamingDescriptors.
Unset Implicit Arguments.

Definition oc_unique_environment {A} (left equal right p q:A) i :=
  match i with 0=>left|1=>equal|2=>right|3=>p|_=>q end.

Lemma source_exclusion_instantiation M matrix point atom neg s t value :
  sf_relation M SFMember (zeroM M) (succM M s) atom ->sf_relation M SFImpl matrix (zeroM M) neg ->
  sf_relation M SFImpl atom neg point ->numerical_instantiation M matrix t value ->
  exists member notvalue exclusion,
    sf_relation M SFMember t s member /\sf_relation M SFImpl value (zeroM M) notvalue /\
    sf_relation M SFImpl member notvalue exclusion /\numerical_instantiation M point t exclusion.
Proof.
  intros HA HN HP HI.
  destruct (sf_relation_total M SFMember t s) as (member&HM).
  destruct (sf_relation_total M SFImpl value (zeroM M)) as (notvalue&HNV).
  destruct (sf_relation_total M SFImpl member notvalue) as (exclusion&HE).
  assert (HFalse:numerical_instantiation M (zeroM M) t (zeroM M)).
  { destruct (substitution_singleton_total M t) as (b&c&HH&_). exists b,c. split;[exact HH|].
    apply (proj2 (numerical_substitution_invalid M (zeroM M) b c (code_numeral M 1)
      (zeroM M) (zeroM M) (or_introl eq_refl))). reflexivity. }
  pose proof (source_member_zero_successor_instantiation M s t atom member HA HM) as HAM.
  pose proof (source_instantiation_binary M SFImpl matrix (zeroM M) neg t value (zeroM M) notvalue
    (or_intror (or_intror eq_refl)) HN HI HFalse HNV) as HNI.
  exists member,notvalue,exclusion. split;[exact HM|]. split;[exact HNV|]. split;[exact HE|].
  exact (source_instantiation_binary M SFImpl atom neg point t member notvalue exclusion
    (or_intror (or_intror eq_refl)) HP HAM HNI HE).
Qed.

Theorem source_full_oc_unique M b c n k bound phi oc ra rb law equal :
  source_bounded M phi k ->context_bounded M b c n bound ->coding_lt M (code_numeral M 1) bound ->
  source_bounded M ra bound ->source_bounded M rb bound ->
  source_oc_form M (source_ordinal_predicate_code M) phi oc ->
  schema_renaming M RepA oc ra ->schema_renaming M RepB oc rb ->
  code_relation M (schema_env3 (code_numeral M 1) (zeroM M) (zeroM M)) ordinal_trichotomy_expression law ->
  sf_relation M SFEqual (code_numeral M 1) (zeroM M) equal ->
  source_full_prv M b c n law ->source_full_prv M b c n ra ->source_full_prv M b c n rb ->
  source_full_prv M b c n equal.
Proof.
  intros HB HC HOne HRA HRB (ord1&swapped&tail&inner&HOrd1&HSwap&HTail&HInner&HOC)
    HRAren HRBren HLaw HEqual PLaw PRA PRB.
  destruct HTail as (shifted&atom&neg&point&HShift&HAtom&HNeg&HPoint&HAll).
  destruct HShift as (cb&cc&cn&HM&HS).
  destruct (source_oc_side_payload M true _ ord1 swapped shifted atom neg point tail inner oc ra
    (source_ordinal_predicate_bounded M) HOrd1 HAtom HNeg HPoint HAll HInner HOC HRAren)
    as (ordA&predA&allA&tagA&matrixA&atomA&negA&pointA&ab&ac&an
      &HOrdA&HPredA&HTagA&HRAout&HAllA&HAtomA&HNegA&HPointA&HLA&HRMatrixA).
  destruct (source_oc_side_payload M false _ ord1 swapped shifted atom neg point tail inner oc rb
    (source_ordinal_predicate_bounded M) HOrd1 HAtom HNeg HPoint HAll HInner HOC HRBren)
    as (ordB&predB&allB&tagB&matrixB&atomB&negB&pointB&bb&bc&bn
      &HOrdB&HPredB&HTagB&HRBout&HAllB&HAtomB&HNegB&HPointB&HLB&HRMatrixB).
  pose proof (source_oc_cross_instantiation M true phi k swapped shifted matrixA predB cb cc cn ab ac an
    HB HSwap HM HS HLA HRMatrixA HPredB) as HCrossA.
  pose proof (source_oc_cross_instantiation M false phi k swapped shifted matrixB predA cb cc cn bb bc bn
    HB HSwap HM HS HLB HRMatrixB HPredA) as HCrossB.
  destruct (source_exclusion_instantiation M matrixA pointA atomA negA (code_numeral M 1) (zeroM M)
    predB HAtomA HNegA HPointA HCrossA) as (right&notB&rex&HRight&HNotB&HRex&HIRex).
  destruct (source_exclusion_instantiation M matrixB pointB atomB negB (zeroM M) (code_numeral M 1)
    predA HAtomB HNegB HPointB HCrossB) as (left&notA&lex&HLeft&HNotA&HLex&HILex).
  destruct (source_ordinal_trichotomy_shell M _ law HLaw)
    as (ordA'&ordB'&imp&tri&first&left'&equal'&right'
      &HOrdA'&HOrdB'&HLawImp&HImpTri&HTri&HFirst&HLeft'&HEqual'&HRight').
  pose proof (numerical_instantiation_functional M (source_ordinal_predicate_code M) (code_numeral M 1)
    ordA' ordA HOrdA' HOrdA) as EA. subst ordA'.
  pose proof (numerical_instantiation_functional M (source_ordinal_predicate_code M) (zeroM M)
    ordB' ordB HOrdB' HOrdB) as EB. subst ordB'.
  pose proof (sf_relation_functional M SFMember _ _ left' left HLeft' HLeft) as E. subst left'.
  pose proof (sf_relation_functional M SFMember _ _ right' right HRight' HRight) as E. subst right'.
  pose proof (sf_relation_functional M SFEqual _ _ equal' equal HEqual' HEqual) as E. subst equal'.
  pose proof (source_full_conjunction_left M b c n tagA allA ra HRAout PRA) as PTagA.
  pose proof (source_full_conjunction_right M b c n tagA allA ra HRAout PRA) as PAllA.
  pose proof (source_full_conjunction_left M b c n ordA predA tagA HTagA PTagA) as POrdA.
  pose proof (source_full_conjunction_right M b c n ordA predA tagA HTagA PTagA) as PPredA.
  pose proof (source_full_conjunction_left M b c n tagB allB rb HRBout PRB) as PTagB.
  pose proof (source_full_conjunction_right M b c n tagB allB rb HRBout PRB) as PAllB.
  pose proof (source_full_conjunction_left M b c n ordB predB tagB HTagB PTagB) as POrdB.
  pose proof (source_full_conjunction_right M b c n ordB predB tagB HTagB PTagB) as PPredB.
  pose proof (source_full_modus_ponens M b c n ordA imp law HLawImp PLaw POrdA) as PImp.
  pose proof (source_full_modus_ponens M b c n ordB tri imp HImpTri PImp POrdB) as PTri.
  set (rho:=oc_unique_environment left equal right predA predB).
  assert (HZero:coding_lt M (zeroM M) bound).
  { exact (coding_lt_trans M (zeroM M) (code_numeral M 1) bound (coding_zero_lt_succ M (zeroM M)) HOne). }
  assert (HBP:source_bounded M predA bound).
  { exact (proj2 (proj1 (source_bounded_accept_binary M SFAnd ordA predA tagA bound (or_introl eq_refl) HTagA)
      (proj1 (proj1 (source_bounded_accept_binary M SFAnd tagA allA ra bound (or_introl eq_refl) HRAout) HRA)))). }
  assert (HBQ:source_bounded M predB bound).
  { exact (proj2 (proj1 (source_bounded_accept_binary M SFAnd ordB predB tagB bound (or_introl eq_refl) HTagB)
      (proj1 (proj1 (source_bounded_accept_binary M SFAnd tagB allB rb bound (or_introl eq_refl) HRBout) HRB)))). }
  assert (HBRho:forall i,source_bounded M (rho i) bound).
  { intros [|[|[|[|i]]]];cbn [rho oc_unique_environment];try assumption.
    - apply (proj2 (source_bounded_accept_atom M SFMember _ _ left bound (or_introl eq_refl) HLeft)). split;assumption.
    - apply (proj2 (source_bounded_accept_atom M SFEqual _ _ equal bound (or_intror eq_refl) HEqual)). split;assumption.
    - apply (proj2 (source_bounded_accept_atom M SFMember _ _ right bound (or_introl eq_refl) HRight)). split;assumption. }
  assert (GFirst:code_relation M rho (E_sf SFOr (CEvar 0) (CEvar 1)) first).
  { exact (proj2 (schema_expression_graph M rho SFOr (CEvar 0) (CEvar 1) left equal first eq_refl eq_refl) HFirst). }
  assert (GTri:code_relation M rho (source_prop_expression ordinal_unique_tri) tri).
  { exact (proj2 (schema_expression_graph M rho SFOr (E_sf SFOr (CEvar 0) (CEvar 1)) (CEvar 2) first right tri GFirst eq_refl) HTri). }
  assert (GNotA:code_relation M rho (E_sf SFImpl (CEvar 3) (CEconst 0)) notA).
  { exact (proj2 (schema_expression_graph M rho SFImpl (CEvar 3) (CEconst 0) predA (zeroM M) notA eq_refl eq_refl) HNotA). }
  assert (GLex:code_relation M rho (source_prop_expression ordinal_unique_left_exclusion) lex).
  { exact (proj2 (schema_expression_graph M rho SFImpl (CEvar 0) (E_sf SFImpl (CEvar 3) (CEconst 0)) left notA lex eq_refl GNotA) HLex). }
  assert (GNotB:code_relation M rho (E_sf SFImpl (CEvar 4) (CEconst 0)) notB).
  { exact (proj2 (schema_expression_graph M rho SFImpl (CEvar 4) (CEconst 0) predB (zeroM M) notB eq_refl eq_refl) HNotB). }
  assert (GRex:code_relation M rho (source_prop_expression ordinal_unique_right_exclusion) rex).
  { exact (proj2 (schema_expression_graph M rho SFImpl (CEvar 2) (E_sf SFImpl (CEvar 4) (CEconst 0)) right notB rex eq_refl GNotB) HRex). }
  exact (source_full_minimal_uniqueness M rho bound b c n tri lex rex pointB allB pointA allA
    (code_numeral M 1) (zeroM M) HBRho HC GTri GLex GRex HAllB HAllA HILex HIRex
    PTri PPredA PPredB PAllB PAllA).
Qed.

Print Assumptions source_exclusion_instantiation.
Print Assumptions source_full_oc_unique.
