(** Three simultaneous witness names specialize the actual attempt step.
    The arbitrary binary relation hole is transported by a genuine lifted
    substitution, with both live roles checked. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded
  NumericalSubstitutionMaps NumericalSubstitution SourceFiniteCutoffShift SourceTripleSpecialization
  SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport SourceRecursionBinaryInstance SourceRecursionAttemptStepShell.
Unset Implicit Arguments.

Theorem source_rec_attempt_point_substitution M phi N f guard successor appOut appIn body ex t3 t2 point
    u u' v' tb tc member namedSuccessor namedApp result r3 r2 target:
  source_bounded M phi(code_numeral M 2) ->
  sf_relation M SFMember(code_numeral M 2)(source_succ_iter M 3 N)guard ->
  source_rec_successor M(code_numeral M 2)(code_numeral M 1)successor ->
  source_rec_app M(source_succ_iter M 3 f)(code_numeral M 1)(zeroM M)appOut ->
  source_rec_app M(source_succ_iter M 4 f)(code_numeral M 3)(zeroM M)appIn ->
  sf_relation M SFAnd appIn phi body ->sf_relation M SFEx body(zeroM M)ex ->
  sf_relation M SFImpl appOut ex t3 ->sf_relation M SFImpl successor t3 t2 ->sf_relation M SFImpl guard t2 point ->
  source_triple_prefix M v' u' u tb tc ->sf_relation M SFMember u N member ->source_rec_successor M u u' namedSuccessor ->
  source_rec_app M f u' v' namedApp ->source_rec_transition_witness M phi f u v' result ->
  sf_relation M SFImpl namedApp result r3 ->sf_relation M SFImpl namedSuccessor r3 r2 ->sf_relation M SFImpl member r2 target ->
  numerical_substitution M point tb tc(code_numeral M 3)(zeroM M)target.
Proof.
  intros HB HG HS HO HI HBody HEx H3 H2 HPoint HPrefix HMember HSuccessor HApp
    (newApp&binary&newBody&HNewApp&HBinary&HNewBody&HNewEx)HR3 HR2 HTarget.
  assert(HGSub:numerical_substitution M guard tb tc(code_numeral M 3)(zeroM M)member).
  { apply(proj2(numerical_substitution_member M(code_numeral M 2)(source_succ_iter M 3 N)guard
      tb tc(code_numeral M 3)(zeroM M)member HG)). exists u,N.
    exact(conj(proj2(proj2 HPrefix))(conj(source_triple_prefix_tail M tb tc N)HMember)). }
  pose proof(source_rec_successor_substitution M(code_numeral M 2)(code_numeral M 1)successor u u' namedSuccessor
    tb tc(code_numeral M 3)(zeroM M)HS HSuccessor(proj2(proj2 HPrefix))(proj1(proj2 HPrefix))) as HSSub.
  pose proof(source_rec_app_substitution M(source_succ_iter M 3 f)(code_numeral M 1)(zeroM M)appOut f u' v' namedApp
    tb tc(code_numeral M 3)(zeroM M)HO HApp(source_triple_prefix_tail M tb tc f)(proj1(proj2 HPrefix))(proj1 HPrefix)) as HOSub.
  destruct(substitution_lift_total M tb tc(code_numeral M 3)(zeroM M)) as(ab&ac&an&HMap).
  pose proof(source_rec_app_substitution M(source_succ_iter M 4 f)(code_numeral M 3)(zeroM M)appIn
    (succM M f)(succM M u)(zeroM M)newApp ab ac an(code_numeral M 1)HI HNewApp
    (proj2(proj2 HMap)(source_succ_iter M 3 f)f(source_triple_prefix_tail M tb tc f))
    (proj2(proj2 HMap)(code_numeral M 2)u(proj2(proj2 HPrefix)))(proj1(proj2 HMap))) as HISub.
  destruct(numerical_substitution_total M phi ab ac an(code_numeral M 1)) as(binary'&HSubBinary).
  pose proof(source_rec_binary_from_substitution M phi ab ac an(code_numeral M 1)binary'(zeroM M)(succM M v')HB HSubBinary
    (proj1(proj2 HMap))(proj2(proj2 HMap)(zeroM M)v'(proj1 HPrefix))) as HBinary'.
  pose proof(source_rec_binary_functional M phi(zeroM M)(succM M v')binary' binary HBinary' HBinary) as E. subst binary'.
  assert(HBodySub:numerical_substitution M body ab ac an(code_numeral M 1)newBody).
  { apply(proj2(numerical_substitution_binary M SFAnd appIn phi body ab ac an(code_numeral M 1)newBody(or_introl eq_refl)HBody)).
    exists newApp,binary. auto. }
  assert(HExSub:numerical_substitution M ex tb tc(code_numeral M 3)(zeroM M)result).
  { apply(proj2(numerical_substitution_quantifier M false body ex tb tc(code_numeral M 3)(zeroM M)result HEx)).
    exists ab,ac,an,newBody. auto. }
  assert(H3Sub:numerical_substitution M t3 tb tc(code_numeral M 3)(zeroM M)r3).
  { apply(proj2(numerical_substitution_binary M SFImpl appOut ex t3 tb tc(code_numeral M 3)(zeroM M)r3(or_intror(or_intror eq_refl))H3)).
    exists namedApp,result. auto. }
  assert(H2Sub:numerical_substitution M t2 tb tc(code_numeral M 3)(zeroM M)r2).
  { apply(proj2(numerical_substitution_binary M SFImpl successor t3 t2 tb tc(code_numeral M 3)(zeroM M)r2(or_intror(or_intror eq_refl))H2)).
    exists namedSuccessor,r3. auto. }
  apply(proj2(numerical_substitution_binary M SFImpl guard t2 point tb tc(code_numeral M 3)(zeroM M)target(or_intror(or_intror eq_refl))HPoint)).
  exists member,r2. auto.
Qed.

Print Assumptions source_rec_attempt_point_substitution.
