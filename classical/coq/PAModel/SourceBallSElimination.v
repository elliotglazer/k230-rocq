(** Actual ballS elimination in the source calculus. The internally finite
    assignment prefix is numerical syntax, and every membership input is
    an ordinary source proof in the same context. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded NumericalContexts NumericalSourceFull SourceQuantifierRules SourceDerivedRules
  NumericalSubstitutionMaps NumericalSubstitution NumericalInstantiation SubstitutionSource SourceSubstitutionBounds
  SourceSubstitutionIdentity SourceSubstitutionComposition SourceBallSRules SourceBallS SourceBallSBounds
  SourceBallSSubstitution SourceBallSInverseBounds SourceBallSInstanceMaps SourceInternalLifts SourceInternalLiftLaws.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.
Definition balls_member_inputs M gb gc gn y b c count:=forall i t member,
  coding_lt M i count ->beta M b c i t ->sf_relation M SFMember t y member ->source_full_prv M gb gc gn member.
Definition balls_member_inputs_formula(gb gc gn y b c count:term):form:=∀∀∀(
  Peano.sless $2(lift3 count) →beta_formula(lift3 b)(lift3 c)$2 $1 →
  sf_formula SFMember $1(lift3 y)$0 →source_full_prv_formula(lift3 gb)(lift3 gc)(lift3 gn)$0).
Local Opaque holds Peano.sless beta_formula sf_formula source_full_prv_formula.
Lemma balls_member_inputs_formula_correct M rho gb gc gn y b c count:
  holds M rho(balls_member_inputs_formula gb gc gn y b c count)<->
  balls_member_inputs M(evalM M rho gb)(evalM M rho gc)(evalM M rho gn)(evalM M rho y)
    (evalM M rho b)(evalM M rho c)(evalM M rho count).
Proof.
  unfold balls_member_inputs_formula,balls_member_inputs. repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp. setoid_rewrite less_formula_correct.
  setoid_rewrite beta_formula_correct. setoid_rewrite sf_formula_correct. setoid_rewrite source_full_prv_formula_correct.
  unfold evalM,lift3. repeat setoid_rewrite eval_up. reflexivity.
Qed.
Definition balls_elimination_at M count:=forall y body out result b c gb gc gn k,
  context_bounded M gb gc gn k ->coding_lt M y k ->source_bounded M body(addM M count k) ->
  substitution_maps_bound M b c count(zeroM M)count k ->source_ballS M count y body out ->
  numerical_substitution M body b c count(zeroM M)result ->source_full_prv M gb gc gn out ->
  balls_member_inputs M gb gc gn y b c count ->source_full_prv M gb gc gn result.
Definition balls_elimination_formula:form:=∀∀∀∀∀∀∀∀∀∀(
  context_bounded_formula $3 $2 $1 $0 →Peano.sless $9 $0 →
  source_bounded_accept_formula $8($10⊕$0) →substitution_maps_bound_formula $5 $4 $10 zero $10 $0 →
  source_ballS_formula $10 $9 $8 $7 →numerical_substitution_formula $8 $5 $4 $10 zero $6 →
  source_full_prv_formula $3 $2 $1 $7 →balls_member_inputs_formula $3 $2 $1 $9 $5 $4 $10 →
  source_full_prv_formula $3 $2 $1 $6).
Local Opaque context_bounded_formula source_bounded_accept_formula substitution_maps_bound_formula
  source_ballS_formula numerical_substitution_formula balls_member_inputs_formula.
Lemma balls_elimination_definable M:Definable1 M(balls_elimination_at M).
Proof.
  exists balls_elimination_formula,(fun _=>zeroM M). intro count.
  unfold balls_elimination_formula,balls_elimination_at. repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp. setoid_rewrite context_bounded_formula_correct.
  setoid_rewrite less_formula_correct. setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite substitution_maps_bound_formula_correct. setoid_rewrite source_ballS_formula_correct.
  setoid_rewrite numerical_substitution_formula_correct. setoid_rewrite source_full_prv_formula_correct.
  setoid_rewrite balls_member_inputs_formula_correct. reflexivity.
Qed.
Theorem source_full_ballS_elimination M count:balls_elimination_at M count.
Proof.
  revert count. apply(definable_induction M _ (balls_elimination_definable M)).
  - intros y body out result b c gb gc gn k HC HY HBody HMap HBall HResult PBall HMembers.
    apply source_ballS_zero in HBall. subst out. rewrite coding_add_zero in HBody.
    assert(HIdentity:numerical_substitution M body b c(zeroM M)(zeroM M)body).
    { apply(numerical_substitution_identity_on_bound M body b c(zeroM M)(zeroM M)k HBody).
      intros i _. pose proof(balls_prefix_tail M b c(zeroM M)i)as H. now rewrite coding_add_zero in H. }
    pose proof(numerical_substitution_functional M body b c(zeroM M)(zeroM M)result body HResult HIdentity)as E.
    now subst result.
  - intros count IH y body out result b c gb gc gn k HC HY HBody HMap HBall HResult PBall HMembers.
    pose proof(source_ballS_bounded M(succM M count)y body out k HBall HY HBody)as BOut.
    destruct(source_ballS_succ M count y body out)as[HForward _].
    destruct(HForward HBall)as(previous&HP&atom&point&HA&HI&HQ).
    pose proof(proj1(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HQ)BOut)as BPoint.
    destruct(beta_total M b c count)as(t&HT).
    pose proof(proj2(substitution_lookup_inside M b c(succM M count)(zeroM M)count t(coding_lt_succ M count))HT)as HTLookup.
    pose proof(HMap count t(coding_lt_succ M count)HTLookup)as BT.
    destruct(numerical_instantiation_total M point t)as(point'&HInst).
    pose proof(numerical_instantiation_bounded M point t point' k BPoint BT HInst)as BPoint'.
    pose proof(full_source_AllE M gb gc gn point out t point'(ex_intro _ k(conj BPoint' HC))PBall HQ HInst)as PPoint'.
    destruct HInst as(ib&ic&HHead&HPointSub).
    destruct(proj1(numerical_substitution_binary M SFImpl atom previous point ib ic(code_numeral M 1)(zeroM M)point'
      (or_intror(or_intror eq_refl))HI)HPointSub)as(atom'&previous'&HAtomSub&HPreviousSub&HI').
    destruct(proj1(numerical_substitution_member M(zeroM M)(succM M y)atom ib ic(code_numeral M 1)(zeroM M)atom' HA)HAtomSub)
      as(x&z&HX&HZ&HA').
    pose proof(substitution_lookup_functional M ib ic(code_numeral M 1)(zeroM M)(zeroM M)x t HX HHead)as E. subst x.
    pose proof(substitution_lookup_functional M ib ic(code_numeral M 1)(zeroM M)(succM M y)z y HZ
      (substitution_singleton_tail M ib ic y))as E. subst z.
    pose proof(HMembers count t atom'(coding_lt_succ M count)HT HA')as PAtom'.
    pose proof(source_full_modus_ponens M gb gc gn atom' previous' point' HI' PPoint' PAtom')as PPrevious'.
    pose proof(proj2(proj1(source_bounded_accept_binary M SFImpl atom' previous' point' k
      (or_intror(or_intror eq_refl))HI')BPoint'))as BPrevious'.
    destruct(source_upn_map_total M count ib ic(code_numeral M 1)(zeroM M))as(ub&uc&HUpn).
    destruct(numerical_substitution_total M body ub uc(addM M count(code_numeral M 1))(addM M count(zeroM M)))as(body'&HBodySub).
    pose proof(source_ballS_substitution M count(succM M y)body previous ib ic(code_numeral M 1)(zeroM M)y body' previous' ub uc
      (substitution_singleton_tail M ib ic y)HP HUpn HBodySub HPreviousSub)as HBall'.
    pose proof(source_ballS_inverse_bound M count y body' previous' k HBall' BPrevious')as BBody'.
    destruct(numerical_substitution_total M body' b c count(zeroM M))as(result'&HResult').
    assert(HComposed:numerical_substitution M body b c(succM M count)(zeroM M)result').
    { apply(numerical_substitution_composition M body(addM M(succM M count)k)
        ub uc(addM M count(code_numeral M 1))(addM M count(zeroM M))
        b c count(zeroM M)b c(succM M count)(zeroM M)body' result' HBody HBodySub HResult').
      intros i j v _. exact(balls_instantiation_composition M count b c t ib ic ub uc HT HHead HUpn i j v). }
    pose proof(numerical_substitution_functional M body b c(succM M count)(zeroM M)result result' HResult HComposed)as E.
    subst result'.
    assert(HMap':substitution_maps_bound M b c count(zeroM M)count k).
    { intros i v HIndex HV. apply(proj1(substitution_lookup_inside M b c count(zeroM M)i v HIndex))in HV.
      exact(HMap i v(proj2(coding_lt_succ_cases M i count)(or_introl HIndex))
        (proj2(substitution_lookup_inside M b c(succM M count)(zeroM M)i v
          (proj2(coding_lt_succ_cases M i count)(or_introl HIndex)))HV)). }
    assert(HMembers':balls_member_inputs M gb gc gn y b c count).
    { intros i v member HIndex HV HM. exact(HMembers i v member
        (proj2(coding_lt_succ_cases M i count)(or_introl HIndex))HV HM). }
    exact(IH y body' previous' result b c gb gc gn k HC HY BBody' HMap' HBall' HResult' PPrevious' HMembers').
Qed.
Print Assumptions source_full_ballS_elimination.
