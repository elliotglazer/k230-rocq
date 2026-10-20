(** Actual bounded-universal introduction for arbitrary internal counts.
    The open proof family is first-order and demands actual shifted-premise
    proofs and actual parameter-membership proofs in its source context. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs
  SetFormulaCodes SourceBounded NumericalContexts NumericalEnvironments NumericalContextRenaming NumericalSourceFull
  NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps SourceRenamingIdentity SourceRepresentationPadding
  SourceContextProofHelpers SourceBallS SourceBallSBounds SourceTarskiVaughtInputs SourceInternalLiftLaws.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature|0.
#[local] Existing Instance PA_preds_signature|0.
Definition source_shifted_context_proofs M cb cc cn delta ub uc un:=forall f g,
  context_member M cb cc cn f ->numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)delta g ->
  source_full_prv M ub uc un g.
Definition source_shifted_context_proofs_formula(cb cc cn delta ub uc un:term):form:=∀∀(
  context_member_formula(code_lift2 cb)(code_lift2 cc)(code_lift2 cn)$1 →
  numerical_renaming_formula $1 zero zero zero(code_lift2 delta)$0 →
  source_full_prv_formula(code_lift2 ub)(code_lift2 uc)(code_lift2 un)$0).
Definition source_balls_open_proof M cb cc cn count carrier body:=forall ub uc un k,
  context_bounded M ub uc un k ->source_shifted_context_proofs M cb cc cn count ub uc un ->
  source_tv_members M ub uc un count(addM M count carrier) ->source_full_prv M ub uc un body.
Definition source_balls_open_proof_formula(cb cc cn count carrier body:term):form:=∀∀∀∀(
  context_bounded_formula $3 $2 $1 $0 →
  source_shifted_context_proofs_formula(lift4 cb)(lift4 cc)(lift4 cn)(lift4 count)$3 $2 $1 →
  source_tv_members_formula $3 $2 $1(lift4 count)(lift4 count⊕lift4 carrier) →
  source_full_prv_formula $3 $2 $1(lift4 body)).
Local Opaque holds context_member_formula numerical_renaming_formula source_full_prv_formula
  context_bounded_formula source_tv_members_formula.
Theorem source_shifted_context_proofs_formula_correct M rho cb cc cn delta ub uc un:
  holds M rho(source_shifted_context_proofs_formula cb cc cn delta ub uc un) <->
  source_shifted_context_proofs M(evalM M rho cb)(evalM M rho cc)(evalM M rho cn)(evalM M rho delta)
    (evalM M rho ub)(evalM M rho uc)(evalM M rho un).
Proof.
  unfold source_shifted_context_proofs_formula,source_shifted_context_proofs.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite context_member_formula_correct. setoid_rewrite numerical_renaming_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. repeat setoid_rewrite code_eval_lift2. reflexivity.
Qed.
Local Opaque source_shifted_context_proofs_formula.
Theorem source_balls_open_proof_formula_correct M rho cb cc cn count carrier body:
  holds M rho(source_balls_open_proof_formula cb cc cn count carrier body) <->
  source_balls_open_proof M(evalM M rho cb)(evalM M rho cc)(evalM M rho cn)(evalM M rho count)
    (evalM M rho carrier)(evalM M rho body).
Proof.
  unfold source_balls_open_proof_formula,source_balls_open_proof.
  repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
  setoid_rewrite context_bounded_formula_correct. setoid_rewrite source_shifted_context_proofs_formula_correct.
  setoid_rewrite source_tv_members_formula_correct. setoid_rewrite source_full_prv_formula_correct.
  setoid_rewrite substitution_eval_add. repeat setoid_rewrite lift4_correct. reflexivity.
Qed.

Definition balls_introduction_at M count:=forall carrier body out cb cc cn k,
  context_bounded M cb cc cn k ->coding_lt M carrier k ->source_bounded M body(addM M count k) ->
  source_ballS M count carrier body out ->source_balls_open_proof M cb cc cn count carrier body ->
  source_full_prv M cb cc cn out.
Definition balls_introduction_formula:form:=∀∀∀∀∀∀∀(
  context_bounded_formula $3 $2 $1 $0 →Peano.sless $6 $0 →source_bounded_accept_formula $5($7⊕$0) →
  source_ballS_formula $7 $6 $5 $4 →source_balls_open_proof_formula $3 $2 $1 $7 $6 $5 →
  source_full_prv_formula $3 $2 $1 $4).
Local Opaque source_bounded_accept_formula source_ballS_formula source_balls_open_proof_formula Peano.sless.
Theorem balls_introduction_definable M:Definable1 M(balls_introduction_at M).
Proof.
  exists balls_introduction_formula,(fun _=>zeroM M). intro count.
  unfold balls_introduction_formula,balls_introduction_at. repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp. setoid_rewrite context_bounded_formula_correct.
  setoid_rewrite less_formula_correct. setoid_rewrite source_bounded_accept_formula_correct.
  setoid_rewrite source_ballS_formula_correct. setoid_rewrite source_balls_open_proof_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. reflexivity.
Qed.
Lemma source_empty_shift_lookup M delta i j:
  renaming_lookup M(zeroM M)(zeroM M)(zeroM M)delta i j <->j=addM M i delta.
Proof. apply renaming_lookup_outside,coding_not_lt_zero. Qed.
Lemma source_empty_shift_composition M f g h k delta epsilon:
  source_bounded M f k ->numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)delta g ->
  numerical_renaming M g(zeroM M)(zeroM M)(zeroM M)epsilon h ->
  numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(addM M delta epsilon)h.
Proof.
  intros BF HG HH. apply(representation_renaming_composition M f k
    (zeroM M)(zeroM M)(zeroM M)delta(zeroM M)(zeroM M)(zeroM M)epsilon
    (zeroM M)(zeroM M)(zeroM M)(addM M delta epsilon)g h BF HG HH).
  intros i j v _ HJ HV. apply source_empty_shift_lookup in HJ,HV.
  apply source_empty_shift_lookup. subst j v.
  symmetry. apply Arithmetic.add_assoc.
Qed.

Theorem source_full_ballS_introduction M count:balls_introduction_at M count.
Proof.
  revert count. apply(definable_induction M _ (balls_introduction_definable M)).
  - intros carrier body out cb cc cn k BC HY BB HB HP.
    apply source_ballS_zero in HB. subst out.
    apply(HP cb cc cn k BC).
    + intros f g HF HG.
      assert(HId:numerical_renaming M f(zeroM M)(zeroM M)(zeroM M)(zeroM M)f).
      { apply(numerical_renaming_identity_on_bound M f _ _ _ _ k(BC f HF)).
        intros i HI. apply source_empty_shift_lookup. symmetry. apply coding_add_zero_r. }
      rewrite(numerical_renaming_functional M f _ _ _ _ g f HG HId).
      exact(full_source_Ctx M cb cc cn f(ex_intro _ k(conj(BC f HF)BC))HF).
    + intros i member HI HG. exfalso. exact(coding_not_lt_zero M i HI).
  - intros count IH carrier body out cb cc cn k BC HY BB HB HP.
    pose proof(source_ballS_bounded M(succM M count)carrier body out k HB HY BB)as BOut.
    apply source_ballS_succ in HB. destruct HB as(previous&HPrevious&guard&point&HG&HI&HAll).
    pose proof(proj1(source_bounded_accept_unary M SFAll point out k(or_introl eq_refl)HAll)BOut)as BPoint.
    destruct(proj1(source_bounded_accept_binary M SFImpl guard previous point(succM M k)
      (or_intror(or_intror eq_refl))HI)BPoint)as(BGuard&BPrevious).
    destruct(context_shift_total M cb cc cn)as(ub&uc&HShift).
    pose proof(context_shift_preserves_bound M cb cc cn ub uc k HShift BC)as BShift.
    destruct(environment_cons_total M ub uc cn guard)as(gb&gc&gn&HCons).
    pose proof(proj2(context_bounded_cons M ub uc cn guard gb gc gn(succM M k)HCons)(conj BGuard BShift))as BCons.
    assert(BBody:source_bounded M body(addM M count(succM M k))).
    { rewrite coding_add_comm,Arithmetic.add_succ,coding_add_comm,<-Arithmetic.add_succ. exact BB. }
    assert(POpen:source_balls_open_proof M gb gc gn count(succM M carrier)body).
    { intros tb tc tn width BT HProofs HMembers. apply(HP tb tc tn width BT).
      - intros f full HF HFull.
        destruct(context_renaming_member_forward M cb cc cn(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)
          ub uc f HShift HF)as(shifted&HShifted&HRShifted).
        destruct(numerical_renaming_total M shifted(zeroM M)(zeroM M)(zeroM M)count)as(result&HRResult).
        pose proof(source_empty_shift_composition M f shifted result k(code_numeral M 1)count(BC f HF)HRShifted HRResult)as HRFull.
        change(code_numeral M 1)with(succM M(zeroM M))in HRFull.
        rewrite Arithmetic.add_succ,coding_add_zero in HRFull.
        assert(E:result=full)by(eapply numerical_renaming_functional;eassumption). subst result.
        apply(HProofs shifted full);[|exact HRResult].
        apply(proj2(context_member_cons M ub uc cn guard gb gc gn shifted HCons)). now right.
      - intros i member HIndex HMember.
        replace(addM M(succM M count)carrier)with(addM M count(succM M carrier))in HMember
          by(now rewrite Arithmetic.add_succ,internal_add_succ_right).
        destruct(proj1(coding_lt_succ_cases M i count)HIndex)as[HSmall|E].
        + exact(HMembers i member HSmall HMember).
        + subst i. apply(HProofs guard member).
          * apply(proj2(context_member_cons M ub uc cn guard gb gc gn guard HCons)). now left.
          * apply(proj2(numerical_renaming_member M(zeroM M)(succM M carrier)guard
              (zeroM M)(zeroM M)(zeroM M)count member HG)).
            exists count,(addM M count(succM M carrier)). split.
            -- apply source_empty_shift_lookup. symmetry. apply coding_add_zero.
            -- split;[apply source_empty_shift_lookup;apply coding_add_comm|exact HMember]. }
    pose proof(IH(succM M carrier)body previous gb gc gn(succM M k)BCons
      (proj2(coding_lt_succ_cancel M carrier k)HY)BBody HPrevious POpen)as PPrevious.
    pose proof(full_source_II M ub uc cn guard previous point gb gc gn
      (ex_intro _(succM M k)(conj BPoint BShift))PPrevious HCons HI)as PPoint.
    exact(full_source_AllI M cb cc cn point out ub uc(ex_intro _ k(conj BOut BC))PPoint HShift HAll).
Qed.
Print Assumptions source_shifted_context_proofs_formula_correct.
Print Assumptions source_balls_open_proof_formula_correct.
Print Assumptions balls_introduction_definable.
Print Assumptions source_empty_shift_composition.
Print Assumptions source_full_ballS_introduction.
