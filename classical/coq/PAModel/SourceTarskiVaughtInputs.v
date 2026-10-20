(** First-order source-proof inputs for uniform Tarski-Vaught induction.
    Witness closure ranges over actual quantified pieces of the source code. *)
From PAModel Require Import Model FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs SetFormulaCodes
  SourceBounded NumericalContexts NumericalContextRenaming NumericalSourceFull SourceProofRenaming SourceProofWeakening
  NumericalRenamingMaps NumericalRenaming SourceRenamingIdentity SourceRelativizationRules
  SourceSetRelativizationRules SourceSetRelativizationRenaming SourceQuantifierPieces SourceQuantifierPieceInversion
  SourcePCSPieces SourcePieceWitnessInstance.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Import Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature|0.
#[local] Existing Instance PA_preds_signature|0.

Definition source_tv_members M cb cc cn count carrier:=forall i member,
  coding_lt M i count ->sf_relation M SFMember i carrier member ->source_full_prv M cb cc cn member.
Definition source_tv_members_formula(cb cc cn count carrier:term):form:=∀∀(
  Peano.sless $1(code_lift2 count) →sf_formula SFMember $1(code_lift2 carrier)$0 →
  source_full_prv_formula(code_lift2 cb)(code_lift2 cc)(code_lift2 cn)$0).
Definition source_tv_witnesses M domain phi count carrier cb cc cn:=forall piececount body piece out,
  source_quantifier_body M phi count piececount body ->source_pcs_sign M domain body piece ->
  source_piece_witness_instance M domain piececount piece carrier out ->source_full_prv M cb cc cn out.
Definition source_tv_witnesses_formula(domain phi count carrier cb cc cn:term):form:=∀∀∀∀(
  source_quantifier_body_formula(lift4 phi)(lift4 count)$3 $2 →
  source_pcs_sign_formula(lift4 domain)$2 $1 →
  source_piece_witness_instance_formula(lift4 domain)$3 $1(lift4 carrier)$0 →
  source_full_prv_formula(lift4 cb)(lift4 cc)(lift4 cn)$0).
Definition source_tv_containment M domain carrier cb cc cn:=exists out,
  ssr_quantifier M true carrier domain out /\source_full_prv M cb cc cn out.
Definition source_tv_containment_formula(domain carrier cb cc cn:term):form:=∃(
  ssr_quantifier_formula true carrier`[↑] domain`[↑] $0 ∧
  source_full_prv_formula cb`[↑] cc`[↑] cn`[↑] $0).
Local Opaque holds sf_formula source_full_prv_formula source_quantifier_body_formula
  source_pcs_sign_formula source_piece_witness_instance_formula ssr_quantifier_formula Peano.sless.

Theorem source_tv_members_formula_correct M rho cb cc cn count carrier:
  holds M rho(source_tv_members_formula cb cc cn count carrier) <->
  source_tv_members M(evalM M rho cb)(evalM M rho cc)(evalM M rho cn)(evalM M rho count)(evalM M rho carrier).
Proof.
  unfold source_tv_members_formula,source_tv_members. repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp. setoid_rewrite less_formula_correct. setoid_rewrite sf_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. repeat setoid_rewrite code_eval_lift2. reflexivity.
Qed.
Theorem source_tv_witnesses_formula_correct M rho domain phi count carrier cb cc cn:
  holds M rho(source_tv_witnesses_formula domain phi count carrier cb cc cn) <->
  source_tv_witnesses M(evalM M rho domain)(evalM M rho phi)(evalM M rho count)(evalM M rho carrier)
    (evalM M rho cb)(evalM M rho cc)(evalM M rho cn).
Proof.
  unfold source_tv_witnesses_formula,source_tv_witnesses. repeat setoid_rewrite holds_all.
  repeat setoid_rewrite holds_imp. setoid_rewrite source_quantifier_body_formula_correct.
  setoid_rewrite source_pcs_sign_formula_correct. setoid_rewrite source_piece_witness_instance_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. repeat setoid_rewrite lift4_correct. reflexivity.
Qed.
Theorem source_tv_containment_formula_correct M rho domain carrier cb cc cn:
  holds M rho(source_tv_containment_formula domain carrier cb cc cn) <->
  source_tv_containment M(evalM M rho domain)(evalM M rho carrier)(evalM M rho cb)(evalM M rho cc)(evalM M rho cn).
Proof.
  unfold source_tv_containment_formula,source_tv_containment. setoid_rewrite holds_ex.
  setoid_rewrite holds_and. setoid_rewrite ssr_quantifier_formula_correct.
  setoid_rewrite source_full_prv_formula_correct. unfold evalM. repeat setoid_rewrite eval_up. reflexivity.
Qed.

Theorem source_tv_members_weaken M cb cc cn ub uc un count carrier k:
  context_included M cb cc cn ub uc un ->context_bounded M ub uc un k ->
  source_tv_members M cb cc cn count carrier ->source_tv_members M ub uc un count carrier.
Proof.
  intros HI BC HM i member HCount HG.
  exact(source_full_prv_weaken_bounded M cb cc cn ub uc un member k(HM i member HCount HG)HI BC).
Qed.
Theorem source_tv_witnesses_weaken M domain phi count carrier cb cc cn ub uc un k:
  context_included M cb cc cn ub uc un ->context_bounded M ub uc un k ->
  source_tv_witnesses M domain phi count carrier cb cc cn ->source_tv_witnesses M domain phi count carrier ub uc un.
Proof.
  intros HI BC HW pc body piece out HB HS HO.
  exact(source_full_prv_weaken_bounded M cb cc cn ub uc un out k(HW pc body piece out HB HS HO)HI BC).
Qed.
Theorem source_tv_containment_weaken M domain carrier cb cc cn ub uc un k:
  context_included M cb cc cn ub uc un ->context_bounded M ub uc un k ->
  source_tv_containment M domain carrier cb cc cn ->source_tv_containment M domain carrier ub uc un.
Proof.
  intros HI BC(out&HO&PO). exists out. split;[exact HO|].
  exact(source_full_prv_weaken_bounded M cb cc cn ub uc un out k PO HI BC).
Qed.
Theorem source_tv_witnesses_shift M domain phi count carrier cb cc cn ub uc:
  source_bounded M domain(code_numeral M 1) ->source_bounded M phi count ->
  context_shift M cb cc cn ub uc ->source_tv_witnesses M domain phi count carrier cb cc cn ->
  source_tv_witnesses M domain phi count(succM M carrier)ub uc cn.
Proof.
  intros HD HP HC HW pc body piece out HB HS HO.
  pose proof(source_quantifier_body_bounded M phi count pc body HB HP)as BB.
  pose proof(source_pcs_sign_bounded M domain body piece(succM M pc)HD BB HS)as BP.
  destruct(source_piece_witness_instance_total M domain pc piece carrier)as(old&HOld).
  pose proof(HW pc body piece old HB HS HOld)as POld.
  apply(source_full_prv_renaming M cb cc cn old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)ub uc out POld HC).
  exact(source_piece_witness_instance_renaming_graph M domain pc piece carrier old(zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1)(succM M carrier)out HD BP HOld(proj2(context_shift_lookup M carrier(succM M carrier))eq_refl)HO).
Qed.
Theorem source_tv_containment_shift M domain carrier cb cc cn ub uc:
  source_bounded M domain(code_numeral M 1) ->context_shift M cb cc cn ub uc ->
  source_tv_containment M domain carrier cb cc cn ->source_tv_containment M domain(succM M carrier)ub uc cn.
Proof.
  intros HD HC(old&HOld&POld).
  destruct(ssr_quantifier_total M true(succM M carrier)domain)as(out&HOut).
  destruct(renaming_lift_total M(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(rb&rc&rn&HL).
  pose proof(numerical_renaming_lift_fixes_domain M domain(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)rb rc rn HD HL)as HRDomain.
  pose proof(ssr_quantifier_renaming M true carrier(succM M carrier)domain old(zeroM M)(zeroM M)(zeroM M)
    (code_numeral M 1)rb rc rn domain out(proj2(context_shift_lookup M carrier(succM M carrier))eq_refl)
    HL HOld HRDomain HOut)as HR.
  exists out. split;[exact HOut|].
  exact(source_full_prv_renaming M cb cc cn old(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1)ub uc out POld HC HR).
Qed.
Print Assumptions source_tv_members_formula_correct.
Print Assumptions source_tv_witnesses_formula_correct.
Print Assumptions source_tv_containment_formula_correct.
Print Assumptions source_tv_members_weaken.
Print Assumptions source_tv_witnesses_weaken.
Print Assumptions source_tv_containment_weaken.
Print Assumptions source_tv_witnesses_shift.
Print Assumptions source_tv_containment_shift.
