(** Moving representative-name transport through internally many Dn
    quantifiers. An output name r appears at r+n in the original matrix. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT FiniteCRTFormula CodeExpressions NumericalProofs SetFormulaCodes
 SourceBounded SourceDnStep SourceDn SourceDnBounds SourceRepresentativeRenaming
 NumericalRenamingMaps NumericalRenaming NumericalSubstitutionMaps.
From FOL Require Import FullSyntax Arithmetics.
From FOL.Tennenbaum Require Peano.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Theorem source_dn_successor_representative_transport M previous out r renamedout k :
 source_bounded M previous(succM M(succM M(succM M k))) ->~coding_lt M r(code_numeral M 2) ->
 source_dn_successor M previous out ->source_representative_renaming M r out renamedout ->
 exists renamed,source_representative_renaming M(succM M r) previous renamed /\
 source_dn_successor M renamed renamedout.
Proof.
 intros HB HR(rot&guard&point&HRot&HGuard&HPoint&HAll) HOut.
 apply(proj1(numerical_renaming_quantifier M true point out r r(code_numeral M 1)(zeroM M)
   renamedout HAll))in HOut.
 destruct HOut as(b&c&n&renamedpoint&HL&HPointRenamed&HAllRenamed).
 apply(proj1(numerical_renaming_binary M SFImpl guard rot point b c n(zeroM M) renamedpoint
   (or_intror(or_intror eq_refl)) HPoint))in HPointRenamed.
 destruct HPointRenamed as(newguard&newrot&HGuardRenamed&HRotRenamed&HNewPoint).
 assert(HGuardFixed:numerical_renaming M guard b c n(zeroM M) guard).
 { apply(proj2(numerical_renaming_member M(zeroM M)(code_numeral M 2) guard b c n(zeroM M) guard HGuard)).
   exists(zeroM M),(code_numeral M 2). split.
   - exact(proj2(renaming_lift_head M r r(code_numeral M 1)(zeroM M) b c n(zeroM M) HL) eq_refl).
   - split;[|exact HGuard]. apply(representative_lift_fixed M r b c n(code_numeral M 2) HL).
     intro E. apply(Model.succ_injective M)in E. exact(Model.zero_ne_succ M(zeroM M)(eq_sym E)). }
 assert(EG:newguard=guard)by(eapply numerical_renaming_functional;eassumption). subst newguard.
 destruct(source_representative_renaming_total M(succM M r) previous)as(renamed&HName).
 exists renamed. split;[exact HName|]. exists newrot,guard,renamedpoint.
 exact(conj(source_representative_dn_rotation_square M previous r renamed rot newrot b c n
   (succM M(succM M(succM M k))) HB HR HName HRot HL HRotRenamed)
   (conj HGuard(conj HNewPoint HAllRenamed))).
Qed.

Definition source_dn_representative_transport_at M count :=forall body out renamedbody renamedout r k,
 source_bounded M body(addM M count(succM M(succM M k))) ->~coding_lt M r(code_numeral M 2) ->
 source_dn M count body out ->source_representative_renaming M(addM M r count) body renamedbody ->
 source_representative_renaming M r out renamedout ->source_dn M count renamedbody renamedout.
Definition source_dn_representative_transport_formula :form :=∀∀∀∀∀∀(
 source_bounded_accept_formula $5($6 ⊕ σ(σ $0)) →(Peano.sless $1(num 2)→⊥) →
 source_dn_formula $6 $5 $4 →source_representative_renaming_formula($1 ⊕ $6) $5 $3 →
 source_representative_renaming_formula $1 $4 $2 →source_dn_formula $6 $3 $2).
Local Opaque holds source_bounded_accept_formula source_dn_formula source_representative_renaming_formula.
Lemma source_dn_representative_transport_definable M :Definable1 M(source_dn_representative_transport_at M).
Proof.
 exists source_dn_representative_transport_formula,(fun _=>zeroM M). intro count.
 unfold source_dn_representative_transport_formula,source_dn_representative_transport_at.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite source_dn_formula_correct.
 setoid_rewrite source_representative_renaming_formula_correct. setoid_rewrite holds_sless.
 setoid_rewrite substitution_holds_false. repeat setoid_rewrite code_eval_num. reflexivity.
Qed.
Theorem source_dn_representative_transport M count :source_dn_representative_transport_at M count.
Proof.
 revert count. apply(definable_induction M(source_dn_representative_transport_at M)(source_dn_representative_transport_definable M)).
 - intros body out renamedbody renamedout r k HB HR HD HBody HOut.
   apply source_dn_zero in HD. subst out. rewrite coding_add_zero_r in HBody.
   apply source_dn_zero. symmetry. exact(source_representative_renaming_functional M r body renamedbody renamedout HBody HOut).
 - intros count IH body out renamedbody renamedout r k HB HR HD HBody HOut.
   apply source_dn_succ in HD. destruct HD as(previous&HD&HS).
   assert(EB:addM M(succM M count)(succM M(succM M k))=
     addM M count(succM M(succM M(succM M k)))).
   { rewrite Arithmetic.add_succ,(Arithmetic.add_comm M count(succM M(succM M(succM M k)))),
      Arithmetic.add_succ,(Arithmetic.add_comm M(succM M(succM M k)) count). reflexivity. }
   rewrite EB in HB.
   destruct(source_dn_successor_representative_transport M previous out r renamedout k
    (source_dn_bounded M count body previous(succM M k) HD HB) HR HS HOut)as(renamed&HName&HSuccessor).
   apply source_dn_succ. exists renamed. split;[|exact HSuccessor].
   apply(IH body previous renamedbody renamed(succM M r)(succM M k));try assumption.
   + intro HBad. apply HR. exact(coding_lt_trans M r(succM M r)(code_numeral M 2)(coding_lt_succ M r) HBad).
   + assert(ER:addM M r(succM M count)=addM M(succM M r) count).
     { rewrite(Arithmetic.add_comm M r(succM M count)),!Arithmetic.add_succ,
        (Arithmetic.add_comm M count r). reflexivity. }
     now rewrite ER in HBody.
Qed.
Print Assumptions source_dn_successor_representative_transport.
Print Assumptions source_dn_representative_transport_definable.
Print Assumptions source_dn_representative_transport.
