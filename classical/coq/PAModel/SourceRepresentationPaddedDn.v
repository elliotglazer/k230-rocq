(** Guarded assignment closure with arbitrary extra set parameters. Their
    initial names are moved above the internally many assignment slots. *)
From PAModel Require Import Model Arithmetic FiniteCoding FiniteCRT BetaExtension BetaPacking
 CodeExpressions NumericalProofs SetFormulaCodes SourceBounded SourceBoundMonotone SourceRenamingBounds
 SourceRepresentationPadding SourceDnConditionalStep SourceDnStep SourceDn SourceDnBounds
 SourceDescriptorProvability SourceDescriptorClosure SourceQuantifierRules NumericalRenamingMaps NumericalRenaming.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.
#[local] Existing Instance PA_funcs_signature | 0.
#[local] Existing Instance PA_preds_signature | 0.

Theorem source_representation_padding_bounded M count f g k :source_bounded M f k ->
 source_representation_padding M count f g ->source_bounded M g(addM M count k).
Proof.
 intros HF HG. apply(numerical_renaming_preserves_bound M f _ _ _ _ g k(addM M count k) HF HG).
 intros i j HI HJ. destruct(NumericalEnvironments.environment_lt_cases M i(code_numeral M 2))as[HSmall|HLarge].
 - assert(EJ:j=i)by(eapply renaming_lookup_functional;[exact HJ|apply representation_padding_inside_lookup;exact HSmall]).
   subst j. apply(source_bound_lt_le M i k(addM M count k) HI).
   rewrite Arithmetic.add_comm. apply coding_le_add.
 - assert(EJ:j=addM M i count)by(eapply renaming_lookup_functional;[exact HJ|apply representation_padding_outside_lookup;exact HLarge]).
   subst j. rewrite(Arithmetic.add_comm M i count). exact(coding_lt_add_left M count i k HI).
Qed.

Theorem source_descriptor_dn_padded_successor_intro M T condition padded previous out point result k :
 source_bounded M condition(succM M(succM M k)) ->
 source_bounded M previous(succM M(succM M(succM M k))) ->
 source_representation_padding M(code_numeral M 1) condition padded ->
 source_dn_successor M previous out ->sf_relation M SFImpl padded previous point ->
 sf_relation M SFImpl condition out result ->source_descriptor_provable M T point ->
 source_descriptor_provable M T result.
Proof.
 intros HC HP HPad(rot&guard&guarded&HR&HG&HGuard&HAll) HPoint HResult PP.
 destruct(numerical_renaming_total M padded(code_numeral M 1653)(code_numeral M 6)
   (code_numeral M 3)(zeroM M))as(shifted&HS).
 destruct(numerical_renaming_total M condition(zeroM M)(zeroM M)(zeroM M)(code_numeral M 1))as(shifted'&HS').
 pose proof(source_representation_padding_rotate_shift M condition padded shifted' shifted
   (succM M(succM M k)) HC HPad HS' HS)as E. subst shifted'.
 destruct(sf_relation_total M SFImpl shifted rot)as(rotpoint&HRotPoint).
 assert(HRPoint:numerical_renaming M point(code_numeral M 1653)(code_numeral M 6)
    (code_numeral M 3)(zeroM M) rotpoint).
 { apply(proj2(numerical_renaming_binary M SFImpl padded previous point _ _ _ _ rotpoint
    (or_intror(or_intror eq_refl)) HPoint)). exists shifted,rot. exact(conj HS(conj HR HRotPoint)). }
 apply(source_descriptor_conditional_guarded_all_intro M T condition shifted rot guard rotpoint guarded out result
   (succM M(succM M k)));try assumption.
 - exact(source_dn_rotate_bounded M previous rot k HP HR).
 - apply(proj2(source_bounded_accept_atom M SFMember _ _ guard(succM M(succM M(succM M k)))
    (or_introl eq_refl) HG)). split;[apply coding_zero_lt_succ|].
   do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ.
 - exact(source_descriptor_provable_renaming M T point _ _ _ _ rotpoint PP HRPoint).
Qed.

Definition source_dn_padded_intro_at M T count :=forall condition padded body result k point out,
 source_bounded M condition(succM M(succM M k)) ->
 source_bounded M body(addM M count(succM M(succM M k))) ->
 source_representation_padding M count condition padded ->source_dn M count body result ->
 sf_relation M SFImpl padded body point ->sf_relation M SFImpl condition result out ->
 source_descriptor_provable M T point ->source_descriptor_provable M T out.
Definition source_dn_padded_intro_formula T :form :=∀∀∀∀∀∀∀(
 source_bounded_accept_formula $6(σ(σ $2)) →source_bounded_accept_formula $4($7 ⊕ σ(σ $2)) →
 source_representation_padding_formula $7 $6 $5 →source_dn_formula $7 $4 $3 →
 sf_formula SFImpl $5 $4 $1 →sf_formula SFImpl $6 $3 $0 →
 source_descriptor_provable_formula T $1 →source_descriptor_provable_formula T $0).
Local Opaque holds source_bounded_accept_formula source_representation_padding_formula source_dn_formula
 sf_formula source_descriptor_provable_formula.
Lemma source_dn_padded_intro_definable M T :Definable1 M(source_dn_padded_intro_at M T).
Proof.
 exists(source_dn_padded_intro_formula T),(fun _=>zeroM M). intro count.
 unfold source_dn_padded_intro_formula,source_dn_padded_intro_at.
 repeat setoid_rewrite holds_all. repeat setoid_rewrite holds_imp.
 setoid_rewrite source_bounded_accept_formula_correct. setoid_rewrite source_representation_padding_formula_correct.
 setoid_rewrite source_dn_formula_correct. setoid_rewrite sf_formula_correct.
 setoid_rewrite source_descriptor_provable_formula_correct. reflexivity.
Qed.
Theorem source_descriptor_dn_padded_intro M T count :source_dn_padded_intro_at M T count.
Proof.
 revert count. apply(definable_induction M(source_dn_padded_intro_at M T)(source_dn_padded_intro_definable M T)).
 - intros condition padded body result k point out HC HB HPad HD HP HO PP.
   assert(E:padded=condition).
   { exact(source_representation_padding_functional M(zeroM M) condition padded condition HPad
      (source_representation_padding_zero M condition(succM M(succM M k)) HC)). }
   subst padded. apply source_dn_zero in HD. subst result.
   rewrite(sf_relation_functional M SFImpl condition body out point HO HP). exact PP.
 - intros count IH condition padded body result k point out HC HB HPad HD HP HO PP.
   apply source_dn_succ in HD. destruct HD as(previous&HD&HS).
   assert(E:addM M(succM M count)(succM M(succM M k))=
     addM M count(succM M(succM M(succM M k)))).
   { rewrite Arithmetic.add_succ,(Arithmetic.add_comm M count(succM M(succM M(succM M k)))),
      Arithmetic.add_succ,(Arithmetic.add_comm M(succM M(succM M k)) count). reflexivity. }
   rewrite E in HB.
   destruct(source_representation_padding_total M(code_numeral M 1) condition)as(first&HFirst).
   destruct(source_representation_padding_total M count first)as(again&HAgain).
   assert(HCombined:source_representation_padding M(succM M count) condition again).
   { pose proof(source_representation_padding_composition M(code_numeral M 1) count condition first again
      (succM M(succM M k)) HC HFirst HAgain)as H.
     change(source_representation_padding M(addM M(succM M(zeroM M)) count) condition again)in H.
     now rewrite Arithmetic.add_succ,Arithmetic.add_zero in H. }
   assert(EAgain:again=padded)by(eapply source_representation_padding_functional;eassumption). subst again.
   assert(BFirst:source_bounded M first(succM M(succM M(succM M k)))).
   { pose proof(source_representation_padding_bounded M(code_numeral M 1) condition first
      (succM M(succM M k)) HC HFirst)as H.
     change(source_bounded M first(addM M(succM M(zeroM M))(succM M(succM M k))))in H.
     now rewrite Arithmetic.add_succ,Arithmetic.add_zero in H. }
   destruct(sf_relation_total M SFImpl first previous)as(previousPoint&HPreviousPoint).
   pose proof(IH first padded body previous(succM M k) point previousPoint BFirst HB HAgain HD HP HPreviousPoint PP)as PPrevious.
   exact(source_descriptor_dn_padded_successor_intro M T condition first previous result previousPoint out k HC
     (source_dn_bounded M count body previous(succM M k) HD HB) HFirst HS HPreviousPoint HO PPrevious).
Qed.
Print Assumptions source_representation_padding_bounded.
Print Assumptions source_descriptor_dn_padded_successor_intro.
Print Assumptions source_dn_padded_intro_definable.
Print Assumptions source_descriptor_dn_padded_intro.
