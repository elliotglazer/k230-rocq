(** The exact Dn successor preserves an actual two-premise source theorem. *)
From PAModel Require Import Model FiniteCoding FiniteCRT CodeExpressions SetFormulaCodes SourceBounded
 SourceDnStep NumericalRenaming SourceDescriptorProvability SourceDescriptorClosure SourceDescriptorBinaryUniversalMap.
Unset Implicit Arguments.

Theorem source_descriptor_dn_successor_binary_map M T a b c outA outB outC bc point targetbc result k :
 source_bounded M a(succM M(succM M(succM M k))) ->
 source_bounded M b(succM M(succM M(succM M k))) ->
 source_bounded M c(succM M(succM M(succM M k))) ->
 source_dn_successor M a outA ->source_dn_successor M b outB ->source_dn_successor M c outC ->
 sf_relation M SFImpl b c bc ->sf_relation M SFImpl a bc point ->
 sf_relation M SFImpl outB outC targetbc ->sf_relation M SFImpl outA targetbc result ->
 source_descriptor_provable M T point ->source_descriptor_provable M T result.
Proof.
 intros BA BB BC(ra&guard&ga&HRA&HG&HGA&HQA)
  (rb&guardB&gb&HRB&HGB0&HGB&HQB)(rc&guardC&gc&HRC&HGC0&HGC&HQC) HBC HP HTBC HResult PP.
 assert(guardB=guard)by(eapply sf_relation_functional;eassumption). subst guardB.
 assert(guardC=guard)by(eapply sf_relation_functional;eassumption). subst guardC.
 destruct(sf_relation_total M SFImpl rb rc)as(rbc&HRBC).
 destruct(sf_relation_total M SFImpl ra rbc)as(rotpoint&HRotPoint).
 assert(HRenBC:numerical_renaming M bc(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M) rbc).
 { apply(proj2(numerical_renaming_binary M SFImpl b c bc _ _ _ _ rbc(or_intror(or_intror eq_refl)) HBC)).
   exists rb,rc. exact(conj HRB(conj HRC HRBC)). }
 assert(HRen:numerical_renaming M point(code_numeral M 1653)(code_numeral M 6)(code_numeral M 3)(zeroM M) rotpoint).
 { apply(proj2(numerical_renaming_binary M SFImpl a bc point _ _ _ _ rotpoint(or_intror(or_intror eq_refl)) HP)).
   exists ra,rbc. exact(conj HRA(conj HRenBC HRotPoint)). }
 pose proof(source_descriptor_provable_renaming M T point _ _ _ _ rotpoint PP HRen)as PRot.
 pose proof(source_dn_rotate_bounded M a ra k BA HRA)as BRA.
 pose proof(source_dn_rotate_bounded M b rb k BB HRB)as BRB.
 pose proof(source_dn_rotate_bounded M c rc k BC HRC)as BRC.
 assert(BGuard:source_bounded M guard(succM M(succM M(succM M k)))).
 { apply(proj2(source_bounded_accept_atom M SFMember _ _ guard _ (or_introl eq_refl) HG)).
   split;[apply coding_zero_lt_succ|]. do 2 apply coding_lt_succ_cancel. apply coding_zero_lt_succ. }
 destruct(sf_relation_total M SFImpl gb gc)as(gbc&HGBC).
 destruct(sf_relation_total M SFImpl ga gbc)as(gpoint&HGPoint).
 pose proof(source_descriptor_binary_guard_map M T ra rb rc guard rbc rotpoint ga gb gc gbc gpoint
   (succM M(succM M(succM M k))) BRA BRB BRC BGuard HRBC HRotPoint HGA HGB HGC HGBC HGPoint PRot)as PG.
 assert(BGA:source_bounded M ga(succM M(succM M(succM M k)))).
 { exact(proj2(source_bounded_accept_binary M SFImpl guard ra ga _ (or_intror(or_intror eq_refl)) HGA)(conj BGuard BRA)). }
 assert(BGB:source_bounded M gb(succM M(succM M(succM M k)))).
 { exact(proj2(source_bounded_accept_binary M SFImpl guard rb gb _ (or_intror(or_intror eq_refl)) HGB)(conj BGuard BRB)). }
 assert(BGC:source_bounded M gc(succM M(succM M(succM M k)))).
 { exact(proj2(source_bounded_accept_binary M SFImpl guard rc gc _ (or_intror(or_intror eq_refl)) HGC)(conj BGuard BRC)). }
 destruct(sf_relation_total M SFAll gbc(zeroM M))as(qbc&HQBC).
 destruct(sf_relation_total M SFImpl outA qbc)as(first&HFirst).
 exact(source_descriptor_binary_universal_map M T ga gb gc gbc gpoint outA outB outC qbc first targetbc result
   (succM M(succM M(succM M k))) BGA BGB BGC HGBC HGPoint HQA HQB HQC HQBC HFirst HTBC HResult PG).
Qed.
Print Assumptions source_descriptor_dn_successor_binary_map.
