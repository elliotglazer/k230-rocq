(** A real uniform source proof sends an attempt for the false relation
    to an attempt for any internally coded binary relation. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes SourceBounded SourceRecursionPrimitiveRelations SourceRecursionPrimitiveTransport
 SourceRecursionAttempt SourceRecursionAttemptBounds SourceRecursionAttemptStepShell SourceZFRPositiveMaps SourceZFRProvability.
Unset Implicit Arguments.
Ltac rec_all_bounds:=repeat first[
 match goal with H:source_bounded ?M ?out ?k,HG:sf_relation ?M SFAll ?a (zeroM ?M) ?out |- _ =>
  match goal with _:source_bounded M a(succM M k) |- _=>fail 1|_=>
   let HB:=fresh "Bound" in pose proof(proj1(source_bounded_accept_unary M SFAll a out k(or_introl eq_refl)HG)H)as HB end
 end|
 match goal with H:source_bounded ?M ?out ?k,HG:sf_relation ?M SFEx ?a (zeroM ?M) ?out |- _ =>
  match goal with _:source_bounded M a(succM M k) |- _=>fail 1|_=>
   let HB:=fresh "Bound" in pose proof(proj1(source_bounded_accept_unary M SFEx a out k(or_intror eq_refl)HG)H)as HB end
 end|
 match goal with H:source_bounded ?M ?out ?k,HG:sf_relation ?M SFAnd ?a ?b ?out |- _ =>
  match goal with _:source_bounded M a k |- _=>fail 1|_=>
   let HB:=fresh "Bound" in pose proof(proj1(proj1(source_bounded_accept_binary M SFAnd a b out k(or_introl eq_refl)HG)H))as HB end
 end|
 match goal with H:source_bounded ?M ?out ?k,HG:sf_relation ?M SFAnd ?a ?b ?out |- _ =>
  match goal with _:source_bounded M b k |- _=>fail 1|_=>
   let HB:=fresh "Bound" in pose proof(proj2(proj1(source_bounded_accept_binary M SFAnd a b out k(or_introl eq_refl)HG)H))as HB end
 end|
 match goal with H:source_bounded ?M ?out ?k,HG:sf_relation ?M SFImpl ?a ?b ?out |- _ =>
  match goal with _:source_bounded M a k |- _=>fail 1|_=>
   let HB:=fresh "Bound" in pose proof(proj1(proj1(source_bounded_accept_binary M SFImpl a b out k(or_intror(or_intror eq_refl))HG)H))as HB end
 end|
 match goal with H:source_bounded ?M ?out ?k,HG:sf_relation ?M SFImpl ?a ?b ?out |- _ =>
  match goal with _:source_bounded M b k |- _=>fail 1|_=>
   let HB:=fresh "Bound" in pose proof(proj2(proj1(source_bounded_accept_binary M SFImpl a b out k(or_intror(or_intror eq_refl))HG)H))as HB end
 end].
Theorem source_zfr_rec_bottom_attempt_map M phi o a N f old new k:
 source_bounded M phi(code_numeral M 2) ->coding_lt M o k ->coding_lt M a k ->coding_lt M N k ->coding_lt M f k ->
 source_rec_attempt M(zeroM M)o a N f old ->source_rec_attempt M phi o a N f new ->source_zfr_map M old new.
Proof.
 intros BP BO BA BN BF HOld HNew.
 pose proof(source_rec_attempt_bounded M(zeroM M)o a N f old k(source_bounded_accept_falsity M(code_numeral M 2))BO BA BN BF HOld)as BOld.
 pose proof(source_rec_attempt_bounded M phi o a N f new k BP BO BA BN BF HNew)as BNew.
 destruct HOld as(first&oldStep&HF&HS&HO). destruct HNew as(first'&newStep&HF'&HS'&HN).
 pose proof(source_rec_attempt_zero_functional M o a f first' first HF' HF)as E. subst first'.
 destruct(source_rec_attempt_step_shell M(zeroM M)N f oldStep HS)
  as(guard&successor&appOut&appIn&body0&ex0&t30&t20&point0&one0&two0&HG&HSuc&HAppOut&HAppIn&HBody0&HEx0&H30&H20&HPoint0&HOne0&HTwo0&HOuter0).
 destruct(source_rec_attempt_step_shell M phi N f newStep HS')
  as(guard'&successor'&appOut'&appIn'&body&ex&t3&t2&point&one&two&HG'&HSuc'&HAppOut'&HAppIn'&HBody&HEx&H3&H2&HPoint&HOne&HTwo&HOuter).
 pose proof(sf_relation_functional M SFMember _ _ guard' guard HG' HG)as E. subst guard'.
 pose proof(source_rec_successor_functional M _ _ successor' successor HSuc' HSuc)as E. subst successor'.
 pose proof(source_rec_app_functional M _ _ _ appOut' appOut HAppOut' HAppOut)as E. subst appOut'.
 pose proof(source_rec_app_functional M _ _ _ appIn' appIn HAppIn' HAppIn)as E. subst appIn'.
 rec_all_bounds.
 assert(MapBody:source_zfr_map M body0 body).
 { eapply source_zfr_map_right;[left;reflexivity| | | |exact HBody0|exact HBody|];try eassumption.
   apply(source_zfr_map_from_false M phi(succM M(succM M(succM M(succM M k))))). assumption. }
 assert(MapEx:source_zfr_map M ex0 ex).
 { eapply source_zfr_map_quantifier;[right;reflexivity| | |exact HEx0|exact HEx|exact MapBody];eassumption. }
 assert(Map3:source_zfr_map M t30 t3).
 { eapply source_zfr_map_right;[right;right;reflexivity| | | |exact H30|exact H3|exact MapEx];eassumption. }
 assert(Map2:source_zfr_map M t20 t2).
 { eapply source_zfr_map_right;[right;right;reflexivity| | | |exact H20|exact H2|exact Map3];eassumption. }
 assert(MapPoint:source_zfr_map M point0 point).
 { eapply source_zfr_map_right;[right;right;reflexivity| | | |exact HPoint0|exact HPoint|exact Map2];eassumption. }
 assert(MapOne:source_zfr_map M one0 one).
 { eapply source_zfr_map_quantifier;[left;reflexivity| | |exact HOne0|exact HOne|exact MapPoint];eassumption. }
 assert(MapTwo:source_zfr_map M two0 two).
 { eapply source_zfr_map_quantifier;[left;reflexivity| | |exact HTwo0|exact HTwo|exact MapOne];eassumption. }
 assert(MapStep:source_zfr_map M oldStep newStep).
 { eapply source_zfr_map_quantifier;[left;reflexivity| | |exact HOuter0|exact HOuter|exact MapTwo];eassumption. }
 eapply source_zfr_map_right;[left;reflexivity| | | |exact HO|exact HN|exact MapStep];eassumption.
Qed.
Print Assumptions source_zfr_rec_bottom_attempt_map.
