(** Literal constructor shells of the actual fixed STot and SInd use laws. *)
From PAModel Require Import Model FiniteCoding CodeExpressions SetFormulaCodes OldNamedSyntaxBridge OldFullNDSourceBridge
 SourceFiniteParameters SourceFiniteNameParameters SourceRecursionPrimitiveRelations SourceRecursionParameterCalibration
 SourceRecursionSuccessorCalibration SourceRecursionSuccessorIn SourceRecursionInductionGraphs SourceRecursionInductionFixed
 SourceRawSubset SourcePropositionalRebase SchemaConstructorBounds SetSchemaConstructors SourceZFRProvability.
From OldZF Require Std_setrec Std_setinf.
Unset Implicit Arguments.

Theorem source_rec_totality_use_shell M N z law:
 code_relation M(source_rec_env3 N z N)
  (source_parameter_expression(source_finite_parameter_names 3)(source_rec_induction_law false))law ->
 exists totality member ex tail,
 source_rec_totality M N totality /\sf_relation M SFMember z N member /\source_rec_successor_in M z N ex /\
 sf_relation M SFImpl member ex tail /\sf_relation M SFImpl totality tail law.
Proof.
 intro HG. set(rho:=source_rec_env3 N z N). set(names:=source_finite_parameter_names 3).
 set(TT:=source_parameter_expression names(isolated_formula(OldZF.Std_setrec.STot OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 0)))).
 set(MX:=E_sf SFMember(names 1)(names 0)).
 set(up:=source_parameter_up names).
 set(SS:=source_parameter_expression up(isolated_formula(OldZF.Std_setrec.Rel2 OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 2)(@OC.var OB.sig_empty 0)))).
 set(MN:=E_sf SFMember(up 0)(up 1)).
 set(EX:=E_sf SFEx(E_sf SFAnd SS MN)(CEconst 0)).
 change(code_relation M rho(E_sf SFImpl TT(E_sf SFImpl MX EX))law)in HG.
 destruct(schema_expression_split M rho SFImpl _ _ law HG)as(totality&tail&HT&HTail&HL).
 destruct(schema_expression_split M rho SFImpl _ _ tail HTail)as(member&ex&HM&HEx&HI).
 pose proof(source_parameter_rec_totality M names rho 0 N totality eq_refl HT)as HTotality.
 pose proof(proj1(schema_expression_graph M rho SFMember (names 1) (names 0) z N member eq_refl eq_refl)HM)as HMember.
 destruct(schema_expression_split M rho SFEx (E_sf SFAnd SS MN) (CEconst 0) ex HEx)as(body&z0&HB&HZ&HE). change(z0=zeroM M)in HZ. subst z0.
 destruct(schema_expression_split M rho SFAnd SS MN body HB)as(successor&mem&HS&HMem&HAnd).
 assert(U0:code_relation M rho(up 0)(zeroM M))by reflexivity.
 assert(U1:code_relation M rho(up 1)(succM M N)).
 { apply(source_parameter_up_name M names rho 0 N). reflexivity. }
 assert(U2:code_relation M rho(up 2)(succM M z)).
 { apply(source_parameter_up_name M names rho 1 z). reflexivity. }
 pose proof(source_parameter_rec_rel2_successor M up rho 2 0 _ _ successor U2 U0 HS)as HSuccessor.
 pose proof(proj1(schema_expression_graph M rho SFMember _ _ (zeroM M)(succM M N)mem U0 U1)HMem)as HMemGraph.
 exists totality,member,ex,tail. split;[exact HTotality|]. split;[exact HMember|].
 split;[exists successor,mem,body;auto|]. auto.
Qed.

Theorem source_zfr_rec_totality_use_total M N z:exists totality member ex tail law,
 source_rec_totality M N totality /\sf_relation M SFMember z N member /\source_rec_successor_in M z N ex /\
 sf_relation M SFImpl member ex tail /\sf_relation M SFImpl totality tail law /\source_zfr_provable M law.
Proof.
 destruct(code_relation_total M(source_parameter_expression(source_finite_parameter_names 3)(source_rec_induction_law false))(source_rec_env3 N z N))as(law&HG).
 destruct(source_rec_totality_use_shell M N z law HG)as(totality&member&ex&tail&HT&HM&HE&HI&HL).
 exists totality,member,ex,tail,law. split;[exact HT|]. split;[exact HM|]. split;[exact HE|]. split;[exact HI|]. split;[exact HL|].
 exact(source_zfr_rec_induction_named M false(source_rec_env3 N z N)law HG).
Qed.

Theorem source_rec_induction_use_shell M o N X law:
 code_relation M(source_rec_env3 o N X)
  (source_parameter_expression(source_finite_parameter_names 3)(source_rec_induction_law true))law ->
 exists induction member closed subset t1 t2,
 source_rec_induction M o N induction /\sf_relation M SFMember o X member /\source_rec_successor_closed M X closed /\
 source_raw_subset_graph M N X subset /\sf_relation M SFImpl closed subset t2 /\sf_relation M SFImpl member t2 t1 /\
 sf_relation M SFImpl induction t1 law.
Proof.
 intro HG. set(rho:=source_rec_env3 o N X). set(names:=source_finite_parameter_names 3).
 set(II:=source_parameter_expression names(isolated_formula(OldZF.Std_setrec.SInd OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 0)(@OC.var OB.sig_empty 1)))).
 set(MO:=E_sf SFMember(names 0)(names 2)). set(up:=source_parameter_up names). set(up2:=source_parameter_up up).
 set(MX:=E_sf SFMember(up 0)(up 3)).
 set(SS:=source_parameter_expression up2(isolated_formula(OldZF.Std_setrec.Rel2 OldZF.Std_setinf.phSig(@OC.var OB.sig_empty 1)(@OC.var OB.sig_empty 0)))).
 set(MV:=E_sf SFMember(up2 0)(up2 4)).
 set(EX:=E_sf SFEx(E_sf SFAnd SS MV)(CEconst 0)).
 set(CL:=E_sf SFAll(E_sf SFImpl MX EX)(CEconst 0)).
 set(MN:=E_sf SFMember(up 0)(up 2)).
 set(SB:=E_sf SFAll(E_sf SFImpl MN MX)(CEconst 0)).
 change(code_relation M rho(E_sf SFImpl II(E_sf SFImpl MO(E_sf SFImpl CL SB)))law)in HG.
 destruct(schema_expression_split M rho SFImpl _ _ law HG)as(induction&t1&HI&HT1&HL).
 destruct(schema_expression_split M rho SFImpl _ _ t1 HT1)as(member&t2&HM&HT2&H1).
 destruct(schema_expression_split M rho SFImpl _ _ t2 HT2)as(closed&subset&HC&HS&H2).
 pose proof(source_parameter_rec_induction M names rho 0 1 o N induction eq_refl eq_refl HI)as HInduction.
 pose proof(proj1(schema_expression_graph M rho SFMember (names 0) (names 2) o X member eq_refl eq_refl)HM)as HOM.
 assert(U0:code_relation M rho(up 0)(zeroM M))by reflexivity.
 assert(U2:code_relation M rho(up 2)(succM M N)).
 { apply(source_parameter_up_name M names rho 1 N). reflexivity. }
 assert(U3:code_relation M rho(up 3)(succM M X)).
 { apply(source_parameter_up_name M names rho 2 X). reflexivity. }
 destruct(schema_expression_split M rho SFAll (E_sf SFImpl MX EX) (CEconst 0) closed HC)as(point&z0&HP&HZ&HAll). change(z0=zeroM M)in HZ. subst z0.
 destruct(schema_expression_split M rho SFImpl MX EX point HP)as(mx&ex&HMX&HEX&HPoint).
 pose proof(proj1(schema_expression_graph M rho SFMember _ _ (zeroM M)(succM M X)mx U0 U3)HMX)as HMXGraph.
 destruct(schema_expression_split M rho SFEx (E_sf SFAnd SS MV) (CEconst 0) ex HEX)as(body&z0&HB&HZ&HEx). change(z0=zeroM M)in HZ. subst z0.
 destruct(schema_expression_split M rho SFAnd SS MV body HB)as(successor&mv&HSuccessor&HMember&HBody).
 assert(V0:code_relation M rho(up2 0)(zeroM M))by reflexivity.
 assert(V1:code_relation M rho(up2 1)(succM M(zeroM M))).
 { apply(source_parameter_up_name M up rho 0(zeroM M)). exact U0. }
 assert(V4:code_relation M rho(up2 4)(succM M(succM M X))).
 { apply(source_parameter_up_name M up rho 3(succM M X)). exact U3. }
 pose proof(source_parameter_rec_rel2_successor M up2 rho 1 0 _ _ successor V1 V0 HSuccessor)as HSuc.
 pose proof(proj1(schema_expression_graph M rho SFMember _ _ (zeroM M)(succM M(succM M X))mv V0 V4)HMember)as HMV.
 assert(HClosed:source_rec_successor_closed M X closed).
 { exists mx,ex,point. split;[exact HMXGraph|]. split;[exists successor,mv,body;auto|]. auto. }
 destruct(schema_expression_split M rho SFAll (E_sf SFImpl MN MX) (CEconst 0) subset HS)as(spoint&z0&HSP&HZ&HSA). change(z0=zeroM M)in HZ. subst z0.
 destruct(schema_expression_split M rho SFImpl MN MX spoint HSP)as(mn&mx'&HMN&HMX'&HSI).
 pose proof(proj1(schema_expression_graph M rho SFMember _ _ (zeroM M)(succM M N)mn U0 U2)HMN)as HMNGraph.
 pose proof(proj1(schema_expression_graph M rho SFMember _ _ (zeroM M)(succM M X)mx' U0 U3)HMX')as HMXGraph'.
 exists induction,member,closed,subset,t1,t2. split;[exact HInduction|]. split;[exact HOM|]. split;[exact HClosed|].
 split;[exists mn,mx',spoint;auto|]. auto.
Qed.

Theorem source_zfr_rec_induction_use_total M o N X:exists induction member closed subset t1 t2 law,
 source_rec_induction M o N induction /\sf_relation M SFMember o X member /\source_rec_successor_closed M X closed /\
 source_raw_subset_graph M N X subset /\sf_relation M SFImpl closed subset t2 /\sf_relation M SFImpl member t2 t1 /\
 sf_relation M SFImpl induction t1 law /\source_zfr_provable M law.
Proof.
 destruct(code_relation_total M(source_parameter_expression(source_finite_parameter_names 3)(source_rec_induction_law true))(source_rec_env3 o N X))as(law&HG).
 destruct(source_rec_induction_use_shell M o N X law HG)as(induction&member&closed&subset&t1&t2&HI&HM&HC&HS&H2&H1&HL).
 exists induction,member,closed,subset,t1,t2,law. split;[exact HI|]. split;[exact HM|]. split;[exact HC|]. split;[exact HS|].
 split;[exact H2|]. split;[exact H1|]. split;[exact HL|]. exact(source_zfr_rec_induction_named M true(source_rec_env3 o N X)law HG).
Qed.
Print Assumptions source_rec_totality_use_shell.
Print Assumptions source_zfr_rec_totality_use_total.
Print Assumptions source_rec_induction_use_shell.
Print Assumptions source_zfr_rec_induction_use_total.
