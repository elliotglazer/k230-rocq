(** Finite constructor propagation through the literal emitted-closure
    scaffold. The three arbitrary matrix holes retain the actual cutoff
    and reopening actions, at depths 3, 5, and 6 respectively. *)
From Stdlib Require Import List Lia.
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs SetFormulaCodes SetCodeDescent
  SetSchemaConstructors SchemaConstructorBounds NumericalSubstitutionMaps NumericalSubstitution SubstitutionPayloads
  SourceFiniteCutoffShift SourceNativeKShifts SourceNativeKMatrixMaps SourceEmittedClosureRecipe
  SourceNamedScopes SourceFiniteMapLifts SourceDoubleActionInversion NativeKUpCutoff NativeCoreLeafAlignment.
Unset Implicit Arguments.

Definition emitted_leaf_actions M kind matrix out sb sc :=exists cb cc cn db dc dn shifted,
  source_cutoff_shift_map M (native_named_leaf_depth kind) cb cc cn /\
  numerical_substitution M matrix cb cc cn (code_numeral M (S (native_named_leaf_depth kind))) shifted /\
  source_substitution_lifts M (native_named_leaf_depth kind) sb sc (code_numeral M 2) (zeroM M) db dc dn /\
  numerical_substitution M shifted db dc dn (code_numeral M (native_named_leaf_depth kind)) out.

Ltac emitted_frame_graph :=
  lazymatch goal with
  | |-code_relation ?M ?env (E_sf ?h ?A ?B) ?f=>
    match goal with H:sf_relation M h ?x ?y f |-_=>
      let HA:=fresh "frameA" in let HB:=fresh "frameB" in
      assert (HA:code_relation M env A x) by emitted_frame_graph;
      assert (HB:code_relation M env B y) by emitted_frame_graph;
      exact (proj2 (schema_expression_graph M env h A B x y f HA HB) H)
    end
  | _=>reflexivity
  end.

Ltac emitted_double_walk HCode H1 H2 HC HL depth sb sc :=
  lazymatch type of HCode with code_relation ?M ?env ?E ?original=>
  lazymatch type of H1 with numerical_substitution M original ?cb ?cc ?cn ?cbase ?first=>
  lazymatch type of H2 with numerical_substitution M first ?db ?dc ?dn ?dbase ?out=>
  lazymatch E with
  | E_sf SFAll ?A (CEconst 0)=>
    let body:=fresh "body" in let HBody:=fresh "bodyGraph" in
    destruct (code_relation_total M A env) as (body&HBody);
    apply (schema_expression_graph M env SFAll A (CEconst 0) body (zeroM M) original HBody eq_refl) in HCode;
    let nb:=fresh "cutB" in let nc:=fresh "cutC" in let nn:=fresh "cutN" in
    let nd:=fresh "openB" in let ne:=fresh "openC" in let nm:=fresh "openN" in
    let body1:=fresh "body1" in let body2:=fresh "body2" in
    let HL1:=fresh "cutLift" in let HL2:=fresh "openLift" in
    let HS1:=fresh "cutAction" in let HS2:=fresh "openAction" in let HOut:=fresh "outAll" in
    destruct (source_double_quantifier_inv M true body original cb cc cn cbase db dc dn dbase first out HCode H1 H2)
      as (nb&nc&nn&nd&ne&nm&body1&body2&HL1&HL2&HS1&HS2&HOut);
    let newDepth:=eval cbv in (S depth) in
    let HNewC:=fresh "cutScope" in let HNewL:=fresh "openScope" in
    assert (HNewC:source_cutoff_shift_map M newDepth nb nc nn) by (exists cb,cc,cn;split;[exact HC|exact HL1]);
    assert (HNewL:source_substitution_lifts M newDepth sb sc (code_numeral M 2) (zeroM M) nd ne nm)
      by (exists db,dc,dn;split;[exact HL|exact HL2]);
    emitted_double_walk HBody HS1 HS2 HNewC HNewL newDepth sb sc
  | E_sf SFEx ?A (CEconst 0)=>
    let body:=fresh "body" in let HBody:=fresh "bodyGraph" in
    destruct (code_relation_total M A env) as (body&HBody);
    apply (schema_expression_graph M env SFEx A (CEconst 0) body (zeroM M) original HBody eq_refl) in HCode;
    let nb:=fresh "cutB" in let nc:=fresh "cutC" in let nn:=fresh "cutN" in
    let nd:=fresh "openB" in let ne:=fresh "openC" in let nm:=fresh "openN" in
    let body1:=fresh "body1" in let body2:=fresh "body2" in
    let HL1:=fresh "cutLift" in let HL2:=fresh "openLift" in
    let HS1:=fresh "cutAction" in let HS2:=fresh "openAction" in let HOut:=fresh "outEx" in
    destruct (source_double_quantifier_inv M false body original cb cc cn cbase db dc dn dbase first out HCode H1 H2)
      as (nb&nc&nn&nd&ne&nm&body1&body2&HL1&HL2&HS1&HS2&HOut);
    let newDepth:=eval cbv in (S depth) in
    let HNewC:=fresh "cutScope" in let HNewL:=fresh "openScope" in
    assert (HNewC:source_cutoff_shift_map M newDepth nb nc nn) by (exists cb,cc,cn;split;[exact HC|exact HL1]);
    assert (HNewL:source_substitution_lifts M newDepth sb sc (code_numeral M 2) (zeroM M) nd ne nm)
      by (exists db,dc,dn;split;[exact HL|exact HL2]);
    emitted_double_walk HBody HS1 HS2 HNewC HNewL newDepth sb sc
  | E_sf SFMember (CEconst ?i) (CEconst ?j)=>
    apply (schema_expression_graph M env SFMember (CEconst i) (CEconst j)
      (code_numeral M i) (code_numeral M j) original eq_refl eq_refl) in HCode;
    let HFixed:=fresh "fixedAtom" in
    pose proof (source_double_fixed_atom M false i j original first out depth cb cc cn sb sc db dc dn
      ltac:(lia) ltac:(lia) HCode HC HL H1 H2) as HFixed
  | E_sf ?h ?A ?B=>
    let x:=fresh "left" in let y:=fresh "right" in let HX:=fresh "leftGraph" in let HY:=fresh "rightGraph" in
    destruct (code_relation_total M A env) as (x&HX);
    destruct (code_relation_total M B env) as (y&HY);
    apply (schema_expression_graph M env h A B x y original HX HY) in HCode;
    let x1:=fresh "left1" in let y1:=fresh "right1" in let x2:=fresh "left2" in let y2:=fresh "right2" in
    let HSX:=fresh "leftCut" in let HSY:=fresh "rightCut" in
    let HRX:=fresh "leftOpen" in let HRY:=fresh "rightOpen" in let HOut:=fresh "outBinary" in
    destruct (source_double_binary_inv M h x y original cb cc cn cbase db dc dn dbase first out
      ltac:(unfold sf_binary;auto) HCode H1 H2) as (x1&y1&x2&y2&HSX&HSY&HRX&HRY&HOut);
    emitted_double_walk HX HSX HRX HC HL depth sb sc;
    emitted_double_walk HY HSY HRY HC HL depth sb sc
  | CEvar ?i=>
    cbn [code_relation] in HCode;rewrite HCode in H1;
    let kind:=lazymatch i with 0=>constr:(NativeKA)|1=>constr:(NativeKB)|2=>constr:(NativeKC) end in
    let HLeaf:=fresh "emittedLeaf" in
    assert (HLeaf:emitted_leaf_actions M kind (env i) out sb sc)
      by (exists cb,cc,cn,db,dc,dn,first;repeat first [assumption|split])
  end end end end.

Theorem source_emitted_double_action M matrixA matrixB matrixC original shifted out sb sc db dc dn :
  code_relation M (schema_env3 matrixA matrixB matrixC)
    (E_source_emitted_closure (CEvar 0)(CEvar 1)(CEvar 2)) original ->
  source_native_k_upshift M original shifted ->
  source_substitution_lifts M 1 sb sc (code_numeral M 2) (zeroM M) db dc dn ->
  numerical_substitution M shifted db dc dn (code_numeral M 1) out ->
  exists qA qB qC,emitted_leaf_actions M NativeKA matrixA qA sb sc /\
    emitted_leaf_actions M NativeKB matrixB qB sb sc /\emitted_leaf_actions M NativeKC matrixC qC sb sc /\
    code_relation M (schema_env3 qA qB qC)
      (E_source_emitted_closure (CEvar 0)(CEvar 1)(CEvar 2)) out.
Proof.
  intros HCode HShift HOpen HL.
  pose proof (native_k_upshift_substitution M original shifted HShift) as HFirst.
  pose proof (native_k_upshift_cutoff_map M) as HCut.
  unfold E_source_emitted_closure,E_native_subset02,E_sf_all,E_sf_ex,E_sf_mem in HCode.
  emitted_double_walk HCode HFirst HL HCut HOpen 1 sb sc.
  match goal with
  | HA:emitted_leaf_actions M NativeKA _ ?qA sb sc,
    HB:emitted_leaf_actions M NativeKB _ ?qB sb sc,
    HC:emitted_leaf_actions M NativeKC _ ?qC sb sc |-_=>exists qA,qB,qC;
      split;[exact HA|];split;[exact HB|];split;[exact HC|]
  end.
  unfold E_source_emitted_closure,E_native_subset02,E_sf_all,E_sf_ex,E_sf_mem.
  cbn [substitution_source_quantifier substitution_source_atom] in *.
  emitted_frame_graph.
Qed.

Print Assumptions source_emitted_double_action.
