(** Exact quotient-Replacement interface for source-defined binary matrices.
    The domain Replacement certificate remains an explicit premise. *)
From PAModel Require Import Model Arithmetic FiniteCoding CodeExpressions SetFormulaCodes
  NumericalEnvironments NumericalQuotation QuotationFunctionality QuotationHygiene
  QuotationPayloads QuotationSchemaSkeleton SetSchemaConstructors SourceBounded
  SchemaRenamingDescriptors SchemaImageReduction NumericalEquivalence ReplacementMatrixQuotation.
Unset Implicit Arguments.

Definition replacement_level M k n := Nat.iter n (succM M) k.

Definition domain_replacement_graph M k thetaA thetaB thetaC eq left right q :=
  exists impB impA allz ally allx rhs exx forward backward iffcode allout exb allrange,
    quotation_binary M SFImpl thetaB eq impB /\
    quotation_binary M SFImpl thetaA impB impA /\
    quotation_quantifier M true (replacement_level M k 2) (code_numeral M 1) impA allz /\
    quotation_quantifier M true (replacement_level M k 1) (code_numeral M 1) allz ally /\
    quotation_quantifier M true k (code_numeral M 1) ally allx /\
    quotation_binary M SFAnd right thetaC rhs /\
    quotation_quantifier M false (replacement_level M k 3) (code_numeral M 1) rhs exx /\
    quotation_binary M SFImpl left exx forward /\
    quotation_binary M SFImpl exx left backward /\
    quotation_binary M SFAnd forward backward iffcode /\
    quotation_quantifier M true (replacement_level M k 2) (code_numeral M 1) iffcode allout /\
    quotation_quantifier M false (replacement_level M k 1) (code_numeral M 1) allout exb /\
    quotation_quantifier M true k (code_numeral M 1) exb allrange /\
    quotation_binary M SFImpl allx allrange q.

(** This premise is restricted to actual source quotations; arbitrary
    representative-sensitive raw predicates are deliberately excluded. *)
Definition quoted_domain_replacement_certificates M marker :=
  forall phi bound eb ec en k thetaA thetaB thetaC eq left right q,
    source_bounded M phi bound -> quotation_safe M eb ec en k (code_numeral M 1) ->
    binary_matrix_quotation M phi eb ec en k (replacement_level M k 1)
      (replacement_level M k 3) (code_numeral M 1) thetaA ->
    binary_matrix_quotation M phi eb ec en k (replacement_level M k 2)
      (replacement_level M k 3) (code_numeral M 1) thetaB ->
    binary_matrix_quotation M phi eb ec en (replacement_level M k 3) (replacement_level M k 2)
      (replacement_level M k 4) (code_numeral M 1) thetaC ->
    quotation_atom M true (replacement_level M k 1) (replacement_level M k 2)
      (code_numeral M 1) (replacement_level M k 3) eq ->
    quotation_atom M false (replacement_level M k 2) (replacement_level M k 1)
      (code_numeral M 1) (replacement_level M k 3) left ->
    quotation_atom M false (replacement_level M k 3) k
      (code_numeral M 1) (replacement_level M k 4) right ->
    domain_replacement_graph M k thetaA thetaB thetaC eq left right q ->
    numerical_implies M marker q.

Lemma replacement_skeleton_atom_values M sources b c n k t equality i j x y v :
  environment_lookup M b c n (code_numeral M i) x ->
  environment_lookup M b c n (code_numeral M j) y ->
  skeleton_quotation M (SkeletonAtom equality i j) sources b c n k t v ->
  quotation_atom M equality x y t k v.
Proof.
  intros HX HY [u [w [HU [HW HV]]]].
  assert (u=x) by exact (environment_lookup_functional M b c n _ u x HU HX).
  assert (w=y) by exact (environment_lookup_functional M b c n _ w y HW HY).
  now subst u w.
Qed.

Theorem replacement_open_image_data M phi bound a b c axiom eb ec en k q :
  source_bounded M phi bound ->
  schema_renaming M RepA phi a -> schema_renaming M RepB phi b -> schema_renaming M RepC phi c ->
  sf_replacement_constructor M a b c axiom ->
  numerical_quotation M axiom eb ec en k (code_numeral M 1) q ->
  exists thetaA thetaB thetaC eq left right,
    binary_matrix_quotation M phi eb ec en k (replacement_level M k 1)
      (replacement_level M k 3) (code_numeral M 1) thetaA /\
    binary_matrix_quotation M phi eb ec en k (replacement_level M k 2)
      (replacement_level M k 3) (code_numeral M 1) thetaB /\
    binary_matrix_quotation M phi eb ec en (replacement_level M k 3) (replacement_level M k 2)
      (replacement_level M k 4) (code_numeral M 1) thetaC /\
    quotation_atom M true (replacement_level M k 1) (replacement_level M k 2)
      (code_numeral M 1) (replacement_level M k 3) eq /\
    quotation_atom M false (replacement_level M k 2) (replacement_level M k 1)
      (code_numeral M 1) (replacement_level M k 3) left /\
    quotation_atom M false (replacement_level M k 3) k
      (code_numeral M 1) (replacement_level M k 4) right /\
    domain_replacement_graph M k thetaA thetaB thetaC eq left right q.
Proof.
  intros HBound HA HB HC HConstruct HQ.
  apply (proj2 (replacement_quotation_skeleton M a b c axiom eb ec en k (code_numeral M 1) q HConstruct)) in HQ.
  cbn [replacement_skeleton functionality_skeleton skeleton_iff skeleton_and skeleton_impl skeleton_quotation] in HQ.
  destruct HQ as [allx [allrange [HFunction [HRange HOut]]]].
  destruct HFunction as [fxb [fxc [fxn [ally [HFX [HFunction HAllX]]]]]].
  destruct HFunction as [fyb [fyc [fyn [allz [HFY [HFunction HAllY]]]]]].
  destruct HFunction as [fzb [fzc [fzn [impA [HFZ [HFunction HAllZ]]]]]].
  destruct HFunction as [thetaA [impB [HThetaA [HFunction HImpA]]]].
  destruct HFunction as [thetaB [eq [HThetaB [HEq HImpB]]]].
  destruct HRange as [ab [ac [an [exb [HRA [HRange HAllRange]]]]]].
  destruct HRange as [bb [bc [bn [allout [HRB [HRange HExB]]]]]].
  destruct HRange as [yb [yc [yn [iffcode [HRY [HRange HAllOut]]]]]].
  destruct HRange as [forward [backward [HForward [HBackward HIff]]]].
  destruct HForward as [left [exx [HLeft [HExX HImpF]]]].
  destruct HExX as [xb [xc [xn [rhs [HRX [HRhs HExX]]]]]].
  destruct HRhs as [right [thetaC [HRight [HThetaC HAnd]]]].
  destruct HBackward as [exx' [left' [HExX' [HLeft' HImpBack]]]].
  destruct HExX' as [xb' [xc' [xn' [rhs' [HRX' [HRhs' HExX']]]]]].
  destruct HRhs' as [right' [thetaC' [HRight' [HThetaC' HAnd']]]].
  assert (MAT_A : binary_matrix_quotation M phi eb ec en k (replacement_level M k 1)
      (replacement_level M k 3) (code_numeral M 1) thetaA).
  { exact (functionality_body_is_binary_matrix M RepA phi a bound eb ec en k
      (succM M k) (succM M (succM M k)) fxb fxc fxn fyb fyc fyn fzb fzc fzn
      (succM M (succM M (succM M k))) (code_numeral M 1) thetaA
      (or_introl eq_refl) HBound HA HFX HFY HFZ HThetaA). }
  assert (MAT_B : binary_matrix_quotation M phi eb ec en k (replacement_level M k 2)
      (replacement_level M k 3) (code_numeral M 1) thetaB).
  { exact (functionality_body_is_binary_matrix M RepB phi b bound eb ec en k
      (succM M k) (succM M (succM M k)) fxb fxc fxn fyb fyc fyn fzb fzc fzn
      (succM M (succM M (succM M k))) (code_numeral M 1) thetaB
      (or_intror eq_refl) HBound HB HFX HFY HFZ HThetaB). }
  assert (MAT_C : binary_matrix_quotation M phi eb ec en (replacement_level M k 3) (replacement_level M k 2)
      (replacement_level M k 4) (code_numeral M 1) thetaC).
  { exact (range_body_is_binary_matrix M phi c bound eb ec en k (succM M k)
      (succM M (succM M (succM M k))) (succM M (succM M k))
      ab ac an bb bc bn yb yc yn xb xc xn
      (succM M (succM M (succM M (succM M k)))) (code_numeral M 1) thetaC
      HBound HC HRA HRB HRY HRX HThetaC). }
  assert (MAT_C' : binary_matrix_quotation M phi eb ec en (replacement_level M k 3) (replacement_level M k 2)
      (replacement_level M k 4) (code_numeral M 1) thetaC').
  { exact (range_body_is_binary_matrix M phi c bound eb ec en k (succM M k)
      (succM M (succM M (succM M k))) (succM M (succM M k))
      ab ac an bb bc bn yb yc yn xb' xc' xn'
      (succM M (succM M (succM M (succM M k)))) (code_numeral M 1) thetaC'
      HBound HC HRA HRB HRY HRX' HThetaC'). }
  assert (thetaC'=thetaC) by exact (binary_matrix_quotation_functional M phi eb ec en
    (replacement_level M k 3) (replacement_level M k 2) (replacement_level M k 4)
    (code_numeral M 1) thetaC' thetaC MAT_C' MAT_C).
  subst thetaC'.
  assert (FLZ : environment_lookup M fzb fzc fzn (code_numeral M 0) (replacement_level M k 2)).
  { apply (proj2 (environment_cons_head M fyb fyc fyn (succM M (succM M k)) fzb fzc fzn _ HFZ));reflexivity. }
  assert (FLY : environment_lookup M fzb fzc fzn (code_numeral M 1) (replacement_level M k 1)).
  { apply (proj2 (environment_cons_tail M fyb fyc fyn (succM M (succM M k)) fzb fzc fzn (zeroM M) _ HFZ)).
    apply (proj2 (environment_cons_head M fxb fxc fxn (succM M k) fyb fyc fyn _ HFY));reflexivity. }
  apply (replacement_skeleton_atom_values M (schema_env3 a b c) fzb fzc fzn
    (replacement_level M k 3) (code_numeral M 1) true 1 0 _ _ eq FLY FLZ) in HEq.
  assert (LY : environment_lookup M yb yc yn (code_numeral M 0) (replacement_level M k 2)).
  { apply (proj2 (environment_cons_head M bb bc bn (succM M (succM M k)) yb yc yn _ HRY));reflexivity. }
  assert (LB : environment_lookup M yb yc yn (code_numeral M 1) (replacement_level M k 1)).
  { apply (proj2 (environment_cons_tail M bb bc bn (succM M (succM M k)) yb yc yn (zeroM M) _ HRY)).
    apply (proj2 (environment_cons_head M ab ac an (succM M k) bb bc bn _ HRB));reflexivity. }
  apply (replacement_skeleton_atom_values M (schema_env3 a b c) yb yc yn
    (replacement_level M k 3) (code_numeral M 1) false 0 1 _ _ left LY LB) in HLeft.
  apply (replacement_skeleton_atom_values M (schema_env3 a b c) yb yc yn
    (replacement_level M k 3) (code_numeral M 1) false 0 1 _ _ left' LY LB) in HLeft'.
  assert (RX : environment_lookup M xb xc xn (code_numeral M 0) (replacement_level M k 3)).
  { apply (proj2 (environment_cons_head M yb yc yn (succM M (succM M (succM M k))) xb xc xn _ HRX));reflexivity. }
  assert (RA : environment_lookup M xb xc xn (code_numeral M 3) k).
  { apply (proj2 (environment_cons_tail M yb yc yn (succM M (succM M (succM M k))) xb xc xn (code_numeral M 2) _ HRX)).
    apply (proj2 (environment_cons_tail M bb bc bn (succM M (succM M k)) yb yc yn (code_numeral M 1) _ HRY)).
    apply (proj2 (environment_cons_tail M ab ac an (succM M k) bb bc bn (zeroM M) _ HRB)).
    apply (proj2 (environment_cons_head M eb ec en k ab ac an _ HRA));reflexivity. }
  assert (RX' : environment_lookup M xb' xc' xn' (code_numeral M 0) (replacement_level M k 3)).
  { apply (proj2 (environment_cons_head M yb yc yn (succM M (succM M (succM M k))) xb' xc' xn' _ HRX'));reflexivity. }
  assert (RA' : environment_lookup M xb' xc' xn' (code_numeral M 3) k).
  { apply (proj2 (environment_cons_tail M yb yc yn (succM M (succM M (succM M k))) xb' xc' xn' (code_numeral M 2) _ HRX')).
    apply (proj2 (environment_cons_tail M bb bc bn (succM M (succM M k)) yb yc yn (code_numeral M 1) _ HRY)).
    apply (proj2 (environment_cons_tail M ab ac an (succM M k) bb bc bn (zeroM M) _ HRB)).
    apply (proj2 (environment_cons_head M eb ec en k ab ac an _ HRA));reflexivity. }
  apply (replacement_skeleton_atom_values M (schema_env3 a b c) xb xc xn
    (replacement_level M k 4) (code_numeral M 1) false 0 3 _ _ right RX RA) in HRight.
  apply (replacement_skeleton_atom_values M (schema_env3 a b c) xb' xc' xn'
    (replacement_level M k 4) (code_numeral M 1) false 0 3 _ _ right' RX' RA') in HRight'.
  assert (left'=left) by exact (quotation_atom_functional M false _ _ _ _ _ _ HLeft' HLeft).
  assert (right'=right) by exact (quotation_atom_functional M false _ _ _ _ _ _ HRight' HRight).
  subst left' right'.
  assert (rhs'=rhs) by exact (quotation_binary_functional M SFAnd right thetaC rhs' rhs HAnd' HAnd).
  subst rhs'.
  assert (exx'=exx) by exact (quotation_quantifier_functional M false
    (replacement_level M k 3) (code_numeral M 1) rhs exx' exx HExX' HExX).
  subst exx'.
  exists thetaA,thetaB,thetaC,eq,left,right.
  split;[exact MAT_A|]. split;[exact MAT_B|]. split;[exact MAT_C|].
  split;[exact HEq|]. split;[exact HLeft|]. split;[exact HRight|].
  exists impB,impA,allz,ally,allx,rhs,exx,forward,backward,iffcode,allout,exb,allrange.
  repeat split;assumption.
Qed.

Theorem open_replacement_images_from_quoted_domain_replacement M marker :
  quoted_domain_replacement_certificates M marker -> open_replacement_images M marker.
Proof.
  intros HRep phi count a b c axiom HBound HA HB HC HConstruct eb ec en k q HSafe HQ.
  destruct (replacement_open_image_data M phi (succM M (succM M count)) a b c axiom
    eb ec en k q HBound HA HB HC HConstruct HQ) as
    [thetaA [thetaB [thetaC [eq [left [right [HMA [HMB [HMC [HE [HL [HR HG]]]]]]]]]]]].
  exact (HRep phi (succM M (succM M count)) eb ec en k thetaA thetaB thetaC eq left right q
    HBound HSafe HMA HMB HMC HE HL HR HG).
Qed.

Print Assumptions replacement_open_image_data.
Print Assumptions open_replacement_images_from_quoted_domain_replacement.
