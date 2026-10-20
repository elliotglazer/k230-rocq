(** A finite named-code interface for the remaining source-defined
    quotient-Replacement certificate. *)
From PAModel Require Import Model FiniteCoding CodeExpressions NumericalProofs ProofTemplates
  NumericalEquivalence QuotientAtomTemplates QuotationPayloads QuotationFixedSource
  QuotationHygiene SourceBounded ReplacementMatrixQuotation DomainReplacementImage
  SchemaImageReduction SetFormulaCodes.
From FOL Require Import FullSyntax Arithmetics.
Unset Implicit Arguments.

Definition E_replacement_all x body := E_wal x (E_wim (E_wel (CEconst 1) x) body).
Definition E_replacement_ex x body := E_wex x (E_wa (E_wel (CEconst 1) x) body).
Definition E_replacement_level k n := Nat.iter n (fun x=>CEadd x (CEconst 1)) k.
Definition E_domain_replacement k thetaA thetaB thetaC eq left right :=
  let k1:=E_replacement_level k 1 in
  let k2:=E_replacement_level k 2 in
  let k3:=E_replacement_level k 3 in
  let funbody:=E_wim thetaA (E_wim thetaB eq) in
  let function:=E_replacement_all k (E_replacement_all k1 (E_replacement_all k2 funbody)) in
  let exx:=E_replacement_ex k3 (E_wa right thetaC) in
  let rangebody:=E_wa (E_wim left exx) (E_wim exx left) in
  let range:=E_replacement_all k (E_replacement_ex k1 (E_replacement_all k2 rangebody)) in
  E_wim function range.
Definition domain_replacement_parameters M k thetaA thetaB thetaC eq left right :=
  k .: thetaA .: thetaB .: thetaC .: eq .: left .: right .: fun _=>zeroM M.

Lemma replacement_level_graph M rho K k n :
  code_relation M rho K k ->
  code_relation M rho (E_replacement_level K n) (replacement_level M k n).
Proof.
  revert K k. induction n as [|n IH];intros K k HK;[exact HK|].
  change (code_relation M rho (CEadd (E_replacement_level K n) (CEconst 1))
    (succM M (replacement_level M k n))).
  exact (code_graph_fresh_successor M rho (E_replacement_level K n)
    (replacement_level M k n) (IH K k HK)).
Qed.

Lemma replacement_all_graph M rho X F x f q :
  code_relation M rho X x -> code_relation M rho F f ->
  (code_relation M rho (E_replacement_all X F) q <->
   quotation_quantifier M true x (code_numeral M 1) f q).
Proof.
  intros HX HF. exact (quotation_quantifier_substitution_graph M rho true X (CEconst 1) F
    x (code_numeral M 1) f q HX eq_refl HF).
Qed.
Lemma replacement_ex_graph M rho X F x f q :
  code_relation M rho X x -> code_relation M rho F f ->
  (code_relation M rho (E_replacement_ex X F) q <->
   quotation_quantifier M false x (code_numeral M 1) f q).
Proof.
  intros HX HF. exact (quotation_quantifier_substitution_graph M rho false X (CEconst 1) F
    x (code_numeral M 1) f q HX eq_refl HF).
Qed.

Theorem domain_replacement_graph_code M k thetaA thetaB thetaC eq left right q :
  domain_replacement_graph M k thetaA thetaB thetaC eq left right q ->
  code_relation M (domain_replacement_parameters M k thetaA thetaB thetaC eq left right)
    (E_domain_replacement (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
      (CEvar 4) (CEvar 5) (CEvar 6)) q.
Proof.
  intros (impB & impA & allz & ally & allx & rhs & exx & forward & backward & iffcode & allout & exb & allrange &
    HIB & HIA & HZ & HY & HX & HRHS & HEX & HF & HB & HI & HOUT & HEB & HRANGE & HROOT).
  set (rho:=domain_replacement_parameters M k thetaA thetaB thetaC eq left right).
  set (K1:=E_replacement_level (CEvar 0) 1).
  set (K2:=E_replacement_level (CEvar 0) 2).
  set (K3:=E_replacement_level (CEvar 0) 3).
  assert (G1 : code_relation M rho K1 (replacement_level M k 1)) by (apply replacement_level_graph;reflexivity).
  assert (G2 : code_relation M rho K2 (replacement_level M k 2)) by (apply replacement_level_graph;reflexivity).
  assert (G3 : code_relation M rho K3 (replacement_level M k 3)) by (apply replacement_level_graph;reflexivity).
  set (IB:=E_wim (CEvar 2) (CEvar 4)).
  set (IA:=E_wim (CEvar 1) IB).
  assert (GIB : code_relation M rho IB impB).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFImpl (CEvar 2) (CEvar 4)
      thetaB eq impB eq_refl eq_refl) HIB). }
  assert (GIA : code_relation M rho IA impA).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFImpl (CEvar 1) IB
      thetaA impB impA eq_refl GIB) HIA). }
  set (AZ:=E_replacement_all K2 IA).
  set (AY:=E_replacement_all K1 AZ).
  set (AX:=E_replacement_all (CEvar 0) AY).
  assert (GAZ : code_relation M rho AZ allz) by exact (proj2 (replacement_all_graph M rho K2 IA _ _ _ G2 GIA) HZ).
  assert (GAY : code_relation M rho AY ally) by exact (proj2 (replacement_all_graph M rho K1 AZ _ _ _ G1 GAZ) HY).
  assert (GAX : code_relation M rho AX allx) by exact (proj2 (replacement_all_graph M rho (CEvar 0) AY _ _ _ eq_refl GAY) HX).
  set (RHS:=E_wa (CEvar 6) (CEvar 3)).
  set (EX:=E_replacement_ex K3 RHS).
  assert (GRHS : code_relation M rho RHS rhs).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFAnd (CEvar 6) (CEvar 3)
      right thetaC rhs eq_refl eq_refl) HRHS). }
  assert (GEX : code_relation M rho EX exx) by exact (proj2 (replacement_ex_graph M rho K3 RHS _ _ _ G3 GRHS) HEX).
  set (F:=E_wim (CEvar 5) EX).
  set (B:=E_wim EX (CEvar 5)).
  set (I:=E_wa F B).
  assert (GF : code_relation M rho F forward).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFImpl (CEvar 5) EX
      left exx forward eq_refl GEX) HF). }
  assert (GB : code_relation M rho B backward).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFImpl EX (CEvar 5)
      exx left backward GEX eq_refl) HB). }
  assert (GI : code_relation M rho I iffcode).
  { exact (proj2 (quotation_binary_substitution_graph M rho SFAnd F B
      forward backward iffcode GF GB) HI). }
  set (AO:=E_replacement_all K2 I).
  set (EB:=E_replacement_ex K1 AO).
  set (AR:=E_replacement_all (CEvar 0) EB).
  assert (GAO : code_relation M rho AO allout) by exact (proj2 (replacement_all_graph M rho K2 I _ _ _ G2 GI) HOUT).
  assert (GEB : code_relation M rho EB exb) by exact (proj2 (replacement_ex_graph M rho K1 AO _ _ _ G1 GAO) HEB).
  assert (GAR : code_relation M rho AR allrange) by exact (proj2 (replacement_all_graph M rho (CEvar 0) EB _ _ _ eq_refl GEB) HRANGE).
  exact (proj2 (quotation_binary_substitution_graph M rho SFImpl AX AR allx allrange q GAX GAR) HROOT).
Qed.

Print Assumptions replacement_level_graph.
Print Assumptions domain_replacement_graph_code.

Definition quoted_domain_replacement_template_certificates M marker :=
  forall phi bound eb ec en k thetaA thetaB thetaC eq left right,
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
    forall q, code_relation M (domain_replacement_parameters M k thetaA thetaB thetaC eq left right)
      (E_domain_replacement (CEvar 0) (CEvar 1) (CEvar 2) (CEvar 3)
        (CEvar 4) (CEvar 5) (CEvar 6)) q -> numerical_implies M marker q.

Theorem quoted_domain_replacement_from_template M marker :
  quoted_domain_replacement_template_certificates M marker ->
  quoted_domain_replacement_certificates M marker.
Proof.
  intros H phi bound eb ec en k thetaA thetaB thetaC eq left right q
    HBound HSafe HA HB HC HE HL HR HG.
  exact (H phi bound eb ec en k thetaA thetaB thetaC eq left right
    HBound HSafe HA HB HC HE HL HR q
    (domain_replacement_graph_code M k thetaA thetaB thetaC eq left right q HG)).
Qed.

Theorem open_replacement_images_from_quoted_template M marker :
  quoted_domain_replacement_template_certificates M marker -> open_replacement_images M marker.
Proof.
  intro H. apply open_replacement_images_from_quoted_domain_replacement.
  exact (quoted_domain_replacement_from_template M marker H).
Qed.

Print Assumptions quoted_domain_replacement_from_template.
Print Assumptions open_replacement_images_from_quoted_template.
