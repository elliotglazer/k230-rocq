(** * Z_refl: the reflection principle for the hierarchy L_α.

    For every formula φ with free variables among $0..$(m-1):
      ∀α ∃β > α  ∀ x⃗ ∈ L_β  (φ^L(x⃗) ↔ φ^{L_β}(x⃗)).
    The derivation is built by recursion on φ (instances [refl_insts m φ]).

    Proof (Tarski-Vaught style).  [pcs m φ] lists the "pieces" of φ: for every quantified
    subformula ∃ψ / ∀ψ under K context variables, the formulas ψ^L and ¬ψ^L (with $0 = the
    witness, $1..$K = the context).  [Ew b Z]: "if a witness of b exists in L, one exists in Z".
    - [TV]: if Y is a set of elements of L and every piece is witness-closed in Y for all
      contexts from Y, then Y reflects φ (induction on φ).
    - [Pc K b d X] = "∀ x⃗ ∈ X (K of them): ∀Z (Z = L_d → Ew b(x⃗) Z)", in the shape [Dn K]
      that matches the ordinal collection schema; [cb_gen] finds such a d for X = L_γ by
      K-fold [ord_collect] (base case: [L_above]); [pcf_bound] combines the pieces ([ord_max]).
    - F(γ) := the least d > γ with all pieces [Pc] for X = L_γ ([least_ord]); a set Y ∋ α
      closed under F (Std_setrec.closure_thm on ω); K := ordinals of Y; β := ⋃K.  Then β is a
      limit, every finite tuple from L_β lies in some L_κ (κ ∈ K, [common_level]), and its
      witnesses lie in L_{F(κ)} ⊆ L_β ([PH_from]).  [TV] gives [Refl m φ β]. *)
From Coq Require Import Arith Lia List.
From OldUndecidability.FOL Require Import Syntax.Facts Sets.minZF Deduction.FullNDFacts.
From OldZF Require Import Std_tr Std_gen Std_iface Std_setnd Std_setbase Std_setinf.
From OldZF Require Std_setrec.
From OldRegCon Require Import Rel.
From OldZFC Require Import Z_rel Z_base Z_prim Z_ord Z_trec Z_cl Z_L.
Import ListNotations.
#[local] Existing Instance sig_empty | 0.
#[local] Existing Instance ZF_pred_sig | 0.
Unset Implicit Arguments.

(** m nested quantifiers bounded by Y (the outermost binds the body's $(m-1)) *)
Fixpoint ballS (m : nat) (Y : term) (body : form) : form :=
  match m with
  | 0 => body
  | S m' => ∀ ($0 ∈' Y`[↑] → ballS m' Y`[↑] body)
  end.

(** β reflects φ: ∀Y (Y = L_β → ∀ x⃗ ∈ Y (φ^L ↔ φ^Y)); inside, Y is $m *)
Definition Refl (m : nat) (phi : form) (b : term) : form :=
  ∀ (LL b`[↑] $0 → ballS m $0 (rel Lform phi ↔ relS $m phi)).

(** ** Substitution utilities *)
#[local] Arguments Lform : simpl never.

Lemma Lform_up sg : Lform[up sg] = Lform.
Proof. exact (M_up' Lform bounded_Lform sg). Qed.
Lemma relL_subst {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) sg :
  (rel Lform phi)[sg] = rel Lform (phi[sg]).
Proof. exact (rel_subst bounded_Lform phi sg). Qed.
#[local] Hint Rewrite Lform_up relL_subst @relS_subst : fsub.

Definition upn (N : nat) (sg : nat -> term) : nat -> term :=
  fun k => if k <? N then var k else (sg (k - N))`[fun j => var (N + j)].
Definition ext (N : nat) (sg : nat -> term) : nat -> term :=
  fun k => if k <? N then sg k else var (k - N).

Lemma upn_S N sg k : upn N (up sg) k = upn (S N) sg k.
Proof.
  unfold upn. destruct (Nat.ltb_spec k N), (Nat.ltb_spec k (S N)); try lia; try reflexivity.
  - assert (k = N) by lia. subst k. rewrite Nat.sub_diag. cbn. f_equal. lia.
  - replace (k - N) with (S (k - S N)) by lia. cbn. unfold funcomp. rewrite subst_term_comp.
    apply subst_term_ext. intros j. cbn. f_equal. lia.
Qed.

Lemma ballS_subst N : forall Y body sg, (ballS N Y body)[sg] = ballS N Y`[sg] (body[upn N sg]).
Proof.
  induction N as [|N IH]; intros Y body sg; cbn.
  - symmetry. apply subst_ext. intros k. unfold upn. cbn. rewrite Nat.sub_0_r. apply subst_term_var.
  - rewrite IH, up_term, (subst_ext body (upn_S N sg)). reflexivity.
Qed.

Lemma ext_lt N sg k : k < N -> ext N sg k = sg k.
Proof. intros H. unfold ext. destruct (Nat.ltb_spec k N); [reflexivity|lia]. Qed.
Lemma ext_ge N sg k : N <= k -> ext N sg k = var (k - N).
Proof. intros H. unfold ext. destruct (Nat.ltb_spec k N); [lia|reflexivity]. Qed.

Lemma upn_ext N t sg sg' : sg' N = t -> (forall k, k < N -> sg' k = sg k) ->
  forall k, (upn N (t..) k)`[ext N sg] = ext (S N) sg' k.
Proof.
  intros H1 H2 k. unfold upn.
  destruct (Nat.ltb_spec k N).
  - cbn [subst_term]. rewrite !ext_lt by lia. symmetry. now apply H2.
  - destruct (Nat.eq_dec k N) as [->|Hne].
    + rewrite Nat.sub_diag, ext_lt by lia. cbn. rewrite subst_term_comp.
      rewrite H1. apply subst_term_id. intros j. cbn. rewrite ext_ge by lia. f_equal. lia.
    + replace (k - N) with (S (k - S N)) by lia. cbn. rewrite !ext_ge by lia. f_equal. lia.
Qed.

Lemma ballS_elim G N : forall Y body sg, G ⊢C ballS N Y body ->
  (forall k, k < N -> G ⊢C sg k ∈' Y) -> G ⊢C body[ext N sg].
Proof.
  induction N as [|N IH]; intros Y body sg H Hs.
  - cbn in H. rewrite subst_id; [exact H|]. intros k. unfold ext. cbn. f_equal. lia.
  - cbn in H. apply (AllE (sg N)) in H. cbn in H. rewrite ballS_subst, subst_term_shift in H.
    pose proof (IE H (Hs N ltac:(lia))) as H'. apply (IH _ _ sg) in H'; [|intros k Hk; apply Hs; lia].
    rewrite subst_comp in H'. erewrite subst_ext; [exact H'|]. intros k. cbn.
    symmetry. apply upn_ext; reflexivity.
Qed.

Lemma ballS_intro N : forall G Y body,
  (forall G' sg, incl G G' -> (forall k, k < N -> G' ⊢C sg k ∈' Y) -> G' ⊢C body[ext N sg]) ->
  G ⊢C ballS N Y body.
Proof.
  induction N as [|N IH]; intros G Y body H.
  - cbn. specialize (H G var (fun a Ha => Ha) (fun k Hk => ltac:(lia))).
    rewrite subst_id in H; [exact H|]. intros k. unfold ext. cbn. f_equal. lia.
  - cbn. apply AllI_named. intros t. cbn. rewrite ballS_subst, subst_term_shift. apply II.
    apply IH. intros G' sg HG' Hs.
    rewrite subst_comp. erewrite subst_ext.
    + apply (H G' (fun k => if k =? N then t else sg k)).
      * intros a Ha. apply HG'. now right.
      * intros k Hk. destruct (Nat.eqb_spec k N).
        -- apply Ctx, HG'. now left.
        -- apply Hs. lia.
    + intros k. cbn. apply upn_ext.
      * now rewrite Nat.eqb_refl.
      * intros j Hj. destruct (Nat.eqb_spec j N); [lia|reflexivity].
Qed.

(** the body of [Refl] after instantiating Y and the m bounded variables *)
Lemma refl_body m phi Y tau sg : fb m phi ->
  (rel Lform phi ↔ relS $m phi)[upn m (Y .: tau)][ext m sg] = (rel Lform (phi[sg]) ↔ relS Y (phi[sg])).
Proof.
  intros Hfb. rewrite subst_comp. cbn. rewrite relL_subst, relS_subst.
  assert (E : phi[upn m (Y .: tau) >> subst_term (ext m sg)] = phi[sg]).
  { apply (subst_ext_fb _ m); [exact Hfb|]. intros k Hk. unfold funcomp, upn.
    destruct (Nat.ltb_spec k m); [|lia]. cbn [subst_term]. now rewrite ext_lt. }
  assert (E2 : $m`[upn m (Y .: tau) >> subst_term (ext m sg)] = Y).
  { cbn [subst_term]. unfold funcomp, upn. destruct (Nat.ltb_spec m m); [lia|].
    rewrite Nat.sub_diag. cbn. rewrite subst_term_comp. apply subst_term_id. intros j. cbn.
    rewrite ext_ge by lia. f_equal. lia. }
  rewrite E, E2. reflexivity.
Qed.

(** ** Pieces: the quantified subformulas, with their number of context variables *)
Lemma fb_rel {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : forall N,
  fb N phi -> fb N (rel Lform phi).
Proof.
  induction phi as [|ff P v|ff op a IHa c IHc|ff q a IHa]; intros N H; cbn in *.
  - exact I.
  - destruct P; exact H.
  - split; [apply IHa|apply IHc]; tauto.
  - destruct q; cbn; (split; [eapply fb_mono; [exact fb_Lform|lia] | apply IHa; exact H]).
Qed.

(** a piece (K, b): b has $0 = the witness and $1..$K = the context *)
Fixpoint pcs {ff} (N : nat) (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : list (nat * form) :=
  match phi with
  | bin _ a c => pcs N a ++ pcs N c
  | quant _ a => (N, rel Lform a) :: (N, ¬ rel Lform a) :: pcs (S N) a
  | _ => []
  end.

Lemma pcs_fb {ff} (phi : @Core.form sig_empty ZF_pred_sig full_operators ff) : forall N, fb N phi ->
  forall K b, In (K, b) (pcs N phi) -> fb (S K) b.
Proof.
  induction phi as [|ff P v|ff op a IHa c IHc|ff q a IHa]; intros N H K b Hin; cbn in *.
  - destruct Hin.
  - destruct Hin.
  - apply in_app_iff in Hin as [Hin|Hin]; [eapply IHa|eapply IHc]; eauto; tauto.
  - destruct Hin as [E|[E|Hin]].
    + inversion E; subst. now apply fb_rel.
    + inversion E; subst. cbn. split; [now apply fb_rel|exact I].
    + eapply IHa; eauto.
Qed.

(** witness closure of a piece in Z *)
Definition Ew (b : form) (Z : term) : form := (∃ (Lform ∧ b)) → ∃ ($0 ∈' Z`[↑] ∧ b).
#[local] Arguments Ew : simpl never.
Lemma Ew_subst b Z sg : (Ew b Z)[sg] = Ew (b[up sg]) Z`[sg].
Proof. unfold Ew. cbn. rewrite Lform_up, up_term. reflexivity. Qed.
#[local] Hint Rewrite Ew_subst : fsub.

(** layout of [D0f b] and [Dn K D]: $0 = δ, $1 = X, $(2+k) = parameter k *)
Definition D0f (b : form) : form := ∀ (LL $1 $0 → Ew (b[up (fun k => $(3 + k))]) $0).
Fixpoint Dn (K : nat) (D : form) : form :=
  match K with
  | 0 => D
  | S K' => ∀ ($0 ∈' $2 → (Dn K' D)[$1 .: $2 .: $0 .: (fun k => $(3 + k))])
  end.
(** "for all x⃗ ∈ X (K of them): witnesses of the piece b found in L lie in L_d" *)
Definition Pc (K : nat) (b : form) (d X : term) : form := (Dn K (D0f b))[d .: X .: (fun _ => X)].
#[local] Arguments Pc : simpl never.
Lemma Pc_subst K b d X sg : (Pc K b d X)[sg] = Pc K b d`[sg] X`[sg].
Proof. unfold Pc. rewrite subst_comp. apply subst_ext. intros [|[|k]]; reflexivity. Qed.
#[local] Hint Rewrite Pc_subst : fsub.

Fixpoint PCf (ps : list (nat * form)) (d X : term) : form :=
  match ps with
  | [] => ⊥ → ⊥
  | (K, b) :: ps' => Pc K b d X ∧ PCf ps' d X
  end.
#[local] Arguments PCf : simpl never.
Lemma PCf_subst ps d X sg : (PCf ps d X)[sg] = PCf ps d`[sg] X`[sg].
Proof.
  induction ps as [|[K b] ps IH]; [reflexivity|].
  change ((Pc K b d X ∧ PCf ps d X)[sg] = Pc K b d`[sg] X`[sg] ∧ PCf ps d`[sg] X`[sg]).
  cbn. rewrite Pc_subst, IH. reflexivity.
Qed.
#[local] Hint Rewrite PCf_subst : fsub.

(** the condition on the next level d after the ordinal x *)
Definition Cond (ps : list (nat * form)) (x d : term) : form :=
  Ord0 x → x ∈' d ∧ ∀ (LL x`[↑] $0 → PCf ps d`[↑] $0).
#[local] Arguments Cond : simpl never.
Lemma Cond_subst ps x d sg : (Cond ps x d)[sg] = Cond ps x`[sg] d`[sg].
Proof. unfold Cond. cbn. autorewrite with fsub. cbn. reflexivity. Qed.
#[local] Hint Rewrite Cond_subst : fsub.
(** y is the least ordinal with [Cond x y] *)
Definition LeastF (ps : list (nat * form)) (x y : term) : form :=
  Ord0 y ∧ Cond ps x y ∧ ∀ ($0 ∈' y`[↑] → ¬ Cond ps x`[↑] $0).
#[local] Arguments LeastF : simpl never.
Lemma LeastF_subst ps x y sg : (LeastF ps x y)[sg] = LeastF ps x`[sg] y`[sg].
Proof. unfold LeastF. cbn. autorewrite with fsub. cbn. reflexivity. Qed.
#[local] Hint Rewrite LeastF_subst : fsub.

Definition psiF ps : form := Cond ps $1 $0.
Definition phG ps : form := LeastF ps $0 $1.
Definition Qf (K : nat) (b : form) : form := (Dn K (D0f b))[$0 .: $2 .: $1 .: (fun k => $(3 + k))].
Fixpoint cinsts (K n : nat) (b : form) : list form :=
  match K with
  | 0 => []
  | S K' => oc_insts (S n) (Qf K' b) ++ cinsts K' (S n) b
  end.
Definition sepOrd : form := forall_times 0 (ax_sep' (Ord0 $0)).
Definition sepTnf : form := forall_times 0 (ax_sep' tnf_form).

(** ** Free-variable bounds *)
Lemma fb_inst (phi : form) N sg : (forall i, idx (sg i) < N) -> fb N phi[sg].
Proof. intros H. destruct (fb_exists phi) as [M HM]. eapply fb_subst; [exact HM|]. intros i _. apply H. Qed.
Lemma fb_LL a Y N : idx a < N -> idx Y < N -> fb N (LL a Y).
Proof.
  intros Ha HY. replace (LL a Y) with ((LL $0 $1)[a .: Y .: var]) by (rewrite LL_subst; reflexivity).
  apply (fb_subst _ 2); [fbcomp|]. intros [|[|i]] Hi; cbn; [exact Ha|exact HY|lia].
Qed.
Lemma fb_Ord0 x N : idx x < N -> fb N (Ord0 x).
Proof.
  intros Hx. replace (Ord0 x) with ((Ord0 $0)[x..]) by (rewrite Ord0_subst; reflexivity).
  apply (fb_subst _ 1); [fbcomp|]. intros [|i] Hi; cbn; [exact Hx|lia].
Qed.
Lemma idx_up (x : term) : idx x`[↑] = S (idx x).
Proof. destruct x as [n|[]]. reflexivity. Qed.
Lemma fb_PCf ps d X N : idx d < N -> idx X < N -> fb N (PCf ps d X).
Proof.
  intros Hd HX. induction ps as [|[K b] ps IH]; [change (fb N (⊥ → ⊥)); cbn; tauto|].
  change (fb N (Pc K b d X ∧ PCf ps d X)). split; [|exact IH].
  unfold Pc. apply fb_inst. intros [|[|i]]; cbn; assumption.
Qed.
Lemma fb_Cond ps x d N : idx x < N -> idx d < N -> fb N (Cond ps x d).
Proof.
  intros Hx Hd. unfold Cond. cbn. split; [now apply fb_Ord0|]. split; [split; assumption|].
  split; [apply fb_LL; cbn; rewrite ?idx_up; lia|]. apply fb_PCf; cbn; rewrite ?idx_up; lia.
Qed.
Lemma fb_LeastF ps x y N : idx x < N -> idx y < N -> fb N (LeastF ps x y).
Proof.
  intros Hx Hy. unfold LeastF. cbn. split; [split; [now apply fb_Ord0|now apply fb_Cond]|].
  split; [split; cbn; rewrite ?idx_up; lia|]. split; [apply fb_Cond; cbn; rewrite ?idx_up; lia|exact I].
Qed.
Lemma fb_Ew b Z N : fb (S N) b -> idx Z < N -> fb N (Ew b Z).
Proof.
  intros Hb HZ. unfold Ew. cbn. split; split; try exact Hb.
  - eapply fb_mono; [exact fb_Lform|lia].
  - split; [lia|]. rewrite idx_up. lia.
Qed.
Lemma fb_D0f b N : fb (S N) b -> fb (2 + N) (D0f b).
Proof.
  intros Hb. unfold D0f. cbn. split; [apply fb_LL; cbn; lia|]. apply fb_Ew; [|cbn; lia].
  eapply fb_subst; [exact Hb|]. intros [|i] Hi; cbn; lia.
Qed.
Lemma fb_Dn K : forall n D, fb (2 + (K + n)) D -> fb (2 + n) (Dn K D).
Proof.
  induction K as [|K IH]; intros n D H; [exact H|]. cbn. split; [cbn; lia|].
  eapply fb_subst; [apply (IH (S n)); replace (2 + (K + S n)) with (2 + (S K + n)) by lia; exact H|].
  intros [|[|[|i]]] Hi; cbn; lia.
Qed.
Lemma fb_Qf K n b : fb (S (S K) + n) b -> fb (S (S (S n))) (Qf K b).
Proof.
  intros Hb. unfold Qf. eapply fb_subst.
  - apply (fb_Dn K (S n)). apply fb_D0f. replace (S (K + S n)) with (S (S K) + n) by lia. exact Hb.
  - intros [|[|[|i]]] Hi; cbn; lia.
Qed.

Lemma cinsts_ok K : forall n b a, fb (S K + n) b -> In a (cinsts K n b) -> ZFR a.
Proof.
  induction K as [|K IH]; intros n b a Hb Ha; [destruct Ha|].
  change (In a (oc_insts (S n) (Qf K b) ++ cinsts K (S n) b)) in Ha.
  apply in_app_iff in Ha as [Ha|Ha].
  - eapply oc_insts_ok; [|exact Ha]. now apply fb_Qf.
  - eapply IH; [|exact Ha]. replace (S K + S n) with (S (S K) + n) by lia. exact Hb.
Qed.

#[local] Arguments D0f : simpl never.
#[local] Arguments Qf : simpl never.

(** instances used for φ: ordinal collection for every piece and bounded variable, the
    least-element instance for F, separation for the ordinals of a set and for ω's natural
    numbers (TNF), and the closure theorem's instances for F *)
Definition refl_insts (m : nat) (phi : form) : list form :=
  flat_map (fun p => cinsts (fst p) 0 (snd p)) (pcs m phi) ++
  [least_inst 1 (psiF (pcs m phi)); sepOrd; sepTnf] ++ Std_setrec.rec_insts phSig (phG (pcs m phi)).
Lemma refl_insts_ok m phi a : fb m phi -> In a (refl_insts m phi) -> ZFR a.
Proof.
  intros Hfb Ha. unfold refl_insts in Ha. apply in_app_iff in Ha as [Ha|Ha].
  - apply in_flat_map in Ha as [[K b] [Hp Ha]]. cbn in Ha. eapply cinsts_ok; [|exact Ha].
    rewrite Nat.add_0_r. exact (pcs_fb phi m Hfb K b Hp).
  - destruct Ha as [<-|[<-|[<-|Ha]]].
    + apply ZFR_sep. unfold psiF. apply fb_Cond; cbn; lia.
    + apply ZFR_sep. fbcomp.
    + apply ZFR_sep. exact fb_tnf.
    + left. left. eapply rec_insts_ZF0. exact Ha.
Qed.

(** ** Tactics *)
(** the fact tactics also weaken hypotheses [forall k, k < n -> G ⊢C _] *)
#[local] Ltac weaken_facts a G ::=
  repeat match goal with
  | H : G ⊢C _ |- _ => apply (weak_cons G a) in H
  | H : forall k : nat, @prv _ _ _ class G (@?P k) |- _ =>
      let H' := fresh in pose proof (fun k => weak_cons G a _ (H k)) as H'; clear H; rename H' into H
  | H : forall k : nat, k < ?n -> @prv _ _ _ class G (@?P k) |- _ =>
      let H' := fresh in pose proof (fun k (Hk : k < n) => weak_cons G a _ (H k Hk)) as H'; clear H;
      rename H' into H
  | H : incl _ G |- _ => apply (incl_cons_r _ G a) in H
  | H : In _ G |- _ => apply (in_cons_r _ a G) in H
  end.

Lemma rf_conv G (phi : form) s1 s2 : (forall k, s1 k = s2 k) -> G ⊢C phi[s1] -> G ⊢C phi[s2].
Proof. intros E H. now rewrite <- (subst_ext phi E). Qed.
Lemma rf_conv_fb G (phi : form) N s1 s2 : fb N phi -> (forall k, k < N -> s1 k = s2 k) -> G ⊢C phi[s1] -> G ⊢C phi[s2].
Proof. intros Hfb E H. now rewrite <- (subst_ext_fb phi N s1 s2 Hfb E). Qed.

Local Ltac rzh := first [ assumption | apply Ax_L_cl; assumption | apply Ax_cl_ord, Ax_L_cl; assumption
  | apply Ax_ord_prim, Ax_cl_ord, Ax_L_cl; assumption ].

(** ** Upstream lemmas with a uniform signature *)
Section W.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G).

Lemma rw_emp0_ex : G ⊢C ∃ Emp0 $0.
Proof using HG HR HOm HL. eapply emp0_ex; rzh. Qed.
Lemma rw_union0_ex x : G ⊢C ∃ Union0 x`[↑] $0.
Proof using HG HR HOm HL. eapply union0_ex; rzh. Qed.
Lemma rw_succ0_ex x : G ⊢C ∃ Succ0 x`[↑] $0.
Proof using HG HR HOm HL. eapply succ0_ex; rzh. Qed.
Lemma rw_ord_el a x : G ⊢C Ord0 a -> G ⊢C x ∈' a -> G ⊢C Ord0 x.
Proof using HG HR HOm HL. intros H1 H2. eapply ord_el; [rzh..|exact H1|exact H2]. Qed.
Lemma rw_ord_tri a b : G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C a ∈' b ∨ a ≡' b ∨ b ∈' a.
Proof using HG HR HOm HL. intros H1 H2. eapply ord_tri; [rzh..|exact H1|exact H2]. Qed.
Lemma rw_ord_el_sub a b : G ⊢C Ord0 b -> G ⊢C a ∈' b -> G ⊢C Sub0 a b.
Proof using HG HR HOm HL. intros H1 H2. eapply ord_el_sub; [rzh..|exact H1|exact H2]. Qed.
Lemma rw_ord_emp e : G ⊢C Emp0 e -> G ⊢C Ord0 e.
Proof using HG HR HOm HL. intros H1. eapply ord_emp; [rzh..|exact H1]. Qed.
Lemma rw_ord_succ a s : G ⊢C Ord0 a -> G ⊢C Succ0 a s -> G ⊢C Ord0 s.
Proof using HG HR HOm HL. intros H1 H2. eapply ord_succ; [rzh..|exact H1|exact H2]. Qed.
Lemma rw_ord_union X u : G ⊢C ∀ ($0 ∈' X`[↑] → Ord0 $0) -> G ⊢C Union0 X u -> G ⊢C Ord0 u.
Proof using HG HR HOm HL. intros H1 H2. eapply ord_union; [rzh..|exact H1|exact H2]. Qed.
Lemma rw_ord_max a b : G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C ∃ (Ord0 $0 ∧ Sub0 a`[↑] $0 ∧ Sub0 b`[↑] $0).
Proof using HG HR HOm HL. intros H1 H2. eapply ord_max; [rzh..|exact H1|exact H2]. Qed.
Lemma rw_least_ord n psi sg a : fb (S n) psi -> In (least_inst n psi) G ->
  G ⊢C Ord0 a -> G ⊢C psi[a .: sg] ->
  G ⊢C ∃ (Ord0 $0 ∧ psi[up sg] ∧ ∀ ($0 ∈' $1 → ¬ psi[up (sg >> subst_term ↑)])).
Proof using HG HR HOm HL. intros H1 H2 H3 H4. eapply least_ord; [rzh..|exact H1|exact H2|exact H3|exact H4]. Qed.
Lemma rw_ord_collect n Q sg X : fb (S (S n)) Q -> incl (oc_insts n Q) G ->
  G ⊢C ∀ ($0 ∈' X`[↑] → ∃ (Ord0 $0 ∧ Q[up (up sg)])) ->
  G ⊢C ∀ (∀ (∀ (Ord0 $1 → Ord0 $0 → Sub0 $1 $0 →
                Q[$1 .: $2 .: (fun k => (sg k)`[↑]`[↑]`[↑])] → Q[$0 .: $2 .: (fun k => (sg k)`[↑]`[↑]`[↑])]))) ->
  G ⊢C ∃ (Ord0 $0 ∧ ∀ ($0 ∈' X`[↑]`[↑] → Q[$1 .: $0 .: (fun k => (sg k)`[↑]`[↑])])).
Proof using HG HR HOm HL. intros H1 H2 H3 H4. eapply ord_collect; [rzh..|exact H1|exact H2|exact H3|exact H4]. Qed.
Lemma rw_LL_ex a : G ⊢C Ord0 a -> G ⊢C ∃ LL a`[↑] $0.
Proof using HG HR HOm HL. intros H1. eapply LL_ex; [rzh..|exact H1]. Qed.
Lemma rw_LL_unique a Y Y' : G ⊢C Ord0 a -> G ⊢C LL a Y -> G ⊢C LL a Y' -> G ⊢C Y ≡' Y'.
Proof using HG HR HOm HL. intros H1 H2 H3. eapply LL_unique; [rzh..|exact H1|exact H2|exact H3]. Qed.
Lemma rw_LL_lim l Y : G ⊢C Lim0 l -> G ⊢C LL l Y ->
  G ⊢C ∀ ($0 ∈' Y`[↑] → ∃ ($0 ∈' l`[↑]`[↑] ∧ ∃ (LL $1 $0 ∧ $2 ∈' $0))).
Proof using HG HR HOm HL. intros H1 H2. eapply LL_lim; [rzh..|exact H1|exact H2]. Qed.
Lemma rw_LL_mono a b Ya Yb : G ⊢C Ord0 a -> G ⊢C b ∈' a -> G ⊢C LL a Ya -> G ⊢C LL b Yb ->
  G ⊢C Yb ∈' Ya ∧ Sub0 Yb Ya.
Proof using HG HR HOm HL. intros H1 H2 H3 H4. eapply LL_mono; [rzh..|exact H1|exact H2|exact H3|exact H4]. Qed.
Lemma rw_LL_sub a b Ya Yb : G ⊢C Ord0 a -> G ⊢C Ord0 b -> G ⊢C Sub0 b a -> G ⊢C LL a Ya -> G ⊢C LL b Yb ->
  G ⊢C Sub0 Yb Ya.
Proof using HG HR HOm HL. intros H1 H2 H3 H4 H5. eapply LL_sub; [rzh..|exact H1|exact H2|exact H3|exact H4|exact H5]. Qed.
Lemma rw_L_above x a : G ⊢C InL x -> G ⊢C Ord0 a ->
  G ⊢C ∃ (∃ (Ord0 $1 ∧ Sub0 a`[↑]`[↑] $1 ∧ LL $1 $0 ∧ x`[↑]`[↑] ∈' $0)).
Proof using HG HR HOm HL. intros H1 H2. eapply L_above; [rzh..|exact H1|exact H2]. Qed.

End W.

(** ** Monotonicity and elimination *)
Lemma Ew_mono {G} b Z Z' : G ⊢C Sub0 Z Z' -> G ⊢C Ew b Z -> G ⊢C Ew b Z'.
Proof.
  intros HS H. unfold Ew in *. fintro Hw. fmp H Hw. fex H y Hy. fdestr Hy Hy1 Hy2.
  fexists y. fsplit; [|exact Hy2]. unfold Sub0 in HS. finst HS y. exact (IE HS Hy1).
Qed.

Lemma Dn_step_eq K D d X x sg :
  (Dn K D)[$1 .: $2 .: $0 .: (fun k => $(3 + k))][up (d .: X .: sg)][x..] = (Dn K D)[d .: X .: x .: sg].
Proof. rewrite !subst_comp. apply subst_ext. intros [|[|[|k]]]; cbn; now rewrite ?subst_term_shift. Qed.

Definition appf (K : nat) (tau sg : nat -> term) : nat -> term := fun k => if k <? K then tau k else sg (k - K).
Lemma appf_0 tau sg k : appf 0 tau sg k = sg k.
Proof. unfold appf. cbn. now rewrite Nat.sub_0_r. Qed.
Lemma appf_S K tau sg k : appf K tau (tau K .: sg) k = appf (S K) tau sg k.
Proof.
  unfold appf. destruct (Nat.ltb_spec k K), (Nat.ltb_spec k (S K)); try lia; try reflexivity.
  - assert (k = K) by lia. subst k. now rewrite Nat.sub_diag.
  - replace (k - K) with (S (k - S K)) by lia. reflexivity.
Qed.
Lemma appf_lt K tau sg k : k < K -> appf K tau sg k = tau k.
Proof. intros H. unfold appf. destruct (Nat.ltb_spec k K); [reflexivity|lia]. Qed.

Lemma Dn_elim G D d X tau : forall K sg, G ⊢C (Dn K D)[d .: X .: sg] ->
  (forall k, k < K -> G ⊢C tau k ∈' X) -> G ⊢C D[d .: X .: appf K tau sg].
Proof.
  induction K as [|K IH]; intros sg H Ht.
  - refine (rf_conv _ _ _ _ _ H). intros [|[|k]]; [reflexivity|reflexivity|]. exact (eq_sym (appf_0 tau sg k)).
  - cbn in H. apply (AllE (tau K)) in H. cbn in H. rewrite subst_term_shift in H.
    pose proof (IE H (Ht K ltac:(lia))) as H'. rewrite Dn_step_eq in H'.
    apply IH in H'; [|intros k Hk; apply Ht; lia].
    refine (rf_conv _ _ _ _ _ H'). intros [|[|k]]; [reflexivity|reflexivity|]. exact (appf_S K tau sg k).
Qed.

Lemma Dn_mono D d d' X : forall K G sg,
  (forall G' rho, incl G G' -> G' ⊢C D[d .: X .: rho] -> G' ⊢C D[d' .: X .: rho]) ->
  G ⊢C (Dn K D)[d .: X .: sg] -> G ⊢C (Dn K D)[d' .: X .: sg].
Proof.
  induction K as [|K IH]; intros G sg HD H.
  - exact (HD G sg (fun a Ha => Ha) H).
  - cbn in H |- *. apply AllI_named. intros x. cbn. rewrite subst_term_shift. apply II.
    apply (AllE x) in H. cbn in H. rewrite subst_term_shift in H.
    assert (Hx : (x ∈' X :: G) ⊢C x ∈' X) by (apply Ctx; now left).
    pose proof (IE (weak_cons _ _ _ H) Hx) as H'.
    rewrite Dn_step_eq in H' |- *. apply (IH (x ∈' X :: G)); [|exact H'].
    intros G' rho HG'. apply HD. intros a Ha. apply HG'. now right.
Qed.

Local Tactic Notation "gchange" constr(phi) := match goal with |- ?G ⊢C _ => change (G ⊢C phi) end.

Lemma Ew_conv G b s1 s2 Z : (forall k, s1 k = s2 k) -> G ⊢C Ew (b[s1]) Z -> G ⊢C Ew (b[s2]) Z.
Proof. intros E H. now rewrite <- (subst_ext b E). Qed.
Lemma Ew_conv_fb G b N s1 s2 Z : fb N b -> (forall k, k < N -> s1 k = s2 k) -> G ⊢C Ew (b[s1]) Z -> G ⊢C Ew (b[s2]) Z.
Proof. intros Hb E H. now rewrite <- (subst_ext_fb b N s1 s2 Hb E). Qed.

(** pointwise equalities of composed substitutions *)
Local Ltac rpw := cbn; unfold funcomp; cbn; rewrite ?subst_term_comp; cbn;
  first [ reflexivity | (apply subst_term_ext; intros [|]; reflexivity)
        | (apply subst_term_id; intros [|]; reflexivity)
        | (symmetry; apply subst_term_id; intros [|]; reflexivity) ].

Lemma D0f_mono {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G)
  b d d' X rho : G ⊢C Ord0 d -> G ⊢C Ord0 d' -> G ⊢C Sub0 d d' ->
  G ⊢C (D0f b)[d .: X .: rho] -> G ⊢C (D0f b)[d' .: X .: rho].
Proof.
  intros Hd Hd' Hs H. unfold D0f in *. simp_in H. fall Z1. fintro HZ1.
  fobtain (rw_LL_ex HG HR HOm HL d Hd) as Z0 HZ0. finst H Z0. fmp H HZ0.
  fhave Hsub : (rw_LL_sub HG HR HOm HL d' d Z1 Z0 Hd' Hd Hs HZ1 HZ0).
  pose proof (Ew_mono _ _ _ Hsub H) as H2. rewrite ?subst_comp in H2; rewrite ?subst_comp.
  refine (Ew_conv _ _ _ _ _ _ H2). intros [|k]; rpw.
Qed.

Lemma D0f_mono_lift {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G)
  b d d' X : G ⊢C Ord0 d -> G ⊢C Ord0 d' -> G ⊢C Sub0 d d' ->
  forall G' rho, incl G G' -> G' ⊢C (D0f b)[d .: X .: rho] -> G' ⊢C (D0f b)[d' .: X .: rho].
Proof.
  intros Hd Hd' Hs G' rho HG' H.
  apply (D0f_mono (incl_tran HG HG') (HG' _ HR) (HG' _ HOm) (incl_tran HL HG') b d d' X rho);
    [exact (Weak Hd HG')|exact (Weak Hd' HG')|exact (Weak Hs HG')|exact H].
Qed.

(** the base case of the collection: one δ for a single tuple *)
Lemma wit_bound {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G)
  b X g rho : G ⊢C Ord0 g -> G ⊢C ∃ (Ord0 $0 ∧ (D0f b)[$0 .: X`[↑] .: rho >> subst_term ↑]).
Proof.
  intros Hg. apply (XM_rule _ (∃ (Lform ∧ b[up rho]))).
  - fintro Hw. pose proof Hw as Hw'. fex Hw' y Hy. fdestr Hy HyL Hyb.
    fobtain (rw_L_above HG HR HOm HL y g HyL Hg) as d Hd. fex Hd Yd HYd.
    fdestr HYd HYd1 HyY. fdestr HYd1 HYd2 HLd. fdestr HYd2 Hdo Hdsub.
    fexists d. fsplit; [exact Hdo|]. unfold D0f. simp. fall Z0. fintro HZ.
    fhave E : (rw_LL_unique HG HR HOm HL d Yd Z0 Hdo HLd HZ).
    rewrite ?subst_comp. refine (Ew_conv _ b (up rho) _ _ _ _); [intros [|k]; rpw|].
    unfold Ew. fintro Hdum. fexists y. fsplit; [|exact Hyb]. fmem.
  - fintro Hn. fexists g. fsplit; [exact Hg|]. unfold D0f. simp. fall Z0. fintro HZ.
    rewrite ?subst_comp. refine (Ew_conv _ b (up rho) _ _ _ _); [intros [|k]; rpw|].
    unfold Ew. fintro Hw. fabsurd. exact (IE Hn Hw).
Qed.

(** collection over K bounded variables *)
Lemma cb_gen b X : forall K n G, incl ZF0base G -> In ax_reg' G -> In ax_om' G -> incl Ax_L G ->
  forall sg, fb (S K + n) b -> incl (cinsts K n b) G ->
  (forall G' rho, incl G G' -> G' ⊢C ∃ (Ord0 $0 ∧ (D0f b)[$0 .: X`[↑] .: rho >> subst_term ↑])) ->
  G ⊢C ∃ (Ord0 $0 ∧ (Dn K (D0f b))[$0 .: X`[↑] .: sg >> subst_term ↑]).
Proof.
  induction K as [|K IH]; intros n G HG HR HOm HL sg Hfb HI Hbase.
  - exact (Hbase G sg (fun a Ha => Ha)).
  - assert (HQ : fb (S (S (S n))) (Qf K b)) by (apply fb_Qf; exact Hfb).
    assert (HI1 : incl (oc_insts (S n) (Qf K b)) G)
      by (intros a Ha; apply HI; change (In a (oc_insts (S n) (Qf K b) ++ cinsts K (S n) b)); apply in_app_iff; now left).
    assert (HI2 : incl (cinsts K (S n) b) G)
      by (intros a Ha; apply HI; change (In a (oc_insts (S n) (Qf K b) ++ cinsts K (S n) b)); apply in_app_iff; now right).
    assert (Hfb2 : fb (S K + S n) b) by (replace (S K + S n) with (S (S K) + n) by lia; exact Hfb).
    assert (HGG : incl G G) by (intros a Ha; exact Ha).
    pose proof (rw_ord_collect HG HR HOm HL (S n) (Qf K b) (X .: sg) X HQ HI1) as HC.
    match type of HC with ?P1 -> ?P2 -> _ => assert (A1 : P1); [|assert (A2 : P2); [|specialize (HC A1 A2)]] end.
    + clear HC. fall v. fintro Hv.
      pose proof (IH (S n) _ HG HR HOm HL (v .: sg) Hfb2 HI2 (fun G' rho H' => Hbase G' rho (incl_tran HGG H'))) as T.
      fex T d Hd. fdestr Hd H1 H2. fexists d. fsplit; [exact H1|]. unfold Qf.
      rewrite ?subst_comp in H2; rewrite ?subst_comp. refine (rf_conv _ _ _ _ _ H2). intros [|[|[|k]]]; rpw.
    + clear HC A1. fall v. fall d. fall d'. fintro Hd. fintro Hd'. fintro Hs. fintro H. unfold Qf in *.
      rewrite ?subst_comp in H; rewrite ?subst_comp.
      apply (rf_conv _ _ (d' .: X .: v .: sg)); [intros [|[|[|k]]]; rpw|].
      apply (Dn_mono _ d d' X K _ (v .: sg)).
      * apply D0f_mono_lift; assumption.
      * refine (rf_conv _ _ _ _ _ H). intros [|[|[|k]]]; rpw.
    + fex HC d Hd. fdestr Hd H1 H2. fexists d. fsplit; [exact H1|]. cbn [Dn]. simp.
      fall v. fintro Hv. finst H2 v. fmp H2 Hv. unfold Qf in H2. rewrite ?subst_comp in H2; rewrite ?subst_comp.
      refine (rf_conv _ _ _ _ _ H2). intros [|[|[|k]]]; rpw.
Qed.

(** ** The condition [PCf] *)
Lemma Pc_mono {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G)
  K b d d' X : G ⊢C Ord0 d -> G ⊢C Ord0 d' -> G ⊢C Sub0 d d' -> G ⊢C Pc K b d X -> G ⊢C Pc K b d' X.
Proof.
  intros H1 H2 H3 H. unfold Pc in *. eapply Dn_mono; [|exact H]. apply D0f_mono_lift; assumption.
Qed.

Lemma PCf_mono {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G)
  d d' X : G ⊢C Ord0 d -> G ⊢C Ord0 d' -> G ⊢C Sub0 d d' ->
  forall ps, G ⊢C PCf ps d X -> G ⊢C PCf ps d' X.
Proof.
  intros H1 H2 H3 ps. induction ps as [|[K b] ps IH]; intros H; [exact H|].
  change (G ⊢C Pc K b d X ∧ PCf ps d X) in H. change (G ⊢C Pc K b d' X ∧ PCf ps d' X).
  fsplit; [exact (Pc_mono HG HR HOm HL K b d d' X H1 H2 H3 (CE1 H))|exact (IH (CE2 H))].
Qed.

Lemma PCf_in {G} ps K b d X : In (K, b) ps -> G ⊢C PCf ps d X -> G ⊢C Pc K b d X.
Proof.
  induction ps as [|[K' b'] ps IH]; intros Hin H; [destruct Hin|].
  change (G ⊢C Pc K' b' d X ∧ PCf ps d X) in H. destruct Hin as [E|Hin].
  - inversion E; subst. exact (CE1 H).
  - exact (IH Hin (CE2 H)).
Qed.

Lemma pcf_bound {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G)
  g X : forall ps, (forall K b, In (K, b) ps -> fb (S K) b) ->
  incl (flat_map (fun p => cinsts (fst p) 0 (snd p)) ps) G -> G ⊢C Ord0 g -> G ⊢C LL g X ->
  G ⊢C ∃ (Ord0 $0 ∧ g`[↑] ∈' $0 ∧ PCf ps $0 X`[↑]).
Proof.
  induction ps as [|[K b] ps IH]; intros Hfb HI Hg HX.
  - fobtain (rw_succ0_ex HG HR HOm HL g) as s Hs. fexists s. fsplit; [fsplit|].
    + exact (rw_ord_succ HG HR HOm HL g s Hg Hs).
    + unfold Succ0 in Hs. exact (CE1 (CE1 Hs)).
    + gchange (⊥ → ⊥). apply imp_refl.
  - assert (HI1 : incl (cinsts K 0 b) G)
      by (intros a Ha; apply HI; change (In a (cinsts K 0 b ++ flat_map (fun p => cinsts (fst p) 0 (snd p)) ps)); apply in_app_iff; now left).
    assert (HI2 : incl (flat_map (fun p => cinsts (fst p) 0 (snd p)) ps) G)
      by (intros a Ha; apply HI; change (In a (cinsts K 0 b ++ flat_map (fun p => cinsts (fst p) 0 (snd p)) ps)); apply in_app_iff; now right).
    assert (Hb : fb (S K + 0) b) by (rewrite Nat.add_0_r; apply (Hfb K b); now left).
    assert (Hfb' : forall K b, In (K, b) ps -> fb (S K) b) by (intros K' b' H'; apply Hfb; now right).
    fhave T1 : (IH Hfb' HI2 Hg HX). fex T1 d1 Hd1. fdestr Hd1 Hd1a Hd1P. fdestr Hd1a Hd1o Hgd1.
    assert (HGG : incl G G) by (intros a Ha; exact Ha).
    pose proof (cb_gen b X K 0 _ HG HR HOm HL (fun _ => X) Hb HI1
      (fun G' rho H' => wit_bound (incl_tran HG H') (H' _ HR) (H' _ HOm) (incl_tran HL H') b X g rho
         (Weak Hg H'))) as T2.
    fex T2 d2 Hd2. fdestr Hd2 Hd2o Hd2P.
    fobtain (rw_ord_max HG HR HOm HL d1 d2 Hd1o Hd2o) as d Hd. fdestr Hd Hda Hs2. fdestr Hda Hdo Hs1.
    fexists d. fsplit; [fsplit|].
    + exact Hdo.
    + unfold Sub0 in Hs1. finst Hs1 g. exact (IE Hs1 Hgd1).
    + gchange (Pc K b d X ∧ PCf ps d X). fsplit.
      * apply (Pc_mono HG HR HOm HL K b d2 d X Hd2o Hdo Hs2). unfold Pc.
        rewrite ?subst_comp in Hd2P. refine (rf_conv _ _ _ _ _ Hd2P). intros [|[|k]]; rpw.
      * exact (PCf_mono HG HR HOm HL d1 d X Hd1o Hdo Hs1 ps Hd1P).
Qed.

#[local] Arguments appf : simpl never.

(** ** The function F: γ ↦ the least δ with [Cond γ δ] *)
Lemma ex_cond {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G)
  ps x : (forall K b, In (K, b) ps -> fb (S K) b) ->
  incl (flat_map (fun p => cinsts (fst p) 0 (snd p)) ps) G -> G ⊢C ∃ (Ord0 $0 ∧ Cond ps x`[↑] $0).
Proof.
  intros Hfb HI. apply (XM_rule _ (Ord0 x)).
  - fintro Hx. fobtain (rw_LL_ex HG HR HOm HL x Hx) as X HX.
    fhave T : (pcf_bound HG HR HOm HL x X ps Hfb HI Hx HX). fex T d Hd. fdestr Hd Hd1 HdP. fdestr Hd1 Hdo Hxd.
    fexists d. fsplit; [exact Hdo|]. unfold Cond. fintro Hx'. fsplit; [exact Hxd|].
    fall X'. fintro HX'. fhave E : (rw_LL_unique HG HR HOm HL x X X' Hx HX HX').
    frew E (PCf ps d`[↑] $0). exact HdP.
  - fintro Hn. fobtain (rw_emp0_ex HG HR HOm HL) as e He. fexists e.
    fsplit; [exact (rw_ord_emp HG HR HOm HL e He)|].
    unfold Cond. fintro Hx. fabsurd. exact (IE Hn Hx).
Qed.

Lemma Rel2_phG ps x y : Std_setrec.Rel2 (phG ps) x y = LeastF ps x y.
Proof. unfold Std_setrec.Rel2, phG. rewrite LeastF_subst. reflexivity. Qed.

Lemma gtot {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G)
  ps : (forall K b, In (K, b) ps -> fb (S K) b) ->
  incl (flat_map (fun p => cinsts (fst p) 0 (snd p)) ps) G -> In (least_inst 1 (psiF ps)) G ->
  G ⊢C Std_setrec.GTot (phG ps).
Proof.
  intros Hfb HI Hl. unfold Std_setrec.GTot. fall x. rewrite Rel2_phG.
  fhave T : (ex_cond HG HR HOm HL ps x Hfb HI). fex T d Hd. fdestr Hd Hdo Hc.
  assert (Hp : fb 2 (psiF ps)) by (unfold psiF; apply fb_Cond; cbn; lia).
  fassert Hc' : ((psiF ps)[d .: x..]); [unfold psiF; simp; exact Hc|].
  fhave T2 : (rw_least_ord HG HR HOm HL 1 (psiF ps) (x..) d Hp Hl Hdo Hc').
  unfold psiF in T2. simp_in T2. unfold LeastF. simp. exact T2.
Qed.

Lemma gfun {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G)
  ps : G ⊢C Std_setrec.GFun (phG ps).
Proof.
  unfold Std_setrec.GFun. fall x. fall y. fall y'. rewrite !Rel2_phG. fintro H1. fintro H2.
  unfold LeastF in H1, H2. fdestr H1 H1a H1m. fdestr H1a H1o H1c. fdestr H2 H2a H2m. fdestr H2a H2o H2c.
  fhave T : (rw_ord_tri HG HR HOm HL y y' H1o H2o). fcases T T1 T3. fcases T1 Ta Tb.
  - fabsurd. finst H2m y. fmp H2m Ta. exact (IE H2m H1c).
  - exact Tb.
  - fabsurd. finst H1m y'. fmp H1m T3. exact (IE H1m H2c).
Qed.

(** a set containing a and closed under a total functional relation (ω-iteration, Std_setrec) *)
Lemma closure_om {G} (HG : incl ZF0base G) phG (HI : incl (Std_setrec.rec_insts phSig phG) G)
  (HT : In sepTnf G) (HOm : In ax_om' G) a :
  G ⊢C Std_setrec.GTot phG -> G ⊢C Std_setrec.GFun phG -> G ⊢C ∃ Std_setrec.Clos phG a`[↑] $0.
Proof.
  intros Htotg Hfun. assert (Hom : G ⊢C ax_om') by (apply Ctx; exact HOm).
  rewrite ax_om'_eq in Hom.
  fex Hom Om HOm'. unfold is_om in HOm'. fdestr HOm' HInd HMin.
  fhave T : (ind_e Om HInd). fex T e He0. fdestr He0 He HeO.
  pose proof (sep_use _ 0 tnf_form var Om HT fb_tnf) as T. unfold tnf_form in T. simp_in T. fex T X HXc.
  fassert HXi : (is_inductive X).
  { unfold is_inductive. fsplit.
    - fexists e. fsplit; [exact He|]. pose proof HXc as H. finst H e. apply (iff_r _ _ _ H). clear H.
      fsplit; [exact HeO|]. unfold TNF. fsplit.
      + unfold Trans. fall y. fall m. fintro H1. fintro H2. fabsurd. exact (eset_el HG e m He H2).
      + fintro H. exact (eset_el HG e e He H).
    - fall u. fintro Hu. pose proof HXc as H. finst H u. fhave Hu' : (iff_l _ _ _ H Hu). clear H.
      fdestr Hu' HuO HuT. unfold TNF in HuT. fdestr HuT HuTr HuN.
      fhave T : (ind_s Om u HInd HuO). fex T s Hs0. fdestr Hs0 Hs HsO.
      fexists s. fsplit; [exact Hs|]. pose proof HXc as H. finst H s. apply (iff_r _ _ _ H). clear H.
      fsplit; [exact HsO|]. unfold TNF. fsplit.
      + unfold Trans. fall y. fall m. fintro Hym. fintro Hms.
        fhave T : (succ_el HG u s m Hs Hms). fcases T T1 T2.
        * apply (succ_in_l HG u s y Hs). unfold Trans in HuTr. finst HuTr y m. fmp HuTr Hym. fmp HuTr T1. exact HuTr.
        * apply (succ_in_l HG u s y Hs). fmem.
      + fintro Hss. fhave Hus : (succ_self HG u s Hs). fhave T : (succ_el HG u s s Hs Hss). fcases T T1 T2.
        * unfold Trans in HuTr. finst HuTr u s. fmp HuTr Hus. fmp HuTr T1. exact (IE HuN HuTr).
        * fassert Huu : (u ∈' u); [fmem|]. exact (IE HuN Huu). }
  fassert HOX : (∀ ($0 ∈' Om`[↑] → TNF $0)).
  { fall n. fintro Hn. pose proof HMin as H. finst H X. fmp H HXi. unfold sub' in H. finst H n. fmp H Hn.
    pose proof HXc as H'. finst H' n. exact (CE2 (iff_l _ _ _ H' H)). }
  fassert Htot : (Std_setrec.STot phSig Om).
  { unfold Std_setrec.STot, phSig. fall z. fintro Hz. exact (ind_s Om z HInd Hz). }
  fassert Hinj : (Std_setrec.SInj phSig Om).
  { unfold Std_setrec.SInj, phSig. fall z1. fall z2. fall z'. fintro H1. fintro H2. fintro H3. fintro H4.
    pose proof HOX as H. finst H z1. fmp H H1. unfold TNF in H. fdestr H Htr Hn.
    fhave Hz1 : (succ_self HG z1 z' H3). fhave Hz2 : (succ_self HG z2 z' H4).
    fhave T : (succ_el HG z2 z' z1 H4 Hz1). fcases T T1 T2.
    - fhave T : (succ_el HG z1 z' z2 H3 Hz2). fcases T T3 T4.
      + unfold Trans in Htr. finst Htr z1 z2. fmp Htr T1. fmp Htr T3. fabsurd. exact (IE Hn Htr).
      + feq.
    - exact T2. }
  fassert Hnz : (Std_setrec.SNz phSig e Om).
  { unfold Std_setrec.SNz, phSig. fall z. fintro Hz. fintro Hs. exact (eset_el HG e z He (succ_self HG z e Hs)). }
  fassert Hind : (Std_setrec.SInd phSig e Om).
  { unfold Std_setrec.SInd, phSig. fall Y. fintro HeY. fintro Hcl. fall z. fintro Hz.
    pose proof HMin as H. finst H Y. fassert HYi : (is_inductive Y).
    { unfold is_inductive. fsplit; [|exact Hcl]. fexists e. fsplit; [exact He|exact HeY]. }
    fmp H HYi. unfold sub' in H. finst H z. exact (IE H Hz). }
  exact (Std_setrec.closure_thm HG phSig phG HI Om e a HeO Htot Hinj Hnz Hind Htotg Hfun).
Qed.

(** ** Finitely many elements of L_β lie in a common level L_κ, κ ∈ K *)
Lemma common_level {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G)
  Ks Lb a : G ⊢C a ∈' Ks -> G ⊢C ∀ ($0 ∈' Ks`[↑] → Ord0 $0) ->
  G ⊢C ∀ ($0 ∈' Lb`[↑] → ∃ ($0 ∈' Ks`[↑]`[↑] ∧ ∃ (LL $1 $0 ∧ $2 ∈' $0))) ->
  forall tau K theta, (forall k, k < K -> G ⊢C tau k ∈' Lb) ->
  (forall G' k Xk, incl G G' -> G' ⊢C k ∈' Ks -> G' ⊢C LL k Xk -> (forall j, j < K -> G' ⊢C tau j ∈' Xk) ->
     G' ⊢C theta) ->
  G ⊢C theta.
Proof.
  intros Ha HKo Hlev tau K. induction K as [|K IH]; intros theta Ht Hk.
  - pose proof HKo as Hao. finst Hao a. fmp Hao Ha. assert (HGG : incl G G) by (intros c Hc; exact Hc).
    fobtain (rw_LL_ex HG HR HOm HL a Hao) as Xa HXa.
    apply (Hk _ a Xa HGG Ha HXa). intros j Hj. lia.
  - apply (IH theta (fun j Hj => Ht j ltac:(lia))). intros G1 k1 X1 HG1 Hk1 HX1 Ht1.
    pose proof (incl_tran HG HG1) as HG'. pose proof (HG1 _ HR) as HR'. pose proof (HG1 _ HOm) as HOm'.
    pose proof (incl_tran HL HG1) as HL'.
    pose proof (Weak HKo HG1) as HKo1. pose proof (Weak Hlev HG1) as Hlev1.
    pose proof (Ht K (Nat.lt_succ_diag_r K)) as HtK0. pose proof (Weak HtK0 HG1) as HtK. clear Ht HtK0.
    finst Hlev1 (tau K). fmp Hlev1 HtK. fex Hlev1 k2 Hk2. fdestr Hk2 Hk2K Hk2e. fex Hk2e X2 HX2.
    fdestr HX2 HX2L HtX2.
    pose proof HKo1 as Ho1. finst Ho1 k1. fmp Ho1 Hk1. pose proof HKo1 as Ho2. finst Ho2 k2. fmp Ho2 Hk2K.
    fhave T : (rw_ord_tri HG' HR' HOm' HL' k1 k2 Ho1 Ho2). fcases T T1 T3. fcases T1 Ta Tb.
    + fhave M : (rw_LL_mono HG' HR' HOm' HL' k2 k1 X2 X1 Ho2 Ta HX2L HX1). fdestr M M1 M2.
      apply (Hk _ k2 X2); [assumption|exact Hk2K|exact HX2L|]. intros j Hj.
      destruct (Nat.eq_dec j K) as [->|Hne]; [exact HtX2|].
      unfold Sub0 in M2. finst M2 (tau j). exact (IE M2 (Ht1 j ltac:(lia))).
    + frew_in Tb (LL $0 X2`[↑]) HX2L. fhave E : (rw_LL_unique HG' HR' HOm' HL' k1 X2 X1 Ho1 HX2L HX1).
      apply (Hk _ k1 X1); [assumption|exact Hk1|exact HX1|]. intros j Hj.
      destruct (Nat.eq_dec j K) as [->|Hne]; [fmem|exact (Ht1 j ltac:(lia))].
    + fhave M : (rw_LL_mono HG' HR' HOm' HL' k1 k2 X1 X2 Ho1 T3 HX1 HX2L). fdestr M M1 M2.
      apply (Hk _ k1 X1); [assumption|exact Hk1|exact HX1|]. intros j Hj.
      destruct (Nat.eq_dec j K) as [->|Hne]; [|exact (Ht1 j ltac:(lia))].
      unfold Sub0 in M2. finst M2 (tau K). exact (IE M2 HtX2).
Qed.

(** ** Tarski-Vaught: witness closure of all pieces gives reflection *)
Definition PH (G0 : list form) (Lb : term) (K : nat) (b : form) : Prop :=
  forall G' tau, incl G0 G' -> (forall k, k < K -> G' ⊢C tau k ∈' Lb) -> G' ⊢C Ew (b[up tau]) Lb.

Lemma TV {G0} Lb (HLsub : forall G' y, incl G0 G' -> G' ⊢C y ∈' Lb -> G' ⊢C InL y) (psi : form) :
  forall N, (forall K b, In (K, b) (pcs N psi) -> PH G0 Lb K b) ->
  forall G sg, incl G0 G -> (forall k, k < N -> G ⊢C sg k ∈' Lb) ->
  G ⊢C rel Lform (psi[sg]) ↔ relS Lb (psi[sg]).
Proof.
  induction psi as [|P v|op a IHa c IHc|q a IHa] using form_ind_falsity; intros N HP G sg HG0 Hsg.
  - cbn. apply iff_refl'.
  - cbn. apply iff_refl'.
  - cbn. apply iff_bin.
    + apply (IHa N); auto. intros K b Hin. apply HP. cbn. apply in_app_iff. now left.
    + apply (IHc N); auto. intros K b Hin. apply HP. cbn. apply in_app_iff. now right.
  - assert (HPa : forall K b, In (K, b) (pcs (S N) a) -> PH G0 Lb K b)
      by (intros K b Hin; apply HP; cbn; right; right; exact Hin).
    assert (HP1 : PH G0 Lb N (rel Lform a)) by (apply HP; cbn; now left).
    assert (HP2 : PH G0 Lb N (¬ rel Lform a)) by (apply HP; cbn; right; now left).
    clear HP.
    destruct q; cbn.
    + fsplit.
      * fintro H. fall y. fintro Hy. finst H y. fhave HyL : (HLsub _ y HG0 Hy). fmp H HyL.
        refine (iff_l _ _ _ (IHa (S N) HPa _ (y .: sg) HG0 _) H).
        intros [|k] Hk; [exact Hy|apply Hsg; lia].
      * fintro H. fall y. fintro HyL. fcontra Hn.
        pose proof (HP2 _ sg HG0 Hsg) as W. simp_in W. unfold Ew in W.
        fassert Hex : (∃ (Lform ∧ ¬ rel Lform (a[up sg]))).
        { fexists y. fsplit; [exact HyL|exact Hn]. }
        fmp W Hex. fex W y' Hy'. fdestr Hy' Hy'1 Hy'2. finst H y'. fmp H Hy'1.
        refine (IE Hy'2 (iff_r _ _ _ (IHa (S N) HPa _ (y' .: sg) HG0 _) H)).
        intros [|k] Hk; [exact Hy'1|apply Hsg; lia].
    + fsplit.
      * fintro H. pose proof (HP1 _ sg HG0 Hsg) as W. simp_in W. unfold Ew in W.
        fmp W H. fex W y Hy. fdestr Hy Hy1 Hy2. fexists y. fsplit; [exact Hy1|].
        refine (iff_l _ _ _ (IHa (S N) HPa _ (y .: sg) HG0 _) Hy2).
        intros [|k] Hk; [exact Hy1|apply Hsg; lia].
      * fintro H. fex H y Hy. fdestr Hy Hy1 Hy2. fexists y. fsplit; [exact (HLsub _ y HG0 Hy1)|].
        refine (iff_r _ _ _ (IHa (S N) HPa _ (y .: sg) HG0 _) Hy2).
        intros [|k] Hk; [exact Hy1|apply Hsg; lia].
Qed.

(** the pieces hold for L_β, from the closure property of K *)
Lemma PH_from {G} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G)
  ps Ks bt Lb a : G ⊢C a ∈' Ks -> G ⊢C ∀ ($0 ∈' Ks`[↑] → Ord0 $0) ->
  G ⊢C ∀ ($0 ∈' Lb`[↑] → ∃ ($0 ∈' Ks`[↑]`[↑] ∧ ∃ (LL $1 $0 ∧ $2 ∈' $0))) ->
  G ⊢C ∀ ($0 ∈' Ks`[↑] → ∃ ($0 ∈' Ks`[↑]`[↑] ∧ ($1 ∈' $0 ∧ ∀ (LL $2 $0 → PCf ps $1 $0)))) ->
  G ⊢C Ord0 bt -> G ⊢C LL bt Lb -> G ⊢C ∀ ($0 ∈' Ks`[↑] → Sub0 $0 bt`[↑]) ->
  forall K b, In (K, b) ps -> fb (S K) b -> PH G Lb K b.
Proof.
  intros Ha HKo Hlev HKF Hbo HLb HKsub K b Hin Hb G' tau HGG' Ht.
  pose proof (incl_tran HG HGG') as HG'. pose proof (HGG' _ HR) as HR'. pose proof (HGG' _ HOm) as HOm'.
  pose proof (incl_tran HL HGG') as HL'.
  apply (common_level HG' HR' HOm' HL' Ks Lb a (Weak Ha HGG') (Weak HKo HGG') (Weak Hlev HGG') tau K _ Ht).
  intros G1 k Xk HG1 Hk HXk Htk.
  pose proof (incl_tran HGG' HG1) as HG01. clear HG' HR' HOm' HL'.
  pose proof (incl_tran HG HG01) as HG1'. pose proof (HG01 _ HR) as HR1. pose proof (HG01 _ HOm) as HOm1.
  pose proof (incl_tran HL HG01) as HL1.
  pose proof (Weak HKF HG01) as HKF1. pose proof (Weak HKo HG01) as HKo1. pose proof (Weak Hbo HG01) as Hbo1.
  pose proof (Weak HLb HG01) as HLb1. pose proof (Weak HKsub HG01) as HKsub1.
  clear Ha HKo Hlev HKF Hbo HLb HKsub HG HR HOm HL.
  finst HKF1 k. fmp HKF1 Hk. fex HKF1 w Hw. fdestr Hw HwK Hw2. fdestr Hw2 Hkw HwP.
  finst HwP Xk. fmp HwP HXk.
  pose proof (PCf_in ps K b w Xk Hin HwP) as HP. unfold Pc in HP.
  pose proof (Dn_elim _ _ w Xk tau K _ HP Htk) as HD. unfold D0f in HD. simp_in HD.
  pose proof HKo1 as Hwo. finst Hwo w. fmp Hwo HwK.
  fobtain (rw_LL_ex HG1' HR1 HOm1 HL1 w Hwo) as Lw HLw. finst HD Lw. fmp HD HLw.
  pose proof HKsub1 as Hws. finst Hws w. fmp Hws HwK.
  fhave Hsub : (rw_LL_sub HG1' HR1 HOm1 HL1 bt w Lb Lw Hbo1 Hwo Hws HLb1 HLw).
  apply (Ew_mono _ Lw Lb Hsub). rewrite ?subst_comp in HD.
  refine (Ew_conv_fb _ b (S K) _ _ _ Hb _ HD). intros [|j] Hj; [reflexivity|].
  cbn. unfold funcomp. cbn. rewrite (appf_lt K tau _ j ltac:(lia)). rewrite ?subst_term_comp.
  apply subst_term_ext. intros [|]; reflexivity.
Qed.

(** ** The main theorems *)
Section Refl.
Context {G : list form} (HG : incl ZF0base G) (HR : In ax_reg' G) (HOm : In ax_om' G) (HL : incl Ax_L G).

Theorem reflection m phi a : fb m phi -> incl (refl_insts m phi) G -> G ⊢C Ord0 a ->
  G ⊢C ∃ (Ord0 $0 ∧ a`[↑] ∈' $0 ∧ Refl m phi $0).
Proof using HG HR HOm HL.
  intros Hfb HI Ha. unfold refl_insts in HI. set (ps := pcs m phi) in HI.
  assert (Hpfb : forall K b, In (K, b) ps -> fb (S K) b) by (intros K b Hin; exact (pcs_fb phi m Hfb K b Hin)).
  assert (HI1 : incl (flat_map (fun p => cinsts (fst p) 0 (snd p)) ps) G)
    by (intros c Hc; apply HI, in_app_iff; now left).
  assert (Hl : In (least_inst 1 (psiF ps)) G) by (apply HI, in_app_iff; right; now left).
  assert (HO : In sepOrd G) by (apply HI, in_app_iff; right; right; now left).
  assert (HT : In sepTnf G) by (apply HI, in_app_iff; right; right; right; now left).
  assert (HIr : incl (Std_setrec.rec_insts phSig (phG ps)) G)
    by (intros c Hc; apply HI, in_app_iff; right; right; right; right; exact Hc).
  clear HI.
  pose proof (gtot HG HR HOm HL ps Hpfb HI1 Hl) as Htot. pose proof (gfun HG HR HOm HL ps) as Hfun.
  fhave T : (closure_om HG (phG ps) HIr HT HOm a Htot Hfun). fex T Y HY.
  unfold Std_setrec.Clos in HY. fdestr HY HaY HYc.
  pose proof (sep_use _ 0 (Ord0 $0) var Y HO ltac:(fbcomp)) as T. simp_in T. fex T Ks HKs.
  fobtain (rw_union0_ex HG HR HOm HL Ks) as bt Hbt.
  fassert HKo : (∀ ($0 ∈' Ks`[↑] → Ord0 $0)).
  { fall k. fintro Hk. pose proof HKs as H. finst H k. exact (CE2 (iff_l _ _ _ H Hk)). }
  fassert HaK : (a ∈' Ks).
  { pose proof HKs as H. finst H a. apply (iff_r _ _ _ H). fsplit; [exact HaY|exact Ha]. }
  fassert HKF : (∀ ($0 ∈' Ks`[↑] → ∃ ($0 ∈' Ks`[↑]`[↑] ∧ ($1 ∈' $0 ∧ ∀ (LL $2 $0 → PCf ps $1 $0))))).
  { fall k. fintro Hk. pose proof HKs as H. finst H k. fhave Hk' : (iff_l _ _ _ H Hk). fdestr Hk' HkY Hko.
    pose proof HYc as H2. finst H2 k. fmp H2 HkY. fex H2 w Hw. fdestr Hw HwF HwY. rewrite Rel2_phG in HwF.
    unfold LeastF in HwF. fdestr HwF HwF1 HwF2. fdestr HwF1 Hwo Hwc. unfold Cond in Hwc. fmp Hwc Hko.
    fdestr Hwc Hkw HwP.
    fexists w. fsplit; [|fsplit; [exact Hkw|exact HwP]].
    pose proof HKs as H3. finst H3 w. apply (iff_r _ _ _ H3). fsplit; [exact HwY|exact Hwo]. }
  fassert HKsub : (∀ ($0 ∈' Ks`[↑] → Sub0 $0 bt`[↑])).
  { fall k. fintro Hk. unfold Sub0. fall z. fintro Hz. pose proof Hbt as H. unfold Union0 in H.
    fdestr H H1 H2. finst H2 k. fmp H2 Hk. finst H2 z. exact (IE H2 Hz). }
  fassert Hbto : (Ord0 bt); [exact (rw_ord_union HG HR HOm HL Ks bt HKo Hbt)|].
  fassert Hbtl : (∀ ($0 ∈' bt`[↑] → ∃ ($0 ∈' Ks`[↑]`[↑] ∧ $1 ∈' $0))); [unfold Union0 in Hbt; exact (CE1 Hbt)|].
  fassert Hab : (a ∈' bt).
  { pose proof HKF as H. finst H a. fmp H HaK. fex H w Hw. fdestr Hw HwK Hw2. fdestr Hw2 Haw Hw3.
    pose proof HKsub as H2. finst H2 w. fmp H2 HwK. unfold Sub0 in H2. finst H2 a. exact (IE H2 Haw). }
  fassert Hlim : (Lim0 bt).
  { unfold Lim0. fsplit; [fsplit|].
    - exact Hbto.
    - fexists a. fsplit; [exact Hab|feq].
    - fall x. fintro Hx. pose proof Hbtl as H. finst H x. fmp H Hx. fex H k Hk. fdestr Hk HkK Hxk.
      pose proof HKF as H2. finst H2 k. fmp H2 HkK. fex H2 w Hw. fdestr Hw HwK Hw2. fdestr Hw2 Hkw Hw3.
      fexists k. fsplit; [|exact Hxk].
      pose proof HKsub as H3. finst H3 w. fmp H3 HwK. unfold Sub0 in H3. finst H3 k. exact (IE H3 Hkw). }
  fexists bt. fsplit; [fsplit; [exact Hbto|exact Hab]|].
  unfold Refl. fall Lb. fintro HLb.
  fassert Hlev : (∀ ($0 ∈' Lb`[↑] → ∃ ($0 ∈' Ks`[↑]`[↑] ∧ ∃ (LL $1 $0 ∧ $2 ∈' $0)))).
  { fall y. fintro Hy. fhave T : (rw_LL_lim HG HR HOm HL bt Lb Hlim HLb). finst T y. fmp T Hy.
    fex T g Hg. fdestr Hg Hgb Hg2. fex Hg2 Yg HYg. fdestr HYg HYgL HyYg.
    pose proof Hbtl as H. finst H g. fmp H Hgb. fex H k Hk. fdestr Hk HkK Hgk.
    pose proof HKo as H2. finst H2 k. fmp H2 HkK.
    fobtain (rw_LL_ex HG HR HOm HL k H2) as Xk HXk.
    fhave M : (rw_LL_mono HG HR HOm HL k g Xk Yg H2 Hgk HXk HYgL). fdestr M M1 M2.
    fexists k. fsplit; [exact HkK|]. fexists Xk. fsplit; [exact HXk|].
    unfold Sub0 in M2. finst M2 y. exact (IE M2 HyYg). }
  match goal with |- ?Gc ⊢C _ =>
    assert (HPH : forall K b, In (K, b) (pcs m phi) -> PH Gc Lb K b) by
      (intros K b Hin; exact (PH_from HG HR HOm HL ps Ks bt Lb a HaK HKo Hlev HKF Hbto HLb HKsub K b Hin (Hpfb K b Hin)));
    assert (HLsub : forall G' y, incl Gc G' -> G' ⊢C y ∈' Lb -> G' ⊢C InL y)
  end.
  { intros G' y HG' Hy. rewrite InL_eq. fexists bt. fexists Lb.
    fsplit; [fsplit; [exact (Weak Hbto HG')|exact (Weak HLb HG')]|exact Hy]. }
  rewrite ballS_subst. apply ballS_intro. intros G' sg HG' Hsg. rewrite refl_body by exact Hfb.
  exact (TV Lb HLsub phi m HPH G' sg HG' Hsg).
Qed.

Lemma refl_use m phi b Y sg : fb m phi -> G ⊢C Refl m phi b -> G ⊢C LL b Y ->
  (forall k, k < m -> G ⊢C sg k ∈' Y) -> G ⊢C rel Lform (phi[sg]) ↔ relS Y (phi[sg]).
Proof using HG HR HOm HL.
  intros Hfb H HY Hs. unfold Refl in H. apply (AllE Y) in H. cbn in H. rewrite LL_subst in H. cbn in H.
  rewrite subst_term_shift in H. pose proof (IE H HY) as H'. rewrite ballS_subst in H'.
  apply (ballS_elim _ _ _ _ sg) in H'; [|exact Hs]. rewrite refl_body in H' by exact Hfb. exact H'.
Qed.

End Refl.
