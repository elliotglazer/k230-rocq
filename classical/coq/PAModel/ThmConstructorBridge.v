(** Constructor-preserving transfer between the isolated original code
    calculus and the current code calculus. No set theory is imported. *)
From OldK230L Require Thm230 Codes230.
From K230L Require Thm230 Codes230.
From Coq Require Import Arith Lia.
Unset Implicit Arguments.

Module OK := OldK230S.KCode230.
Module NK := K230S.KCode230.
Module OR := OldK230L.Codes230.
Module NR := K230L.Codes230.

Lemma isolated_pair_current a b : OK.P a b = NK.P a b.
Proof. reflexivity. Qed.
Local Opaque OK.P NK.P.
Lemma isolated_wim_current a b : OK.wim a b = NK.wim a b.
Proof. unfold OK.wim,NK.wim. now rewrite isolated_pair_current. Qed.
Lemma isolated_wel_current a b : OK.wel a b = NK.wel a b.
Proof. unfold OK.wel,NK.wel. now rewrite isolated_pair_current. Qed.
Lemma isolated_weq_current a b : OK.weq a b = NK.weq a b.
Proof. unfold OK.weq,NK.weq. now rewrite isolated_pair_current. Qed.
Lemma isolated_wal_current a b : OK.wal a b = NK.wal a b.
Proof. unfold OK.wal,NK.wal. now rewrite isolated_pair_current. Qed.
Lemma isolated_wn_current a : OK.wn a = NK.wn a.
Proof. unfold OK.wn,NK.wn,OK.F,NK.F. apply isolated_wim_current. Qed.
Lemma isolated_wa_current a b : OK.wa a b = NK.wa a b.
Proof. unfold OK.wa,NK.wa. now rewrite !isolated_wn_current,isolated_wim_current. Qed.
Lemma isolated_wex_current a b : OK.wex a b = NK.wex a b.
Proof. unfold OK.wex,NK.wex. now rewrite !isolated_wn_current,isolated_wal_current. Qed.

Local Opaque OK.wim NK.wim OK.wel NK.wel OK.weq NK.weq OK.wal NK.wal
  OK.wn NK.wn OK.wa NK.wa OK.wex NK.wex.

Ltac isolated_constructors :=
  repeat lazymatch goal with
  | |- context[OK.wim ?a ?b] => rewrite (isolated_wim_current a b)
  | |- context[OK.wel ?a ?b] => rewrite (isolated_wel_current a b)
  | |- context[OK.weq ?a ?b] => rewrite (isolated_weq_current a b)
  | |- context[OK.wal ?a ?b] => rewrite (isolated_wal_current a b)
  | |- context[OK.wn ?a] => rewrite (isolated_wn_current a)
  | |- context[OK.wa ?a ?b] => rewrite (isolated_wa_current a b)
  | |- context[OK.wex ?a ?b] => rewrite (isolated_wex_current a b)
  end.

Lemma isolated_bundle_current a b c : OR.bundle a b c = NR.bundle a b c.
Proof.
  unfold OR.bundle,NR.bundle,OK.bundle230,NK.bundle230,OK.k230,NK.k230,
    OK.kcore,NK.kcore,OK.vacuity230,NK.vacuity230,
    OK.ksubset,NK.ksubset,OK.krequest,NK.krequest.
  isolated_constructors. reflexivity.
Qed.

Theorem original_thm230_to_current n :
  OldK230L.Thm230.thm230 n -> K230L.Thm230.thm230 n.
Proof.
  intro H. induction H as
    [|t b HT IHT HI IHI|a h HH IHH|a b|a b c|a b c|a b c|a b c|
     a b|a b c|a b c u|a b c Hca Hcb].
  - apply K230L.Thm230.T_true.
  - rewrite isolated_wim_current in IHI. exact (K230L.Thm230.T_mp t b IHT IHI).
  - rewrite isolated_wal_current. exact (K230L.Thm230.T_gen a h IHH).
  - unfold OR.rho1. isolated_constructors. exact (K230L.Thm230.T_r1 a b).
  - unfold OR.rho2. isolated_constructors. exact (K230L.Thm230.T_r2 a b c).
  - unfold OR.rho3. isolated_constructors. exact (K230L.Thm230.T_r3 a b c).
  - unfold OR.rho4. isolated_constructors. exact (K230L.Thm230.T_r4 a b c).
  - unfold OR.rho5. isolated_constructors. exact (K230L.Thm230.T_r5 a b c).
  - unfold OR.rho6. isolated_constructors. exact (K230L.Thm230.T_r6 a b).
  - unfold OR.rho7. isolated_constructors. exact (K230L.Thm230.T_r7 a b c).
  - unfold OR.rho8. isolated_constructors. exact (K230L.Thm230.T_r8 a b c u).
  - rewrite isolated_bundle_current. exact (K230L.Thm230.T_bundle a b c Hca Hcb).
Qed.

Print Assumptions original_thm230_to_current.
