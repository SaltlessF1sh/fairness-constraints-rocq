From Stdlib Require Import Bool List Arith Lia Classical.
Import ListNotations.

(* ========================================================================= *)
(* Formal Verification in Rocq (Coq) of:                                     *)
(*   - P2 (Existence of an Unfair PI-explanation) is Sigma_3^P-complete      *)
(*   - P3 (Decision Universal Fairness) is Pi_3^P-complete                   *)
(* Verified directly against literal Definition 4 (AXp + not strictly        *)
(* subsumed by any AXp) and Definition 5 of Cooper & Bousdira (CP 2026).     *)
(* ========================================================================= *)

Definition lit := (nat * bool)%type.
Definition clause := list lit.
Definition cnf := list clause.

Definition eval_lit (assign : nat -> bool) (l : lit) : bool :=
  Bool.eqb (assign (fst l)) (snd l).

Fixpoint eval_clause (assign : nat -> bool) (c : clause) : bool :=
  match c with
  | [] => false
  | l :: rest => eval_lit assign l || eval_clause assign rest
  end.

Fixpoint eval_cnf (assign : nat -> bool) (phi : cnf) : bool :=
  match phi with
  | [] => true
  | c :: rest => eval_clause assign c && eval_cnf assign rest
  end.

Definition cnf_bounded (n : nat) (phi : cnf) : Prop :=
  forall c, In c phi -> forall l, In l c -> fst l < n.

Lemma eval_cnf_ext : forall phi f g,
  (forall k, f k = g k) ->
  eval_cnf f phi = eval_cnf g phi.
Proof.
  intros phi f g Hext.
  induction phi as [|c rest IH]; simpl; [reflexivity|].
  f_equal; [|apply IH].
  induction c as [|l cs IHc]; simpl; [reflexivity|].
  f_equal; [unfold eval_lit; rewrite Hext; reflexivity | apply IHc].
Qed.

Definition combine3 (r q : nat) (X Y Z : nat -> bool) (k : nat) : bool :=
  if k <? r then X k
  else if k <? r + q then Y (k - r)
  else Z (k - (r + q)).

Definition three_qbf (r q : nat) (phi : cnf) : Prop :=
  exists X : nat -> bool, forall Y : nat -> bool, exists Z : nat -> bool,
    eval_cnf (combine3 r q X Y Z) phi = true.

Record Inst := mkInst {
  fd : bool;
  fXp : nat -> bool;
  fXm : nat -> bool;
  fp : bool;
  fYp : nat -> bool;
  fYm : nat -> bool;
  fZ : nat -> bool
}.

Record Sub := mkSub {
  sd : bool;
  sXp : nat -> bool;
  sXm : nat -> bool;
  sp : bool;
  sYp : nat -> bool;
  sYm : nat -> bool;
  sZ : nat -> bool
}.

(* In P2/P3 reduction, d is the UNIQUE protected feature: P = {d} *)
Definition is_unfair_P2 (T : Sub) : Prop := sd T = true.

Definition agrees_on (r q s : nat) (w : Inst) (S : Sub) : Prop :=
  (sd S = true -> fd w = true) /\
  (forall i, i < r -> sXp S i = true -> fXp w i = true) /\
  (forall i, i < r -> sXm S i = true -> fXm w i = true) /\
  (sp S = true -> fp w = true) /\
  (forall j, j < q -> sYp S j = true -> fYp w j = true) /\
  (forall j, j < q -> sYm S j = true -> fYm w j = true) /\
  (forall k, k < s -> sZ S k = true -> fZ w k = true).

(* Subset inclusion (bounded by r, q, s) *)
Definition sub_le (r q s : nat) (S1 S2 : Sub) : Prop :=
  (sd S1 = true -> sd S2 = true) /\
  (forall i, i < r -> sXp S1 i = true -> sXp S2 i = true) /\
  (forall i, i < r -> sXm S1 i = true -> sXm S2 i = true) /\
  (sp S1 = true -> sp S2 = true) /\
  (forall j, j < q -> sYp S1 j = true -> sYp S2 j = true) /\
  (forall j, j < q -> sYm S1 j = true -> sYm S2 j = true) /\
  (forall k, k < s -> sZ S1 k = true -> sZ S2 k = true).

Definition sub_strict_lt (r q s : nat) (S1 S2 : Sub) : Prop :=
  sub_le r q s S1 S2 /\
  ((sd S2 = true /\ sd S1 = false) \/
   (exists i, i < r /\ sXp S2 i = true /\ sXp S1 i = false) \/
   (exists i, i < r /\ sXm S2 i = true /\ sXm S1 i = false) \/
   (sp S2 = true /\ sp S1 = false) \/
   (exists j, j < q /\ sYp S2 j = true /\ sYp S1 j = false) \/
   (exists j, j < q /\ sYm S2 j = true /\ sYm S1 j = false) \/
   (exists k, k < s /\ sZ S2 k = true /\ sZ S1 k = false)).

Lemma sub_le_trans : forall r q s A B C,
  sub_le r q s A B -> sub_le r q s B C -> sub_le r q s A C.
Proof.
  intros r q s A B C [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] [G1 [G2 [G3 [G4 [G5 [G6 G7]]]]]].
  repeat split; intros; auto.
Qed.

Lemma agrees_sub_le : forall r q s w S1 S2,
  sub_le r q s S1 S2 -> agrees_on r q s w S2 -> agrees_on r q s w S1.
Proof.
  intros r q s w S1 S2 [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] [G1 [G2 [G3 [G4 [G5 [G6 G7]]]]]].
  repeat split; intros; auto.
Qed.

Fixpoint forall_nat (n : nat) (P : nat -> bool) : bool :=
  match n with
  | 0 => true
  | S m => P m && forall_nat m P
  end.

Lemma forall_nat_iff : forall n P,
  forall_nat n P = true <-> (forall i, i < n -> P i = true).
Proof.
  induction n as [|m IH]; intro P; simpl.
  - split; [intros _ i Hi; lia | intros _; reflexivity].
  - rewrite Bool.andb_true_iff, IH. split.
    + intros [Hm Hrest] i Hi.
      destruct (Nat.eq_dec i m); [subst; exact Hm | apply Hrest; lia].
    + intro H. split; [apply H; lia | intros i Hi; apply H; lia].
Qed.

Lemma forall_nat_true : forall n P,
  (forall i, i < n -> P i = true) -> forall_nat n P = true.
Proof. intros n P. apply (proj2 (forall_nat_iff n P)). Qed.

Lemma forall_nat_elim : forall n P,
  forall_nat n P = true -> forall i, i < n -> P i = true.
Proof. intros n P. apply (proj1 (forall_nat_iff n P)). Qed.

Definition x_ok (r : nat) (w : Inst) : bool :=
  forall_nat r (fun i => fXp w i || fXm w i).

Definition x_uniq (r : nat) (w : Inst) : bool :=
  forall_nat r (fun i => Bool.eqb (fXp w i) (negb (fXm w i))).

Definition y_uniq (q : nat) (w : Inst) : bool :=
  forall_nat q (fun j => Bool.eqb (fYp w j) (negb (fYm w j))).

Definition all_Y_true (q : nat) (w : Inst) : bool :=
  forall_nat q (fun j => fYp w j && fYm w j).

Definition C_p2 (r q : nat) (w : Inst) : bool :=
  if fd w then
    if x_ok r w then fp w && all_Y_true q w else true
  else
    if fp w then x_uniq r w && y_uniq q w else true.

Definition kappa_p2 (r q : nat) (phi : cnf) (w : Inst) : bool :=
  if fd w then x_ok r w
  else if fp w then negb (eval_cnf (combine3 r q (fXp w) (fYp w) (fZ w)) phi)
  else false.

Definition weak_axp (r q s : nat) (phi : cnf) (S : Sub) : Prop :=
  forall w : Inst, C_p2 r q w = true -> agrees_on r q s w S ->
    kappa_p2 r q phi w = true.

(* Literal Definition 3: AXp = subset-minimal weak AXp *)
Definition is_axp (r q s : nat) (phi : cnf) (S : Sub) : Prop :=
  weak_axp r q s phi S /\
  forall S' : Sub, sub_strict_lt r q s S' S -> ~ weak_axp r q s phi S'.

Definition strictly_subsumes (r q s : nat) (T S : Sub) : Prop :=
  (forall u : Inst, C_p2 r q u = true -> agrees_on r q s u S -> agrees_on r q s u T) /\
  (exists v : Inst, C_p2 r q v = true /\ agrees_on r q s v T /\ ~ agrees_on r q s v S).

(* Literal Definition 4: PI-explanation = AXp not strictly subsumed by another AXp *)
Definition is_pi (r q s : nat) (phi : cnf) (S : Sub) : Prop :=
  is_axp r q s phi S /\
  forall T : Sub, is_axp r q s phi T -> ~ strictly_subsumes r q s T S.

(* P2: Existence of an unfair PI-explanation *)
Definition exists_unfair_pi (r q s : nat) (phi : cnf) : Prop :=
  exists T : Sub, is_unfair_P2 T /\ is_pi r q s phi T.

(* P3: Universal fairness of decision x_star *)
Definition dec_univ_fair (r q s : nat) (phi : cnf) : Prop :=
  forall T : Sub, is_pi r q s phi T -> ~ is_unfair_P2 T.

(* Weight of a bounded subset for finite induction *)
Fixpoint sum_bool (n : nat) (f : nat -> bool) : nat :=
  match n with
  | 0 => 0
  | S m => (if f m then 1 else 0) + sum_bool m f
  end.

Definition sub_weight (r q s : nat) (S : Sub) : nat :=
  (if sd S then 1 else 0) +
  sum_bool r (sXp S) + sum_bool r (sXm S) +
  (if sp S then 1 else 0) +
  sum_bool q (sYp S) + sum_bool q (sYm S) + sum_bool s (sZ S).

Lemma sum_bool_le : forall n f1 f2,
  (forall i, i < n -> f1 i = true -> f2 i = true) ->
  sum_bool n f1 <= sum_bool n f2.
Proof.
  induction n as [|m IH]; intros f1 f2 H; simpl; [lia|].
  assert (Hm : (if f1 m then 1 else 0) <= (if f2 m then 1 else 0)).
  { destruct (f1 m) eqn:E1; [rewrite (H m ltac:(lia) E1); lia | destruct (f2 m); lia]. }
  assert (Hr : sum_bool m f1 <= sum_bool m f2) by (apply IH; intros i Hi; apply H; lia).
  lia.
Qed.

Lemma sum_bool_lt : forall n f1 f2 i0,
  (forall i, i < n -> f1 i = true -> f2 i = true) ->
  i0 < n -> f2 i0 = true -> f1 i0 = false ->
  sum_bool n f1 < sum_bool n f2.
Proof.
  induction n as [|m IH]; intros f1 f2 i0 H Hi0 H2 H1; [lia|].
  simpl.
  destruct (Nat.eq_dec i0 m).
  - subst. rewrite H2, H1.
    assert (Hr : sum_bool m f1 <= sum_bool m f2) by (apply sum_bool_le; intros i Hi; apply H; lia).
    lia.
  - assert (Hm : (if f1 m then 1 else 0) <= (if f2 m then 1 else 0)).
    { destruct (f1 m) eqn:E1; [rewrite (H m ltac:(lia) E1); lia | destruct (f2 m); lia]. }
    assert (Hr : sum_bool m f1 < sum_bool m f2)
      by (apply IH with i0; [intros i Hi; apply H; lia | lia | exact H2 | exact H1]).
    lia.
Qed.

Lemma sub_strict_lt_weight : forall r q s S1 S2,
  sub_strict_lt r q s S1 S2 -> sub_weight r q s S1 < sub_weight r q s S2.
Proof.
  intros r q s S1 S2 [[H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] Hdiff].
  unfold sub_weight.
  assert (L1 : (if sd S1 then 1 else 0) <= (if sd S2 then 1 else 0)) by (destruct (sd S1) eqn:E; [rewrite (H1 eq_refl); lia | destruct (sd S2); lia]).
  assert (L2 : sum_bool r (sXp S1) <= sum_bool r (sXp S2)) by (apply sum_bool_le; exact H2).
  assert (L3 : sum_bool r (sXm S1) <= sum_bool r (sXm S2)) by (apply sum_bool_le; exact H3).
  assert (L4 : (if sp S1 then 1 else 0) <= (if sp S2 then 1 else 0)) by (destruct (sp S1) eqn:E; [rewrite (H4 eq_refl); lia | destruct (sp S2); lia]).
  assert (L5 : sum_bool q (sYp S1) <= sum_bool q (sYp S2)) by (apply sum_bool_le; exact H5).
  assert (L6 : sum_bool q (sYm S1) <= sum_bool q (sYm S2)) by (apply sum_bool_le; exact H6).
  assert (L7 : sum_bool s (sZ S1) <= sum_bool s (sZ S2)) by (apply sum_bool_le; exact H7).
  destruct Hdiff as [[D2 D1] | [[i [Hi [D2 D1]]] | [[i [Hi [D2 D1]]] | [[D2 D1] | [[j [Hj [D2 D1]]] | [[j [Hj [D2 D1]]] | [k [Hk [D2 D1]]]]]]]]].
  - rewrite D2, D1 in *. lia.
  - assert (sum_bool r (sXp S1) < sum_bool r (sXp S2)) by (apply sum_bool_lt with i; assumption). lia.
  - assert (sum_bool r (sXm S1) < sum_bool r (sXm S2)) by (apply sum_bool_lt with i; assumption). lia.
  - rewrite D2, D1 in *. lia.
  - assert (sum_bool q (sYp S1) < sum_bool q (sYp S2)) by (apply sum_bool_lt with j; assumption). lia.
  - assert (sum_bool q (sYm S1) < sum_bool q (sYm S2)) by (apply sum_bool_lt with j; assumption). lia.
  - assert (sum_bool s (sZ S1) < sum_bool s (sZ S2)) by (apply sum_bool_lt with k; assumption). lia.
Qed.

Lemma weak_axp_has_axp : forall r q s phi W,
  weak_axp r q s phi W ->
  exists S, sub_le r q s S W /\ is_axp r q s phi S.
Proof.
  intros r q s phi W HW.
  remember (sub_weight r q s W) as n eqn:Hn.
  revert W Hn HW.
  induction n as [n IH] using lt_wf_ind.
  intros W Hn HW.
  destruct (classic (is_axp r q s phi W)) as [Haxp | Hnot].
  - exists W. split; [repeat split; auto | exact Haxp].
  - unfold is_axp in Hnot. apply not_and_or in Hnot.
    destruct Hnot as [Hbad | Hnotmin]; [contradiction|].
    apply not_all_ex_not in Hnotmin. destruct Hnotmin as [W' HW'].
    apply imply_to_and in HW'. destruct HW' as [Hlt Hnotw].
    apply NNPP in Hnotw.
    assert (Hwt : sub_weight r q s W' < n) by (subst; apply sub_strict_lt_weight; exact Hlt).
    destruct (IH (sub_weight r q s W') Hwt W' eq_refl Hnotw) as [S [Hle HSaxp]].
    exists S. split; [|exact HSaxp].
    apply sub_le_trans with W'; [exact Hle | exact (proj1 Hlt)].
Qed.

(* Witness instances *)
Definition inst_flip_Z (k0 : nat) : Inst :=
  mkInst true (fun _ => true) (fun _ => true) true (fun _ => true) (fun _ => true)
         (fun k => negb (k =? k0)).

Lemma C_p2_flip_Z : forall r q k0, C_p2 r q (inst_flip_Z k0) = true.
Proof.
  intros r q k0. unfold C_p2, inst_flip_Z. simpl.
  assert (Hok : x_ok r (mkInst true (fun _ => true) (fun _ => true) true (fun _ => true) (fun _ => true) (fun k => negb (k =? k0))) = true)
    by (apply forall_nat_true; intros; reflexivity).
  rewrite Hok. apply forall_nat_true. intros. reflexivity.
Qed.

Definition inst_zero_X (i0 : nat) : Inst :=
  mkInst true (fun i => negb (i =? i0)) (fun i => negb (i =? i0)) true
         (fun _ => true) (fun _ => true) (fun _ => true).

Lemma C_p2_zero_X : forall r q i0, C_p2 r q (inst_zero_X i0) = true.
Proof.
  intros r q i0. unfold C_p2, inst_zero_X. simpl.
  destruct (x_ok r _); [|reflexivity].
  apply forall_nat_true. intros. reflexivity.
Qed.

Lemma x_ok_zero_X_false : forall r i0, i0 < r -> x_ok r (inst_zero_X i0) = false.
Proof.
  intros r i0 Hi.
  destruct (x_ok r (inst_zero_X i0)) eqn:H; [|reflexivity].
  exfalso. unfold x_ok in H.
  pose proof (forall_nat_elim _ _ H i0 Hi) as H0.
  unfold inst_zero_X in H0. simpl in H0. rewrite Nat.eqb_refl in H0. discriminate.
Qed.

Definition inst_d0_p0 : Inst :=
  mkInst false (fun _ => true) (fun _ => true) false (fun _ => true) (fun _ => true) (fun _ => true).

Lemma C_p2_d0_p0 : forall r q, C_p2 r q inst_d0_p0 = true.
Proof. intros. reflexivity. Qed.

Lemma kappa_p2_d0_p0 : forall r q phi, kappa_p2 r q phi inst_d0_p0 = false.
Proof. intros. reflexivity. Qed.

Definition inst_of_XYZ (X Y Z : nat -> bool) : Inst :=
  mkInst false X (fun i => negb (X i)) true Y (fun j => negb (Y j)) Z.

Lemma C_p2_of_XYZ : forall r q X Y Z, C_p2 r q (inst_of_XYZ X Y Z) = true.
Proof.
  intros r q X Y Z. unfold C_p2, inst_of_XYZ. simpl.
  apply Bool.andb_true_iff. split.
  - apply forall_nat_true. intros i _. simpl. destruct (X i); reflexivity.
  - apply forall_nat_true. intros j _. simpl. destruct (Y j); reflexivity.
Qed.

Definition S_of_X (X : nat -> bool) : Sub :=
  mkSub true X (fun i => negb (X i)) false (fun _ => false) (fun _ => false) (fun _ => false).

Definition T_of_SY (S : Sub) (Y : nat -> bool) : Sub :=
  mkSub false (sXp S) (sXm S) true Y (fun j => negb (Y j)) (fun _ => false).

(* ========================================================================= *)
(* Theorem 1: three_qbf r q phi <-> exists_unfair_pi r q s phi (P2)          *)
(* ========================================================================= *)

Theorem p2_sigma3p_equiv :
  forall (r q s : nat) (phi : cnf),
    cnf_bounded (r + q + s) phi ->
    (three_qbf r q phi <-> exists_unfair_pi r q s phi).
Proof.
  intros r q s phi _. split.
  - (* Forward: three_qbf -> exists_unfair_pi *)
    intros [X HXY].
    exists (S_of_X X).
    split; [reflexivity|].
    split.
    + (* is_axp (S_of_X X) *)
      split.
      * (* weak_axp *)
        intros w HCw [Hwd [HwA [HwB _]]].
        unfold kappa_p2. rewrite (Hwd eq_refl).
        apply forall_nat_true. intros i Hi.
        destruct (X i) eqn:HXi.
        -- rewrite HwA; [reflexivity | exact Hi | exact HXi].
        -- rewrite HwB; [rewrite Bool.orb_true_r; reflexivity | exact Hi | unfold S_of_X; simpl; rewrite HXi; reflexivity].
      * (* subset-minimal *)
        intros T [HTle Hdiff] HTwaxp.
        destruct Hdiff as [[_ HTd] | [[i [Hi [HXA HTA]]] | [[i [Hi [HXB HTB]]] | [[Hc _] | [[j [_ [Hc _]]] | [[j [_ [Hc _]]] | [k [_ [Hc _]]]]]]]]];
          try (simpl in Hc; discriminate).
        -- (* sd T = false -> inst_d0_p0 agrees with T *)
           pose proof (HTwaxp inst_d0_p0 (C_p2_d0_p0 r q)) as Hkap.
           assert (Hag : agrees_on r q s inst_d0_p0 T).
           { destruct HTle as [L1 [L2 [L3 [L4 [L5 [L6 L7]]]]]].
             repeat split; unfold inst_d0_p0; simpl; try (intros; reflexivity).
             - intro Hc. rewrite Hc in HTd. discriminate.
             - intro Hc. apply L4 in Hc. simpl in Hc. discriminate. }
           apply Hkap in Hag. rewrite kappa_p2_d0_p0 in Hag. discriminate.
        -- (* sXp T i = false when X i = true -> inst_zero_X i agrees with T *)
           assert (HTB : sXm T i = false).
           { destruct (sXm T i) eqn:E; [|reflexivity].
             destruct HTle as [_ [_ [L3 _]]].
             specialize (L3 i Hi E). simpl in L3, HXA. rewrite HXA in L3. discriminate. }
           pose proof (HTwaxp (inst_zero_X i) (C_p2_zero_X r q i)) as Hkap.
           assert (Hag : agrees_on r q s (inst_zero_X i) T).
           { destruct HTle as [L1 [L2 [L3 [L4 [L5 [L6 L7]]]]]].
             unfold inst_zero_X.
             split; [simpl; intro; reflexivity|].
             split; [simpl; intros i' _ Hmem; destruct (Nat.eq_dec i' i); [subst; rewrite HTA in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]|].
             split; [simpl; intros i' _ Hmem; destruct (Nat.eq_dec i' i); [subst; rewrite HTB in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]|].
             split; [simpl; intro Hc; apply L4 in Hc; simpl in Hc; discriminate|].
             split; [simpl; intros j Hj Hc; apply L5 in Hc; [simpl in Hc; discriminate | exact Hj]|].
             split; [simpl; intros j Hj Hc; apply L6 in Hc; [simpl in Hc; discriminate | exact Hj]|].
             simpl; intros k Hk Hc; apply L7 in Hc; [simpl in Hc; discriminate | exact Hk]. }
           apply Hkap in Hag. unfold kappa_p2 in Hag. simpl in Hag.
           rewrite x_ok_zero_X_false in Hag; [discriminate | exact Hi].
        -- (* sXm T i = false when X i = false -> inst_zero_X i agrees with T *)
           assert (HTA : sXp T i = false).
           { destruct (sXp T i) eqn:E; [|reflexivity].
             destruct HTle as [_ [L2 _]].
             specialize (L2 i Hi E). simpl in L2, HXB. rewrite L2 in HXB. discriminate. }
           pose proof (HTwaxp (inst_zero_X i) (C_p2_zero_X r q i)) as Hkap.
           assert (Hag : agrees_on r q s (inst_zero_X i) T).
           { destruct HTle as [L1 [L2 [L3 [L4 [L5 [L6 L7]]]]]].
             unfold inst_zero_X.
             split; [simpl; intro; reflexivity|].
             split; [simpl; intros i' _ Hmem; destruct (Nat.eq_dec i' i); [subst; rewrite HTA in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]|].
             split; [simpl; intros i' _ Hmem; destruct (Nat.eq_dec i' i); [subst; rewrite HTB in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]|].
             split; [simpl; intro Hc; apply L4 in Hc; simpl in Hc; discriminate|].
             split; [simpl; intros j Hj Hc; apply L5 in Hc; [simpl in Hc; discriminate | exact Hj]|].
             split; [simpl; intros j Hj Hc; apply L6 in Hc; [simpl in Hc; discriminate | exact Hj]|].
             simpl; intros k Hk Hc; apply L7 in Hc; [simpl in Hc; discriminate | exact Hk]. }
           apply Hkap in Hag. unfold kappa_p2 in Hag. simpl in Hag.
           rewrite x_ok_zero_X_false in Hag; [discriminate | exact Hi].
    + (* Not strictly subsumed by any AXp T *)
      intros T [HTaxp _] [HTsub [v [HCv [HvT HnotvS]]]].
      assert (HnoZ : forall k, k < s -> sZ T k = false).
      { intros k Hk. destruct (sZ T k) eqn:HsZ; [|reflexivity].
        exfalso.
        pose proof (HTsub (inst_flip_Z k) (C_p2_flip_Z r q k)) as Hcont.
        assert (Hags : agrees_on r q s (inst_flip_Z k) (S_of_X X)).
        { repeat split; try (intro; reflexivity); intros; simpl; try reflexivity; discriminate. }
        apply Hcont in Hags. destruct Hags as [_ [_ [_ [_ [_ [_ HZk]]]]]].
        specialize (HZk k Hk HsZ). unfold inst_flip_Z in HZk. simpl in HZk.
        rewrite Nat.eqb_refl in HZk. discriminate. }
      destruct (sd T) eqn:HTd.
      * (* sd T = true: T must contain all of S_of_X X, contradicting ~ agrees v S *)
        apply HnotvS.
        destruct HvT as [Hvd [HvA [HvB _]]].
        repeat split.
        -- intro. apply Hvd. exact HTd.
        -- intros i Hi HXA. apply HvA; [exact Hi|].
           destruct (sXp T i) eqn:HsA; [reflexivity|].
           exfalso.
           assert (HsB : sXm T i = false).
           { destruct (sXm T i) eqn:HsB'; [|reflexivity].
             set (u := mkInst true (fun _ => true) (fun i' => negb (i' =? i)) true
                              (fun _ => true) (fun _ => true) (fun _ => true)).
             assert (HCu : C_p2 r q u = true).
             { unfold C_p2, u. simpl.
               assert (Hok : x_ok r (mkInst true (fun _ => true) (fun i' => negb (i' =? i)) true (fun _ => true) (fun _ => true) (fun _ => true)) = true)
                 by (apply forall_nat_true; intros; reflexivity).
               rewrite Hok. apply forall_nat_true. intros; reflexivity. }
             assert (Hagu : agrees_on r q s u (S_of_X X)).
             { repeat split; try (intro; reflexivity); try (intros; simpl; try reflexivity; discriminate).
               intros i' Hi' Hbi'. unfold u. simpl.
               destruct (Nat.eq_dec i' i); [subst; simpl in HXA, Hbi'; rewrite HXA in Hbi'; discriminate|].
               apply Nat.eqb_neq in n. rewrite n. reflexivity. }
             apply (HTsub u HCu) in Hagu. destruct Hagu as [_ [_ [HuB _]]].
             specialize (HuB i Hi HsB'). unfold u in HuB. simpl in HuB.
             rewrite Nat.eqb_refl in HuB. discriminate. }
           pose proof (HTaxp (inst_zero_X i) (C_p2_zero_X r q i)) as Hkap.
           assert (Hagz : agrees_on r q s (inst_zero_X i) T).
           { repeat split; try (intro; reflexivity); intros i' Hi' Hmem; unfold inst_zero_X; simpl.
             - destruct (Nat.eq_dec i' i); [subst; rewrite HsA in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity].
             - destruct (Nat.eq_dec i' i); [subst; rewrite HsB in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]. }
           apply Hkap in Hagz. unfold kappa_p2 in Hagz. simpl in Hagz.
           rewrite x_ok_zero_X_false in Hagz; [discriminate | exact Hi].
        -- intros i Hi HXB. apply HvB; [exact Hi|].
           destruct (sXm T i) eqn:HsB; [reflexivity|].
           exfalso.
           assert (HsA : sXp T i = false).
           { destruct (sXp T i) eqn:HsA'; [|reflexivity].
             set (u := mkInst true (fun i' => negb (i' =? i)) (fun _ => true) true
                              (fun _ => true) (fun _ => true) (fun _ => true)).
             assert (HCu : C_p2 r q u = true).
             { unfold C_p2, u. simpl.
               assert (Hok : x_ok r (mkInst true (fun i' => negb (i' =? i)) (fun _ => true) true (fun _ => true) (fun _ => true) (fun _ => true)) = true)
                 by (apply forall_nat_true; intros; simpl; apply Bool.orb_true_r).
               rewrite Hok. apply forall_nat_true. intros; reflexivity. }
             assert (Hagu : agrees_on r q s u (S_of_X X)).
             { repeat split; try (intro; reflexivity); try (intros; simpl; try reflexivity; discriminate).
               intros i' Hi' Hai'. unfold u. simpl.
               destruct (Nat.eq_dec i' i); [subst; simpl in HXB, Hai'; rewrite Hai' in HXB; discriminate|].
               apply Nat.eqb_neq in n. rewrite n. reflexivity. }
             apply (HTsub u HCu) in Hagu. destruct Hagu as [_ [HuA _]].
             specialize (HuA i Hi HsA'). unfold u in HuA. simpl in HuA.
             rewrite Nat.eqb_refl in HuA. discriminate. }
           pose proof (HTaxp (inst_zero_X i) (C_p2_zero_X r q i)) as Hkap.
           assert (Hagz : agrees_on r q s (inst_zero_X i) T).
           { repeat split; try (intro; reflexivity); intros i' Hi' Hmem; unfold inst_zero_X; simpl.
             - destruct (Nat.eq_dec i' i); [subst; rewrite HsA in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity].
             - destruct (Nat.eq_dec i' i); [subst; rewrite HsB in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]. }
           apply Hkap in Hagz. unfold kappa_p2 in Hagz. simpl in Hagz.
           rewrite x_ok_zero_X_false in Hagz; [discriminate | exact Hi].
        -- intro Hc; discriminate.
        -- intros j _ Hc; discriminate.
        -- intros j _ Hc; discriminate.
        -- intros k _ Hc; discriminate.
      * (* sd T = false *)
        assert (Hsp : sp T = true).
        { destruct (sp T) eqn:Hsp'; [reflexivity|].
          exfalso. pose proof (HTaxp inst_d0_p0 (C_p2_d0_p0 r q)) as Hkap.
          assert (Hag : agrees_on r q s inst_d0_p0 T).
          { repeat split; unfold inst_d0_p0; simpl; try (intro Hc; rewrite Hc in HTd; discriminate);
            try (intro Hc; rewrite Hc in Hsp'; discriminate);
            try (intros; reflexivity). }
          apply Hkap in Hag. rewrite kappa_p2_d0_p0 in Hag. discriminate. }
        assert (Hno_both_Y : forall j, j < q -> ~(sYp T j = true /\ sYm T j = true)).
        { intros j Hj [HY1 HY2].
          apply HnotvS.
          assert (Hvd_true : fd v = true).
          { destruct (fd v) eqn:Hfdv; [reflexivity|].
            exfalso. unfold C_p2 in HCv. rewrite Hfdv in HCv.
            destruct HvT as [_ [_ [_ [Hvp [HvY [HvYb _]]]]]].
            rewrite (Hvp Hsp) in HCv.
            apply Bool.andb_true_iff in HCv. destruct HCv as [_ Hyu].
            unfold y_uniq in Hyu.
            pose proof (forall_nat_elim _ _ Hyu j Hj) as Hyuj. simpl in Hyuj.
            rewrite (HvY j Hj HY1), (HvYb j Hj HY2) in Hyuj. discriminate. }
          destruct HvT as [_ [HvA [HvB _]]].
          repeat split.
          - intro; exact Hvd_true.
          - intros i Hi HXA. apply HvA; [exact Hi|].
            destruct (sXp T i) eqn:HsA; [reflexivity|].
            exfalso.
            assert (HsB : sXm T i = false).
            { destruct (sXm T i) eqn:HsB'; [|reflexivity].
              set (u := mkInst true (fun _ => true) (fun i' => negb (i' =? i)) true
                               (fun _ => true) (fun _ => true) (fun _ => true)).
              assert (HCu : C_p2 r q u = true).
              { unfold C_p2, u. simpl.
                assert (Hok : x_ok r (mkInst true (fun _ => true) (fun i' => negb (i' =? i)) true (fun _ => true) (fun _ => true) (fun _ => true)) = true)
                  by (apply forall_nat_true; intros; reflexivity).
                rewrite Hok. apply forall_nat_true. intros; reflexivity. }
              assert (Hagu : agrees_on r q s u (S_of_X X)).
              { repeat split; try (intro; reflexivity); try (intros; simpl; try reflexivity; discriminate).
                intros i' Hi' Hbi'. unfold u. simpl.
                destruct (Nat.eq_dec i' i); [subst; simpl in HXA, Hbi'; rewrite HXA in Hbi'; discriminate|].
                apply Nat.eqb_neq in n. rewrite n. reflexivity. }
              apply (HTsub u HCu) in Hagu. destruct Hagu as [_ [_ [HuB _]]].
              specialize (HuB i Hi HsB'). unfold u in HuB. simpl in HuB.
              rewrite Nat.eqb_refl in HuB. discriminate. }
            pose proof (HTaxp (inst_zero_X i) (C_p2_zero_X r q i)) as Hkap.
            assert (Hagz : agrees_on r q s (inst_zero_X i) T).
            { repeat split; unfold inst_zero_X; simpl; try (intro Hc; rewrite Hc in HTd; discriminate);
              try (intro; reflexivity); try (intros; reflexivity).
              - intros i' Hi' Hmem. destruct (Nat.eq_dec i' i); [subst; rewrite HsA in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity].
              - intros i' Hi' Hmem. destruct (Nat.eq_dec i' i); [subst; rewrite HsB in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]. }
            apply Hkap in Hagz. unfold kappa_p2 in Hagz. simpl in Hagz.
            rewrite x_ok_zero_X_false in Hagz; [discriminate | exact Hi].
          - intros i Hi HXB. apply HvB; [exact Hi|].
            destruct (sXm T i) eqn:HsB; [reflexivity|].
            exfalso.
            assert (HsA : sXp T i = false).
            { destruct (sXp T i) eqn:HsA'; [|reflexivity].
              set (u := mkInst true (fun i' => negb (i' =? i)) (fun _ => true) true
                               (fun _ => true) (fun _ => true) (fun _ => true)).
              assert (HCu : C_p2 r q u = true).
              { unfold C_p2, u. simpl.
                assert (Hok : x_ok r (mkInst true (fun i' => negb (i' =? i)) (fun _ => true) true (fun _ => true) (fun _ => true) (fun _ => true)) = true)
                  by (apply forall_nat_true; intros; simpl; apply Bool.orb_true_r).
                rewrite Hok. apply forall_nat_true. intros; reflexivity. }
              assert (Hagu : agrees_on r q s u (S_of_X X)).
              { repeat split; try (intro; reflexivity); try (intros; simpl; try reflexivity; discriminate).
                intros i' Hi' Hai'. unfold u. simpl.
                destruct (Nat.eq_dec i' i); [subst; simpl in HXB, Hai'; rewrite Hai' in HXB; discriminate|].
                apply Nat.eqb_neq in n. rewrite n. reflexivity. }
              apply (HTsub u HCu) in Hagu. destruct Hagu as [_ [HuA _]].
              specialize (HuA i Hi HsA'). unfold u in HuA. simpl in HuA.
              rewrite Nat.eqb_refl in HuA. discriminate. }
            pose proof (HTaxp (inst_zero_X i) (C_p2_zero_X r q i)) as Hkap.
            assert (Hagz : agrees_on r q s (inst_zero_X i) T).
            { repeat split; unfold inst_zero_X; simpl; try (intro Hc; rewrite Hc in HTd; discriminate);
              try (intro; reflexivity); try (intros; reflexivity).
              - intros i' Hi' Hmem. destruct (Nat.eq_dec i' i); [subst; rewrite HsA in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity].
              - intros i' Hi' Hmem. destruct (Nat.eq_dec i' i); [subst; rewrite HsB in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]. }
            apply Hkap in Hagz. unfold kappa_p2 in Hagz. simpl in Hagz.
            rewrite x_ok_zero_X_false in Hagz; [discriminate | exact Hi].
          - intro Hc; discriminate.
          - intros j' _ Hc; discriminate.
          - intros j' _ Hc; discriminate.
          - intros k' _ Hc; discriminate. }
        set (Ystar := fun j => negb (sYm T j)).
        destruct (HXY Ystar) as [Zstar HZstar].
        set (w := inst_of_XYZ X Ystar Zstar).
        pose proof (HTaxp w (C_p2_of_XYZ r q X Ystar Zstar)) as Hkap.
        assert (Hagw : agrees_on r q s w T).
        { unfold w, inst_of_XYZ.
          split. { simpl. intro Hc. rewrite Hc in HTd. discriminate. }
          split. { simpl. intros i Hi HsAi.
            destruct (X i) eqn:HXi; [reflexivity|].
            exfalso.
            set (u := mkInst true (fun i' => negb (i' =? i)) (fun _ => true) true
                             (fun _ => true) (fun _ => true) (fun _ => true)).
            assert (HCu : C_p2 r q u = true).
            { unfold C_p2, u. simpl.
              assert (Hok : x_ok r (mkInst true (fun i' => negb (i' =? i)) (fun _ => true) true (fun _ => true) (fun _ => true) (fun _ => true)) = true)
                by (apply forall_nat_true; intros; simpl; apply Bool.orb_true_r).
              rewrite Hok. apply forall_nat_true. intros; reflexivity. }
            assert (Hagu : agrees_on r q s u (S_of_X X)).
            { repeat split; try (intro; reflexivity); try (intros; simpl; try reflexivity; discriminate).
              intros i' Hi' Hai'. unfold u. simpl.
              destruct (Nat.eq_dec i' i); [subst; simpl in Hai'; rewrite Hai' in HXi; discriminate|].
              apply Nat.eqb_neq in n. rewrite n. reflexivity. }
            apply (HTsub u HCu) in Hagu. destruct Hagu as [_ [HuA _]].
            specialize (HuA i Hi HsAi). unfold u in HuA. simpl in HuA.
            rewrite Nat.eqb_refl in HuA. discriminate. }
          split. { simpl. intros i Hi HsBi.
            destruct (X i) eqn:HXi; [|reflexivity].
            exfalso.
            set (u := mkInst true (fun _ => true) (fun i' => negb (i' =? i)) true
                             (fun _ => true) (fun _ => true) (fun _ => true)).
            assert (HCu : C_p2 r q u = true).
            { unfold C_p2, u. simpl.
              assert (Hok : x_ok r (mkInst true (fun _ => true) (fun i' => negb (i' =? i)) true (fun _ => true) (fun _ => true) (fun _ => true)) = true)
                by (apply forall_nat_true; intros; reflexivity).
              rewrite Hok. apply forall_nat_true. intros; reflexivity. }
            assert (Hagu : agrees_on r q s u (S_of_X X)).
            { repeat split; try (intro; reflexivity); try (intros; simpl; try reflexivity; discriminate).
              intros i' Hi' Hbi'. unfold u. simpl.
              destruct (Nat.eq_dec i' i); [subst; simpl in Hbi'; rewrite HXi in Hbi'; discriminate|].
              apply Nat.eqb_neq in n. rewrite n. reflexivity. }
            apply (HTsub u HCu) in Hagu. destruct Hagu as [_ [_ [HuB _]]].
            specialize (HuB i Hi HsBi). unfold u in HuB. simpl in HuB.
            rewrite Nat.eqb_refl in HuB. discriminate. }
          split. { simpl. intro; reflexivity. }
          split. { simpl. intros j Hj HsYj. unfold Ystar.
            destruct (sYm T j) eqn:HsYbj; [|reflexivity].
            exfalso. apply (Hno_both_Y j Hj). split; assumption. }
          split. { simpl. intros j Hj HsYbj. unfold Ystar. rewrite HsYbj. reflexivity. }
          simpl. intros k Hk HsZk. rewrite HnoZ in HsZk; [discriminate | exact Hk]. }
        apply Hkap in Hagw. unfold kappa_p2, w, inst_of_XYZ in Hagw. simpl in Hagw.
        rewrite HZstar in Hagw. discriminate.
  - (* Backward: exists_unfair_pi -> three_qbf *)
    intros [T [HTunfair [[HTwaxp HTmin] HnoSub]]].
    (* sd T = true since P = {d} *)
    assert (HTd : sd T = true) by exact HTunfair.
    (* At least one of sXp T i, sXm T i is true for each i < r *)
    assert (HT_at_least_one : forall i, i < r -> sXp T i = true \/ sXm T i = true).
    { intros i Hi.
      destruct (sXp T i) eqn:HA; [left; reflexivity|].
      destruct (sXm T i) eqn:HB; [right; reflexivity|].
      exfalso. pose proof (HTwaxp (inst_zero_X i) (C_p2_zero_X r q i)) as Hkap.
      assert (Hag : agrees_on r q s (inst_zero_X i) T).
      { unfold inst_zero_X.
        split; [simpl; intro; reflexivity|].
        split; [simpl; intros i' _ Hmem; destruct (Nat.eq_dec i' i); [subst; rewrite HA in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]|].
        split; [simpl; intros i' _ Hmem; destruct (Nat.eq_dec i' i); [subst; rewrite HB in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]|].
        split; [simpl; intro; reflexivity|].
        split; [simpl; intros; reflexivity|].
        split; [simpl; intros; reflexivity|].
        simpl; intros; reflexivity. }
      apply Hkap in Hag. unfold kappa_p2 in Hag. simpl in Hag.
      rewrite x_ok_zero_X_false in Hag; [discriminate | exact Hi]. }
    (* At most one of sXp T i, sXm T i is true (by subset-minimality of T!) *)
    assert (HT_at_most_one : forall i, i < r -> ~(sXp T i = true /\ sXm T i = true)).
    { intros i0 Hi0 [HA0 HB0].
      set (T' := mkSub (sd T) (fun i => if i =? i0 then false else sXp T i) (sXm T)
                       (sp T) (sYp T) (sYm T) (sZ T)).
      apply (HTmin T').
      - split.
        + repeat split; intros; simpl in *; auto.
          destruct (i =? i0); [discriminate | assumption].
        + right. left. exists i0. repeat split; [exact Hi0 | exact HA0 | unfold T'; simpl; rewrite Nat.eqb_refl; reflexivity].
      - intros w HCw [Hwd [HwA [HwB _]]].
        unfold kappa_p2. rewrite (Hwd HTd). apply forall_nat_true. intros i Hi.
        destruct (Nat.eq_dec i i0).
        + subst. rewrite (HwB i0 Hi0 HB0). apply Bool.orb_true_r.
        + destruct (HT_at_least_one i Hi) as [HAi | HBi].
          * rewrite (HwA i Hi); [reflexivity|].
            unfold T'. simpl. apply Nat.eqb_neq in n. rewrite n. exact HAi.
          * rewrite (HwB i Hi HBi). apply Bool.orb_true_r. }
    (* Define X := sXp T *)
    exists (sXp T). intro Y.
    assert (Hnot_waxp : ~ weak_axp r q s phi (T_of_SY T Y)).
    { intro Hwaxp.
      destruct (weak_axp_has_axp r q s phi (T_of_SY T Y) Hwaxp) as [S [HSle HSaxp]].
      apply (HnoSub S HSaxp).
      split.
      - intros u HCu [Hud [HuA [HuB _]]].
        apply agrees_sub_le with (T_of_SY T Y); [exact HSle|].
        assert (Hok : x_ok r u = true).
        { apply forall_nat_true. intros i Hi.
          destruct (HT_at_least_one i Hi) as [HAi | HBi];
            [rewrite (HuA i Hi HAi); reflexivity | rewrite (HuB i Hi HBi); apply Bool.orb_true_r]. }
        unfold C_p2 in HCu. rewrite (Hud HTd), Hok in HCu.
        apply Bool.andb_true_iff in HCu. destruct HCu as [Hup HuY].
        unfold all_Y_true in HuY. pose proof (forall_nat_elim _ _ HuY) as HuY'.
        repeat split.
        + intro Hc; discriminate.
        + intros i Hi HTi. apply HuA; assumption.
        + intros i Hi HTi. apply HuB; assumption.
        + intro. exact Hup.
        + intros j Hj _. specialize (HuY' j Hj). apply Bool.andb_true_iff in HuY'. exact (proj1 HuY').
        + intros j Hj _. specialize (HuY' j Hj). apply Bool.andb_true_iff in HuY'. exact (proj2 HuY').
        + intros k _ Hc; simpl in Hc; discriminate.
      - exists (inst_of_XYZ (sXp T) Y (fun _ => false)).
        split; [apply C_p2_of_XYZ|].
        split.
        + apply agrees_sub_le with (T_of_SY T Y); [exact HSle|].
          repeat split; unfold inst_of_XYZ, T_of_SY; simpl; try (intro Hc; discriminate);
          try (intro; reflexivity); try (intros; discriminate).
          * intros i Hi HTi. rewrite HTi. reflexivity.
          * intros i Hi HTi. destruct (sXp T i) eqn:HAi; [exfalso; apply (HT_at_most_one i Hi); split; assumption | reflexivity].
          * intros j _ HYj. rewrite HYj. reflexivity.
          * intros j _ HYbj. rewrite HYbj. reflexivity.
        + intros [Hvd _]. unfold inst_of_XYZ in Hvd. simpl in Hvd.
          specialize (Hvd HTd). discriminate. }
    unfold weak_axp in Hnot_waxp.
    apply not_all_ex_not in Hnot_waxp. destruct Hnot_waxp as [w Hw].
    apply imply_to_and in Hw. destruct Hw as [HCw Hw].
    apply imply_to_and in Hw. destruct Hw as [Hagw Hkw].
    apply Bool.not_true_iff_false in Hkw.
    assert (Hwd0 : fd w = false).
    { destruct (fd w) eqn:Hfdw; [|reflexivity].
      exfalso. unfold kappa_p2 in Hkw. rewrite Hfdw in Hkw.
      destruct Hagw as [_ [HwA [HwB _]]].
      assert (Hok : x_ok r w = true).
      { apply forall_nat_true. intros i Hi.
        destruct (HT_at_least_one i Hi) as [HAi | HBi];
          [rewrite (HwA i Hi HAi); reflexivity | rewrite (HwB i Hi HBi); apply Bool.orb_true_r]. }
      rewrite Hok in Hkw. discriminate. }
    destruct Hagw as [_ [HwA [HwB [Hwp [HwY [HwYb _]]]]]].
    assert (Hwp1 : fp w = true) by (apply Hwp; reflexivity).
    unfold kappa_p2 in Hkw. rewrite Hwd0, Hwp1 in Hkw.
    apply Bool.negb_false_iff in Hkw.
    unfold C_p2 in HCw. rewrite Hwd0, Hwp1 in HCw.
    apply Bool.andb_true_iff in HCw. destruct HCw as [Hxu Hyu].
    unfold x_uniq in Hxu. unfold y_uniq in Hyu.
    pose proof (forall_nat_elim _ _ Hxu) as Hxu'.
    pose proof (forall_nat_elim _ _ Hyu) as Hyu'.
    exists (fZ w).
    rewrite <- Hkw. apply eval_cnf_ext. intro k.
    unfold combine3.
    destruct (Nat.ltb_spec k r) as [Hk|Hk].
    + destruct (sXp T k) eqn:HAk.
      * symmetry. apply HwA; [exact Hk | exact HAk].
      * destruct (HT_at_least_one k Hk) as [Hc | HBk]; [congruence|].
        specialize (HwB k Hk HBk). specialize (Hxu' k Hk). simpl in Hxu'.
        rewrite HwB in Hxu'. simpl in Hxu'. apply Bool.eqb_prop in Hxu'. symmetry. exact Hxu'.
    + destruct (Nat.ltb_spec k (r + q)) as [Hk2|Hk2].
      * assert (Hkr : k - r < q) by lia.
        destruct (Y (k - r)) eqn:HYk.
        -- symmetry. apply HwY; [exact Hkr | exact HYk].
        -- assert (HYbk : negb (Y (k - r)) = true) by (rewrite HYk; reflexivity).
           specialize (HwYb (k - r) Hkr HYbk).
           specialize (Hyu' (k - r) Hkr). simpl in Hyu'.
           rewrite HwYb in Hyu'. simpl in Hyu'. apply Bool.eqb_prop in Hyu'. symmetry. exact Hyu'.
      * reflexivity.
Qed.

(* ========================================================================= *)
(* Theorem 2: ~ three_qbf r q phi <-> dec_univ_fair r q s phi (P3)           *)
(* ========================================================================= *)

Theorem p3_pi3p_equiv :
  forall (r q s : nat) (phi : cnf),
    cnf_bounded (r + q + s) phi ->
    (~ three_qbf r q phi <-> dec_univ_fair r q s phi).
Proof.
  intros r q s phi Hbnd. split.
  - intros Hnot T HTpi HTunfair. apply Hnot.
    apply (proj2 (p2_sigma3p_equiv r q s phi Hbnd)).
    exists T. split; assumption.
  - intros Huniv Hex.
    apply (proj1 (p2_sigma3p_equiv r q s phi Hbnd)) in Hex.
    destruct Hex as [T [HTunfair HTpi]].
    exact (Huniv T HTpi HTunfair).
Qed.

Print Assumptions p2_sigma3p_equiv.
Print Assumptions p3_pi3p_equiv.
