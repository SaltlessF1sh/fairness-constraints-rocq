From Stdlib Require Import Bool List Arith Lia Classical.
Import ListNotations.

(* ========================================================================= *)
(* Formal Verification in Rocq (Coq) of the 3-QBF <-> Decision Existential   *)
(* Fairness Reduction (Sigma_3^P-completeness of P1, closing the Open        *)
(* Question on p. 12 / Proposition 27 of Cooper & Bousdira, CP 2026).        *)
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

(* Standard 3-QBF: exists X, forall Y, exists Z, Phi(X, Y, Z) = true *)
Definition three_qbf (r q : nat) (phi : cnf) : Prop :=
  exists X : nat -> bool, forall Y : nat -> bool, exists Z : nat -> bool,
    eval_cnf (combine3 r q X Y Z) phi = true.

(* Feature space for reduction *)
Record Inst := mkInst {
  fd : bool;
  fXp : nat -> bool;
  fXm : nat -> bool;
  fp : bool;
  fYp : nat -> bool;
  fYm : nat -> bool;
  fZ : nat -> bool
}.

(* Subset of F = N \cup P *)
Record Sub := mkSub {
  sd : bool;
  sXp : nat -> bool;
  sXm : nat -> bool;
  sp : bool;
  sYp : nat -> bool;
  sYm : nat -> bool;
  sZ : nat -> bool
}.

Definition is_fair (S : Sub) : Prop :=
  sp S = false /\
  (forall j, sYp S j = false) /\
  (forall j, sYm S j = false) /\
  (forall k, sZ S k = false).

Definition is_unfair (T : Sub) : Prop :=
  sp T = true \/
  (exists j, sYp T j = true) \/
  (exists j, sYm T j = true) \/
  (exists k, sZ T k = true).

(* Target instance x^* = all true *)
Definition x_star : Inst :=
  mkInst true (fun _ => true) (fun _ => true) true (fun _ => true) (fun _ => true) (fun _ => true).

(* Agreement of w with x_star on subset S (bounded by r, q, s) *)
Definition agrees_on (r q s : nat) (w : Inst) (S : Sub) : Prop :=
  (sd S = true -> fd w = true) /\
  (forall i, i < r -> sXp S i = true -> fXp w i = true) /\
  (forall i, i < r -> sXm S i = true -> fXm w i = true) /\
  (sp S = true -> fp w = true) /\
  (forall j, j < q -> sYp S j = true -> fYp w j = true) /\
  (forall j, j < q -> sYm S j = true -> fYm w j = true) /\
  (forall k, k < s -> sZ S k = true -> fZ w k = true).

(* Helper checks on finite prefixes *)
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

(* Constraint C_p1 *)
Definition C_p1 (r q : nat) (w : Inst) : bool :=
  if fd w then
    if x_ok r w then fp w && all_Y_true q w else true
  else
    if fp w then x_uniq r w && y_uniq q w else true.

(* Classifier kappa_p1 *)
Definition kappa_p1 (r q : nat) (phi : cnf) (w : Inst) : bool :=
  if fd w then x_ok r w
  else if fp w then negb (eval_cnf (combine3 r q (fXp w) (fYp w) (fZ w)) phi)
  else false.

Definition weak_axp (r q s : nat) (phi : cnf) (S : Sub) : Prop :=
  forall w : Inst, C_p1 r q w = true -> agrees_on r q s w S ->
    kappa_p1 r q phi w = true.

Definition strictly_subsumes (r q s : nat) (T S : Sub) : Prop :=
  (forall u : Inst, C_p1 r q u = true -> agrees_on r q s u S -> agrees_on r q s u T) /\
  (exists v : Inst, C_p1 r q v = true /\ agrees_on r q s v T /\ ~ agrees_on r q s v S).

(* Decision existential fairness at x_star (where kappa_p1(x_star) = true):
   Exists fair weak AXp S not strictly subsumed by any unfair weak AXp T *)
Definition dec_exist_fair (r q s : nat) (phi : cnf) : Prop :=
  exists S : Sub,
    is_fair S /\
    weak_axp r q s phi S /\
    forall T : Sub, is_unfair T -> weak_axp r q s phi T ->
      ~ strictly_subsumes r q s T S.

(* Literal Definition 5: Fair PI-explanation existence (bounded finite feature domain) *)
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

Definition is_axp (r q s : nat) (phi : cnf) (S : Sub) : Prop :=
  weak_axp r q s phi S /\
  forall S' : Sub, sub_strict_lt r q s S' S -> ~ weak_axp r q s phi S'.

Definition is_pi (r q s : nat) (phi : cnf) (S : Sub) : Prop :=
  is_axp r q s phi S /\
  forall T : Sub, is_axp r q s phi T -> ~ strictly_subsumes r q s T S.

Definition is_fair_bounded (q s : nat) (S : Sub) : Prop :=
  sp S = false /\
  (forall j, j < q -> sYp S j = false) /\
  (forall j, j < q -> sYm S j = false) /\
  (forall k, k < s -> sZ S k = false).

Definition is_unfair_bounded (q s : nat) (T : Sub) : Prop :=
  sp T = true \/
  (exists j, j < q /\ sYp T j = true) \/
  (exists j, j < q /\ sYm T j = true) \/
  (exists k, k < s /\ sZ T k = true).

Definition dec_exist_fair_b (r q s : nat) (phi : cnf) : Prop :=
  exists S : Sub,
    is_fair S /\
    weak_axp r q s phi S /\
    forall T : Sub, is_unfair_bounded q s T -> weak_axp r q s phi T ->
      ~ strictly_subsumes r q s T S.

Definition dec_exist_fair_pi (r q s : nat) (phi : cnf) : Prop :=
  exists S : Sub,
    is_fair_bounded q s S /\
    is_pi r q s phi S.

Definition cnf_bounded (n : nat) (phi : cnf) : Prop :=
  forall c, In c phi -> forall l, In l c -> fst l < n.

Lemma C_p1_x_star : forall r q, C_p1 r q x_star = true.
Proof.
  intros r q. unfold C_p1, x_star. simpl.
  destruct (x_ok r _) eqn:Hok; [|reflexivity].
  apply forall_nat_true. intros j _. reflexivity.
Qed.

Lemma kappa_p1_x_star : forall r q phi, kappa_p1 r q phi x_star = true.
Proof.
  intros r q phi. unfold kappa_p1, x_star. simpl.
  apply forall_nat_true. intros i _. reflexivity.
Qed.

(* Helper: witness flipping Z_k = false while all else = true *)
Definition inst_flip_Z (k0 : nat) : Inst :=
  mkInst true (fun _ => true) (fun _ => true) true (fun _ => true) (fun _ => true)
         (fun k => negb (k =? k0)).

Lemma C_p1_flip_Z : forall r q k0, C_p1 r q (inst_flip_Z k0) = true.
Proof.
  intros r q k0. unfold C_p1, inst_flip_Z. simpl.
  assert (Hok : x_ok r (mkInst true (fun _ => true) (fun _ => true) true (fun _ => true) (fun _ => true) (fun k => negb (k =? k0))) = true)
    by (apply forall_nat_true; intros; reflexivity).
  rewrite Hok. apply forall_nat_true. intros. reflexivity.
Qed.

(* Helper: witness setting a_i0 = b_i0 = false while d=true, all else = true *)
Definition inst_zero_X (i0 : nat) : Inst :=
  mkInst true (fun i => negb (i =? i0)) (fun i => negb (i =? i0)) true
         (fun _ => true) (fun _ => true) (fun _ => true).

Lemma C_p1_zero_X : forall r q i0, C_p1 r q (inst_zero_X i0) = true.
Proof.
  intros r q i0. unfold C_p1, inst_zero_X. simpl.
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

(* Helper: witness for d=false, p=false, all else = true *)
Definition inst_d0_p0 : Inst :=
  mkInst false (fun _ => true) (fun _ => true) false (fun _ => true) (fun _ => true) (fun _ => true).

Lemma C_p1_d0_p0 : forall r q, C_p1 r q inst_d0_p0 = true.
Proof. intros. reflexivity. Qed.

Lemma kappa_p1_d0_p0 : forall r q phi, kappa_p1 r q phi inst_d0_p0 = false.
Proof. intros. reflexivity. Qed.

(* Encode X into fair S *)
Definition S_of_X (X : nat -> bool) : Sub :=
  mkSub true X (fun i => negb (X i)) false (fun _ => false) (fun _ => false) (fun _ => false).

(* Encode X, Y into valid d=false, p=true instance *)
Definition inst_of_XYZ (X Y Z : nat -> bool) : Inst :=
  mkInst false X (fun i => negb (X i)) true Y (fun j => negb (Y j)) Z.

Lemma C_p1_of_XYZ : forall r q X Y Z, C_p1 r q (inst_of_XYZ X Y Z) = true.
Proof.
  intros r q X Y Z. unfold C_p1, inst_of_XYZ. simpl.
  apply Bool.andb_true_iff. split.
  - apply forall_nat_true. intros i _. simpl. destruct (X i); reflexivity.
  - apply forall_nat_true. intros j _. simpl. destruct (Y j); reflexivity.
Qed.

(* Encode Y into T_Y given S *)
Definition T_of_SY (S : Sub) (Y : nat -> bool) : Sub :=
  mkSub false (sXp S) (sXm S) true Y (fun j => negb (Y j)) (fun _ => false).

Theorem p1_sigma3p_equiv :
  forall (r q s : nat) (phi : cnf),
    three_qbf r q phi <-> dec_exist_fair_b r q s phi.
Proof.
  intros r q s phi. split.
  - (* Forward: three_qbf -> dec_exist_fair_b *)
    intros [X HXY].
    exists (S_of_X X).
    split; [unfold is_fair; repeat split; reflexivity|].
    split.
    + (* weak_axp *)
      intros w HCw [Hwd [HwA [HwB _]]].
      unfold kappa_p1. rewrite (Hwd eq_refl).
      apply forall_nat_true. intros i Hi.
      destruct (X i) eqn:HXi.
      * rewrite HwA; [reflexivity | exact Hi | exact HXi].
      * rewrite HwB; [rewrite Bool.orb_true_r; reflexivity | exact Hi | unfold S_of_X; simpl; rewrite HXi; reflexivity].
    + (* No unfair T strictly subsumes S *)
      intros T HTunfair HTaxp [HTsub [v [HCv [HvT HnotvS]]]].
      (* 1. T cannot contain any Z_k (k < s) *)
      assert (HnoZ : forall k, k < s -> sZ T k = false).
      { intros k Hk. destruct (sZ T k) eqn:HsZ; [|reflexivity].
        exfalso.
        pose proof (HTsub (inst_flip_Z k) (C_p1_flip_Z r q k)) as Hcont.
        assert (Hags : agrees_on r q s (inst_flip_Z k) (S_of_X X)).
        { repeat split; try (intro; reflexivity); intros; simpl; try reflexivity; discriminate. }
        apply Hcont in Hags. destruct Hags as [_ [_ [_ [_ [_ [_ HZk]]]]]].
        specialize (HZk k Hk HsZ). unfold inst_flip_Z in HZk. simpl in HZk.
        rewrite Nat.eqb_refl in HZk. discriminate. }
      (* 2. Case split on sd T *)
      destruct (sd T) eqn:HTd.
      * (* sd T = true: T must contain all of S_of_X X, contradicting ~ agrees v S *)
        apply HnotvS.
        destruct HvT as [Hvd [HvA [HvB _]]].
        repeat split.
        -- intro. apply Hvd. exact HTd.
        -- intros i Hi HXA. apply HvA; [exact Hi|].
           destruct (sXp T i) eqn:HsA; [reflexivity|].
           (* If sXp T i = false when X i = true, T cannot contain b_i either *)
           exfalso.
           assert (HsB : sXm T i = false).
           { destruct (sXm T i) eqn:HsB'; [|reflexivity].
             (* Pick u = inst_d=true, all=true except b_i=false *)
             set (u := mkInst true (fun _ => true) (fun i' => negb (i' =? i)) true
                              (fun _ => true) (fun _ => true) (fun _ => true)).
             assert (HCu : C_p1 r q u = true).
             { unfold C_p1, u. simpl.
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
           (* Then inst_zero_X i agrees with T, yet kappa = false! *)
           pose proof (HTaxp (inst_zero_X i) (C_p1_zero_X r q i)) as Hkap.
           assert (Hagz : agrees_on r q s (inst_zero_X i) T).
           { repeat split; try (intro; reflexivity); intros i' Hi' Hmem; unfold inst_zero_X; simpl.
             - destruct (Nat.eq_dec i' i); [subst; rewrite HsA in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity].
             - destruct (Nat.eq_dec i' i); [subst; rewrite HsB in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]. }
           apply Hkap in Hagz. unfold kappa_p1 in Hagz. simpl in Hagz.
           rewrite x_ok_zero_X_false in Hagz; [discriminate | exact Hi].
        -- intros i Hi HXB. apply HvB; [exact Hi|].
           destruct (sXm T i) eqn:HsB; [reflexivity|].
           exfalso.
           assert (HsA : sXp T i = false).
           { destruct (sXp T i) eqn:HsA'; [|reflexivity].
             set (u := mkInst true (fun i' => negb (i' =? i)) (fun _ => true) true
                              (fun _ => true) (fun _ => true) (fun _ => true)).
             assert (HCu : C_p1 r q u = true).
             { unfold C_p1, u. simpl.
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
           pose proof (HTaxp (inst_zero_X i) (C_p1_zero_X r q i)) as Hkap.
           assert (Hagz : agrees_on r q s (inst_zero_X i) T).
           { repeat split; try (intro; reflexivity); intros i' Hi' Hmem; unfold inst_zero_X; simpl.
             - destruct (Nat.eq_dec i' i); [subst; rewrite HsA in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity].
             - destruct (Nat.eq_dec i' i); [subst; rewrite HsB in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]. }
           apply Hkap in Hagz. unfold kappa_p1 in Hagz. simpl in Hagz.
           rewrite x_ok_zero_X_false in Hagz; [discriminate | exact Hi].
        -- intro Hc; discriminate.
        -- intros j _ Hc; discriminate.
        -- intros j _ Hc; discriminate.
        -- intros k _ Hc; discriminate.
      * (* sd T = false: sp T must be true *)
        assert (Hsp : sp T = true).
        { destruct (sp T) eqn:Hsp'; [reflexivity|].
          exfalso.
          (* Evaluate T on w with fd=false, fp=false, all other non-Z fields = true, Z = false!
             Wait: T might have sYp or sYm = true, all 1 in inst_d0_p0! *)
          pose proof (HTaxp inst_d0_p0 (C_p1_d0_p0 r q)) as Hkap.
          assert (Hag : agrees_on r q s inst_d0_p0 T).
          { repeat split; unfold inst_d0_p0; simpl; try (intro Hc; rewrite Hc in HTd; discriminate);
            try (intro Hc; rewrite Hc in Hsp'; discriminate);
            try (intros; reflexivity). }
          apply Hkap in Hag. rewrite kappa_p1_d0_p0 in Hag. discriminate. }
        (* Also, for each j < q, T cannot have BOTH sYp T j = true and sYm T j = true! *)
        assert (Hno_both_Y : forall j, j < q -> ~(sYp T j = true /\ sYm T j = true)).
        { intros j Hj [HY1 HY2].
          (* If both are true, then any w agreeing with T has fd w = true (since at fd=false, fp=true forces y_uniq) *)
          apply HnotvS.
          assert (Hvd_true : fd v = true).
          { destruct (fd v) eqn:Hfdv; [reflexivity|].
            exfalso. unfold C_p1 in HCv. rewrite Hfdv in HCv.
            destruct HvT as [_ [_ [_ [Hvp [HvY [HvYb _]]]]]].
            rewrite (Hvp Hsp) in HCv.
            apply Bool.andb_true_iff in HCv. destruct HCv as [_ Hyu].
            unfold y_uniq in Hyu.
            pose proof (forall_nat_elim _ _ Hyu j Hj) as Hyuj. simpl in Hyuj.
            rewrite (HvY j Hj HY1), (HvYb j Hj HY2) in Hyuj. discriminate. }
          (* Since fd v = true and ~ agrees v S, v must violate some a_i or b_i in S;
             yet at fd=true, T cannot omit that member of S! *)
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
              assert (HCu : C_p1 r q u = true).
              { unfold C_p1, u. simpl.
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
            pose proof (HTaxp (inst_zero_X i) (C_p1_zero_X r q i)) as Hkap.
            assert (Hagz : agrees_on r q s (inst_zero_X i) T).
            { repeat split; unfold inst_zero_X; simpl; try (intro Hc; rewrite Hc in HTd; discriminate);
              try (intro; reflexivity); try (intros; reflexivity).
              - intros i' Hi' Hmem. destruct (Nat.eq_dec i' i); [subst; rewrite HsA in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity].
              - intros i' Hi' Hmem. destruct (Nat.eq_dec i' i); [subst; rewrite HsB in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]. }
            apply Hkap in Hagz. unfold kappa_p1 in Hagz. simpl in Hagz.
            rewrite x_ok_zero_X_false in Hagz; [discriminate | exact Hi].
          - intros i Hi HXB. apply HvB; [exact Hi|].
            destruct (sXm T i) eqn:HsB; [reflexivity|].
            exfalso.
            assert (HsA : sXp T i = false).
            { destruct (sXp T i) eqn:HsA'; [|reflexivity].
              set (u := mkInst true (fun i' => negb (i' =? i)) (fun _ => true) true
                               (fun _ => true) (fun _ => true) (fun _ => true)).
              assert (HCu : C_p1 r q u = true).
              { unfold C_p1, u. simpl.
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
            pose proof (HTaxp (inst_zero_X i) (C_p1_zero_X r q i)) as Hkap.
            assert (Hagz : agrees_on r q s (inst_zero_X i) T).
            { repeat split; unfold inst_zero_X; simpl; try (intro Hc; rewrite Hc in HTd; discriminate);
              try (intro; reflexivity); try (intros; reflexivity).
              - intros i' Hi' Hmem. destruct (Nat.eq_dec i' i); [subst; rewrite HsA in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity].
              - intros i' Hi' Hmem. destruct (Nat.eq_dec i' i); [subst; rewrite HsB in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]. }
            apply Hkap in Hagz. unfold kappa_p1 in Hagz. simpl in Hagz.
            rewrite x_ok_zero_X_false in Hagz; [discriminate | exact Hi].
          - intro Hc; discriminate.
          - intros j' _ Hc; discriminate.
          - intros j' _ Hc; discriminate.
          - intros k' _ Hc; discriminate. }
        (* Define Y* : false if sYm T j = true, else true *)
        set (Ystar := fun j => negb (sYm T j)).
        destruct (HXY Ystar) as [Zstar HZstar].
        set (w := inst_of_XYZ X Ystar Zstar).
        pose proof (HTaxp w (C_p1_of_XYZ r q X Ystar Zstar)) as Hkap.
        assert (Hagw : agrees_on r q s w T).
        { unfold w, inst_of_XYZ.
          split. { simpl. intro Hc. rewrite Hc in HTd. discriminate. }
          split. { simpl. intros i Hi HsAi.
            destruct (X i) eqn:HXi; [reflexivity|].
            exfalso.
            set (u := mkInst true (fun i' => negb (i' =? i)) (fun _ => true) true
                             (fun _ => true) (fun _ => true) (fun _ => true)).
            assert (HCu : C_p1 r q u = true).
            { unfold C_p1, u. simpl.
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
            assert (HCu : C_p1 r q u = true).
            { unfold C_p1, u. simpl.
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
        apply Hkap in Hagw. unfold kappa_p1, w, inst_of_XYZ in Hagw. simpl in Hagw.
        rewrite HZstar in Hagw. discriminate.
  - (* Backward: dec_exist_fair_b -> three_qbf *)
    intros [S [HSfair [HSaxp HnoT]]].
    (* 1. sd S must be true *)
    assert (HSd : sd S = true).
    { destruct (sd S) eqn:HSd'; [reflexivity|].
      exfalso. pose proof (HSaxp inst_d0_p0 (C_p1_d0_p0 r q)) as Hkap.
      assert (Hag : agrees_on r q s inst_d0_p0 S).
      { destruct HSfair as [Hsp [HsY [HsYb HsZ]]].
        repeat split; unfold inst_d0_p0; simpl; try (intro Hc; rewrite Hc in HSd'; discriminate);
        try (intro Hc; rewrite Hc in Hsp; discriminate);
        try (intros; reflexivity). }
      apply Hkap in Hag. rewrite kappa_p1_d0_p0 in Hag. discriminate. }
    (* 2. For every i < r, at least one of sXp S i, sXm S i is true *)
    assert (HS_at_least_one : forall i, i < r -> sXp S i = true \/ sXm S i = true).
    { intros i Hi.
      destruct (sXp S i) eqn:HA; [left; reflexivity|].
      destruct (sXm S i) eqn:HB; [right; reflexivity|].
      exfalso. pose proof (HSaxp (inst_zero_X i) (C_p1_zero_X r q i)) as Hkap.
      assert (Hag : agrees_on r q s (inst_zero_X i) S).
      { destruct HSfair as [Hsp [HsY [HsYb HsZ]]].
        unfold inst_zero_X.
        split; [simpl; intro; reflexivity|].
        split; [simpl; intros i' _ Hmem; destruct (Nat.eq_dec i' i); [subst; rewrite HA in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]|].
        split; [simpl; intros i' _ Hmem; destruct (Nat.eq_dec i' i); [subst; rewrite HB in Hmem; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity]|].
        split; [simpl; intro Hc; rewrite Hc in Hsp; discriminate|].
        split; [simpl; intros j _ Hc; rewrite HsY in Hc; discriminate|].
        split; [simpl; intros j _ Hc; rewrite HsYb in Hc; discriminate|].
        simpl; intros k _ Hc; rewrite HsZ in Hc; discriminate. }
      apply Hkap in Hag. unfold kappa_p1 in Hag. simpl in Hag.
      rewrite x_ok_zero_X_false in Hag; [discriminate | exact Hi]. }
    (* 3. For every i < r, CANNOT have both sXp S i = true and sXm S i = true *)
    assert (HS_at_most_one : forall i, i < r -> ~(sXp S i = true /\ sXm S i = true)).
    { intros i0 Hi0 [HA0 HB0].
      set (T := mkSub true (fun i => if i =? i0 then false else sXp S i) (sXm S)
                      true (fun _ => false) (fun _ => false) (fun _ => false)).
      apply (HnoT T).
      - left. reflexivity.
      - (* T is weak AXp *)
        intros w HCw [Hwd [HwA [HwB _]]].
        unfold kappa_p1. rewrite (Hwd eq_refl). apply forall_nat_true. intros i Hi.
        destruct (Nat.eq_dec i i0).
        + subst. rewrite (HwB i0 Hi0 HB0). apply Bool.orb_true_r.
        + destruct (HS_at_least_one i Hi) as [HAi | HBi].
          * rewrite (HwA i Hi); [reflexivity|].
            unfold T. simpl. apply Nat.eqb_neq in n. rewrite n. exact HAi.
          * rewrite (HwB i Hi HBi). apply Bool.orb_true_r.
      - (* T strictly subsumes S *)
        split.
        + intros u HCu [Hud [HuA [HuB _]]].
          repeat split.
          * intro. apply Hud. exact HSd.
          * intros i Hi HTi. unfold T in HTi. simpl in HTi.
            destruct (i =? i0); [discriminate | apply HuA; assumption].
          * intros i Hi HTi. apply HuB; assumption.
          * intro. unfold C_p1 in HCu. rewrite (Hud HSd) in HCu.
            assert (Hok : x_ok r u = true).
            { apply forall_nat_true. intros i Hi.
              destruct (HS_at_least_one i Hi) as [HAi | HBi];
                [rewrite (HuA i Hi HAi); reflexivity | rewrite (HuB i Hi HBi); apply Bool.orb_true_r]. }
            rewrite Hok in HCu. apply Bool.andb_true_iff in HCu. destruct HCu as [Hp _]. exact Hp.
          * intros j _ Hc; simpl in Hc; discriminate.
          * intros j _ Hc; simpl in Hc; discriminate.
          * intros k _ Hc; simpl in Hc; discriminate.
        + set (v := mkInst true (fun i => negb (i =? i0)) (fun _ => true) true
                           (fun _ => true) (fun _ => true) (fun _ => true)).
          exists v. split.
          * unfold C_p1, v. simpl.
            assert (Hok : x_ok r (mkInst true (fun i => negb (i =? i0)) (fun _ => true) true (fun _ => true) (fun _ => true) (fun _ => true)) = true)
              by (apply forall_nat_true; intros; simpl; apply Bool.orb_true_r).
            rewrite Hok. apply forall_nat_true. intros; reflexivity.
          * split.
            -- repeat split; unfold v; simpl; try (intro; reflexivity); try (intros; discriminate).
               intros i Hi HTi. unfold T in HTi. simpl in HTi.
               destruct (Nat.eq_dec i i0); [subst; rewrite Nat.eqb_refl in HTi; discriminate | apply Nat.eqb_neq in n; rewrite n; reflexivity].
            -- intros [_ [HvA _]]. specialize (HvA i0 Hi0 HA0).
               unfold v in HvA. simpl in HvA. rewrite Nat.eqb_refl in HvA. discriminate. }
    (* 4. Define X := sXp S *)
    exists (sXp S). intro Y.
    (* Check T_of_SY S Y *)
    assert (Hnot_waxp : ~ weak_axp r q s phi (T_of_SY S Y)).
    { intro Hwaxp. apply (HnoT (T_of_SY S Y)).
      - left. reflexivity.
      - exact Hwaxp.
      - split.
        + intros u HCu [Hud [HuA [HuB _]]].
          assert (Hok : x_ok r u = true).
          { apply forall_nat_true. intros i Hi.
            destruct (HS_at_least_one i Hi) as [HAi | HBi];
              [rewrite (HuA i Hi HAi); reflexivity | rewrite (HuB i Hi HBi); apply Bool.orb_true_r]. }
          unfold C_p1 in HCu. rewrite (Hud HSd), Hok in HCu.
          apply Bool.andb_true_iff in HCu. destruct HCu as [Hup HuY].
          unfold all_Y_true in HuY. pose proof (forall_nat_elim _ _ HuY) as HuY'.
          repeat split.
          * intro Hc; discriminate.
          * intros i Hi HTi. apply HuA; assumption.
          * intros i Hi HTi. apply HuB; assumption.
          * intro. exact Hup.
          * intros j Hj _. specialize (HuY' j Hj). apply Bool.andb_true_iff in HuY'. exact (proj1 HuY').
          * intros j Hj _. specialize (HuY' j Hj). apply Bool.andb_true_iff in HuY'. exact (proj2 HuY').
          * intros k _ Hc; simpl in Hc; discriminate.
        + exists (inst_of_XYZ (sXp S) Y (fun _ => false)).
          split; [apply C_p1_of_XYZ|].
          split.
          * repeat split; unfold inst_of_XYZ, T_of_SY; simpl; try (intro Hc; discriminate);
            try (intro; reflexivity); try (intros; discriminate).
            -- intros i Hi HTi. rewrite HTi. reflexivity.
            -- intros i Hi HTi.
               destruct (sXp S i) eqn:HAi.
               ++ exfalso. apply (HS_at_most_one i Hi). split; assumption.
               ++ reflexivity.
            -- intros j _ HYj. rewrite HYj. reflexivity.
            -- intros j _ HYbj. rewrite HYbj. reflexivity.
          * intros [Hvd _]. unfold inst_of_XYZ in Hvd. simpl in Hvd.
            specialize (Hvd HSd). discriminate. }
    (* Extract counterexample w via classical logic *)
    unfold weak_axp in Hnot_waxp.
    apply not_all_ex_not in Hnot_waxp. destruct Hnot_waxp as [w Hw].
    apply imply_to_and in Hw. destruct Hw as [HCw Hw].
    apply imply_to_and in Hw. destruct Hw as [Hagw Hkw].
    apply Bool.not_true_iff_false in Hkw.
    (* Prove fd w = false *)
    assert (Hwd0 : fd w = false).
    { destruct (fd w) eqn:Hfdw; [|reflexivity].
      exfalso. unfold kappa_p1 in Hkw. rewrite Hfdw in Hkw.
      destruct Hagw as [_ [HwA [HwB _]]].
      assert (Hok : x_ok r w = true).
      { apply forall_nat_true. intros i Hi.
        destruct (HS_at_least_one i Hi) as [HAi | HBi];
          [rewrite (HwA i Hi HAi); reflexivity | rewrite (HwB i Hi HBi); apply Bool.orb_true_r]. }
      rewrite Hok in Hkw. discriminate. }
    (* Prove fp w = true *)
    destruct Hagw as [_ [HwA [HwB [Hwp [HwY [HwYb _]]]]]].
    assert (Hwp1 : fp w = true) by (apply Hwp; reflexivity).
    unfold kappa_p1 in Hkw. rewrite Hwd0, Hwp1 in Hkw.
    apply Bool.negb_false_iff in Hkw.
    (* Check w agrees with (sXp S) on 0..r-1 and Y on 0..q-1 *)
    unfold C_p1 in HCw. rewrite Hwd0, Hwp1 in HCw.
    apply Bool.andb_true_iff in HCw. destruct HCw as [Hxu Hyu].
    unfold x_uniq in Hxu. unfold y_uniq in Hyu.
    pose proof (forall_nat_elim _ _ Hxu) as Hxu'.
    pose proof (forall_nat_elim _ _ Hyu) as Hyu'.
    exists (fZ w).
    rewrite <- Hkw. apply eval_cnf_ext. intro k.
    unfold combine3.
    destruct (Nat.ltb_spec k r) as [Hk|Hk].
    + (* k < r: fXp w k = sXp S k *)
      destruct (sXp S k) eqn:HAk.
      * symmetry. apply HwA; [exact Hk | exact HAk].
      * destruct (HS_at_least_one k Hk) as [Hc | HBk]; [congruence|].
        specialize (HwB k Hk HBk). specialize (Hxu' k Hk). simpl in Hxu'.
        rewrite HwB in Hxu'. simpl in Hxu'. apply Bool.eqb_prop in Hxu'. symmetry. exact Hxu'.
    + destruct (Nat.ltb_spec k (r + q)) as [Hk2|Hk2].
      * (* r <= k < r + q: fYp w (k - r) = Y (k - r) *)
        assert (Hkr : k - r < q) by lia.
        destruct (Y (k - r)) eqn:HYk.
        -- symmetry. apply HwY; [exact Hkr | exact HYk].
        -- assert (HYbk : negb (Y (k - r)) = true) by (rewrite HYk; reflexivity).
           specialize (HwYb (k - r) Hkr HYbk).
           specialize (Hyu' (k - r) Hkr). simpl in Hyu'.
           rewrite HwYb in Hyu'. simpl in Hyu'. apply Bool.eqb_prop in Hyu'. symmetry. exact Hyu'.
      * reflexivity.
Qed.

(* ========================================================================= *)
(* Literal Definition 3 & 4 & 5 Bridge (is_axp / is_pi) + cnf_bounded        *)
(* ========================================================================= *)

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
  induction n as [|m IH]; intros f1 f2 i0 Hle Hi0 H2 H1; simpl; [lia|].
  destruct (Nat.eq_dec i0 m).
  - subst. rewrite H2, H1.
    assert (Hr : sum_bool m f1 <= sum_bool m f2) by (apply sum_bool_le; intros i Hi; apply Hle; lia).
    lia.
  - assert (Hm : (if f1 m then 1 else 0) <= (if f2 m then 1 else 0)).
    { destruct (f1 m) eqn:E1; [rewrite (Hle m ltac:(lia) E1); lia | destruct (f2 m); lia]. }
    assert (Hr : sum_bool m f1 < sum_bool m f2) by (apply (IH f1 f2 i0); [intros i Hi; apply Hle; lia | lia | exact H2 | exact H1]).
    lia.
Qed.

Lemma sub_weight_lt : forall r q s S1 S2,
  sub_strict_lt r q s S1 S2 -> sub_weight r q s S1 < sub_weight r q s S2.
Proof.
  intros r q s S1 S2 [[H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]] Hlt].
  unfold sub_weight.
  assert (W1 : (if sd S1 then 1 else 0) <= (if sd S2 then 1 else 0)).
  { destruct (sd S1) eqn:E; [rewrite (H1 eq_refl); lia | destruct (sd S2); lia]. }
  assert (W2 : sum_bool r (sXp S1) <= sum_bool r (sXp S2)) by (apply sum_bool_le; exact H2).
  assert (W3 : sum_bool r (sXm S1) <= sum_bool r (sXm S2)) by (apply sum_bool_le; exact H3).
  assert (W4 : (if sp S1 then 1 else 0) <= (if sp S2 then 1 else 0)).
  { destruct (sp S1) eqn:E; [rewrite (H4 eq_refl); lia | destruct (sp S2); lia]. }
  assert (W5 : sum_bool q (sYp S1) <= sum_bool q (sYp S2)) by (apply sum_bool_le; exact H5).
  assert (W6 : sum_bool q (sYm S1) <= sum_bool q (sYm S2)) by (apply sum_bool_le; exact H6).
  assert (W7 : sum_bool s (sZ S1) <= sum_bool s (sZ S2)) by (apply sum_bool_le; exact H7).
  destruct Hlt as [[Ha Hb] | [[i [Hi [Ha Hb]]] | [[i [Hi [Ha Hb]]] | [[Ha Hb] |
                 [[j [Hj [Ha Hb]]] | [[j [Hj [Ha Hb]]] | [k [Hk [Ha Hb]]]]]]]]].
  - rewrite Ha, Hb in *; lia.
  - pose proof (sum_bool_lt r (sXp S1) (sXp S2) i H2 Hi Ha Hb); lia.
  - pose proof (sum_bool_lt r (sXm S1) (sXm S2) i H3 Hi Ha Hb); lia.
  - rewrite Ha, Hb in *; lia.
  - pose proof (sum_bool_lt q (sYp S1) (sYp S2) j H5 Hj Ha Hb); lia.
  - pose proof (sum_bool_lt q (sYm S1) (sYm S2) j H6 Hj Ha Hb); lia.
  - pose proof (sum_bool_lt s (sZ S1) (sZ S2) k H7 Hk Ha Hb); lia.
Qed.

Lemma weak_axp_has_axp : forall r q s phi S,
  weak_axp r q s phi S ->
  exists S' : Sub, sub_le r q s S' S /\ is_axp r q s phi S'.
Proof.
  intros r q s phi S HS.
  remember (sub_weight r q s S) as w eqn:Hw.
  revert S Hw HS.
  induction w as [w IH] using lt_wf_ind.
  intros S Hw HS.
  destruct (classic (is_axp r q s phi S)) as [Haxp | Hnot].
  - exists S. split; [repeat split; intros; auto | exact Haxp].
  - unfold is_axp in Hnot.
    apply not_and_or in Hnot. destruct Hnot as [Hbad | Hnotmin]; [contradiction|].
    apply not_all_ex_not in Hnotmin. destruct Hnotmin as [S1 HS1].
    apply imply_to_and in HS1. destruct HS1 as [Hlt Hnotweak].
    apply NNPP in Hnotweak.
    assert (Hw1 : sub_weight r q s S1 < w) by (subst w; apply sub_weight_lt; exact Hlt).
    destruct (IH (sub_weight r q s S1) Hw1 S1 eq_refl Hnotweak) as [S' [Hle' Haxp']].
    exists S'. split; [|exact Haxp'].
    apply (sub_le_trans r q s S' S1 S Hle' (proj1 Hlt)).
Qed.

(* Finite canonical instance enumeration for coverage-maximal PI extraction *)
Fixpoint all_vecs (n : nat) : list (nat -> bool) :=
  match n with
  | 0 => [fun _ => false]
  | S m =>
      let rest := all_vecs m in
      map (fun f k => if k =? m then false else f k) rest ++
      map (fun f k => if k =? m then true else f k) rest
  end.

Lemma all_vecs_complete : forall n (f : nat -> bool),
  exists g, In g (all_vecs n) /\ forall k, k < n -> g k = f k.
Proof.
  induction n as [|m IH]; intro f; simpl.
  - exists (fun _ => false). split; [left; reflexivity | intros k Hk; lia].
  - destruct (IH f) as [g [Hg1 Hg2]].
    destruct (f m) eqn:Efm.
    + exists (fun k => if k =? m then true else g k). split.
      * apply in_or_app. right. exact (in_map (fun h k => if k =? m then true else h k) _ g Hg1).
      * intros k Hk. destruct (Nat.eqb_spec k m); [subst; symmetry; exact Efm | apply Hg2; lia].
    + exists (fun k => if k =? m then false else g k). split.
      * apply in_or_app. left. exact (in_map (fun h k => if k =? m then false else h k) _ g Hg1).
      * intros k Hk. destruct (Nat.eqb_spec k m); [subst; symmetry; exact Efm | apply Hg2; lia].
Qed.

Definition prod_list {A B : Type} (la : list A) (lb : list B) : list (A * B) :=
  flat_map (fun a => map (fun b => (a, b)) lb) la.

Lemma prod_list_in : forall {A B : Type} (la : list A) (lb : list B) a b,
  In a la -> In b lb -> In (a, b) (prod_list la lb).
Proof.
  intros A B la lb a b Ha Hb. unfold prod_list.
  apply in_flat_map. exists a. split; [exact Ha | apply in_map; exact Hb].
Qed.

Definition all_bools : list bool := [false; true].

Definition all_insts_p1 (r q s : nat) : list Inst :=
  map (fun '(d, A, B, p, Y, Yb, Z) => mkInst d A B p Y Yb Z)
      (prod_list
        (prod_list
          (prod_list
            (prod_list
              (prod_list (prod_list all_bools (all_vecs r)) (all_vecs r))
              all_bools)
            (all_vecs q))
          (all_vecs q))
        (all_vecs s)).

Definition same_inst_p1 (r q s : nat) (u w : Inst) : Prop :=
  fd u = fd w /\
  (forall i, i < r -> fXp u i = fXp w i) /\
  (forall i, i < r -> fXm u i = fXm w i) /\
  fp u = fp w /\
  (forall j, j < q -> fYp u j = fYp w j) /\
  (forall j, j < q -> fYm u j = fYm w j) /\
  (forall k, k < s -> fZ u k = fZ w k).

Lemma all_insts_p1_complete : forall r q s w,
  exists u, In u (all_insts_p1 r q s) /\ same_inst_p1 r q s u w.
Proof.
  intros r q s w.
  destruct (all_vecs_complete r (fXp w)) as [gA [HgA1 HgA2]].
  destruct (all_vecs_complete r (fXm w)) as [gB [HgB1 HgB2]].
  destruct (all_vecs_complete q (fYp w)) as [gY [HgY1 HgY2]].
  destruct (all_vecs_complete q (fYm w)) as [gYb [HgYb1 HgYb2]].
  destruct (all_vecs_complete s (fZ w)) as [gZ [HgZ1 HgZ2]].
  assert (Hd : In (fd w) all_bools) by (unfold all_bools; destruct (fd w); simpl; auto).
  assert (Hp : In (fp w) all_bools) by (unfold all_bools; destruct (fp w); simpl; auto).
  exists (mkInst (fd w) gA gB (fp w) gY gYb gZ). split.
  - unfold all_insts_p1.
    change (mkInst (fd w) gA gB (fp w) gY gYb gZ) with
      ((fun '(d, A, B, p, Y, Yb, Z) => mkInst d A B p Y Yb Z) (fd w, gA, gB, fp w, gY, gYb, gZ)).
    apply in_map.
    repeat apply prod_list_in; assumption.
  - repeat split; simpl; auto.
Qed.

Lemma forall_nat_ext : forall n P Q,
  (forall i, i < n -> P i = Q i) -> forall_nat n P = forall_nat n Q.
Proof.
  induction n as [|m IH]; intros P Q H; simpl; [reflexivity|].
  rewrite (H m ltac:(lia)), (IH P Q (fun i Hi => H i ltac:(lia))). reflexivity.
Qed.

Lemma C_p1_same_inst : forall r q s u w,
  same_inst_p1 r q s u w -> C_p1 r q u = C_p1 r q w.
Proof.
  intros r q s u w [Hd [HA [HB [Hp [HY [HYb _]]]]]].
  assert (Exok : x_ok r u = x_ok r w) by (unfold x_ok; apply forall_nat_ext; intros i Hi; rewrite (HA i Hi), (HB i Hi); reflexivity).
  assert (Exu : x_uniq r u = x_uniq r w) by (unfold x_uniq; apply forall_nat_ext; intros i Hi; rewrite (HA i Hi), (HB i Hi); reflexivity).
  assert (Eyu : y_uniq q u = y_uniq q w) by (unfold y_uniq; apply forall_nat_ext; intros j Hj; rewrite (HY j Hj), (HYb j Hj); reflexivity).
  assert (EallY : all_Y_true q u = all_Y_true q w) by (unfold all_Y_true; apply forall_nat_ext; intros j Hj; rewrite (HY j Hj), (HYb j Hj); reflexivity).
  unfold C_p1. rewrite Hd, Exok, Exu, Eyu, Hp, EallY. reflexivity.
Qed.

Lemma agrees_on_same_inst : forall r q s u w S,
  same_inst_p1 r q s u w -> (agrees_on r q s u S <-> agrees_on r q s w S).
Proof.
  intros r q s u w S [Hd [HA [HB [Hp [HY [HYb HZ]]]]]].
  unfold agrees_on. rewrite Hd, Hp.
  split; intros [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]; repeat split; intros; auto.
  - rewrite <- (HA i H); auto.
  - rewrite <- (HB i H); auto.
  - rewrite <- (HY j H); auto.
  - rewrite <- (HYb j H); auto.
  - rewrite <- (HZ k H); auto.
  - rewrite (HA i H); auto.
  - rewrite (HB i H); auto.
  - rewrite (HY j H); auto.
  - rewrite (HYb j H); auto.
  - rewrite (HZ k H); auto.
Qed.

Definition agrees_bool (r q s : nat) (w : Inst) (S : Sub) : bool :=
  (negb (sd S) || fd w) &&
  forall_nat r (fun i => negb (sXp S i) || fXp w i) &&
  forall_nat r (fun i => negb (sXm S i) || fXm w i) &&
  (negb (sp S) || fp w) &&
  forall_nat q (fun j => negb (sYp S j) || fYp w j) &&
  forall_nat q (fun j => negb (sYm S j) || fYm w j) &&
  forall_nat s (fun k => negb (sZ S k) || fZ w k).

Lemma agrees_bool_iff : forall r q s w S,
  agrees_bool r q s w S = true <-> agrees_on r q s w S.
Proof.
  intros r q s w S. unfold agrees_bool, agrees_on.
  repeat rewrite Bool.andb_true_iff.
  repeat rewrite forall_nat_iff.
  assert (Hd : (negb (sd S) || fd w = true) <-> (sd S = true -> fd w = true))
    by (destruct (sd S); destruct (fd w); simpl; split; intro H; try discriminate; auto).
  assert (Hp : (negb (sp S) || fp w = true) <-> (sp S = true -> fp w = true))
    by (destruct (sp S); destruct (fp w); simpl; split; intro H; try discriminate; auto).
  assert (HA : (forall i, i < r -> negb (sXp S i) || fXp w i = true) <-> (forall i, i < r -> sXp S i = true -> fXp w i = true))
    by (split; intros H i Hi; pose proof (H i Hi) as Hi0; destruct (sXp S i); destruct (fXp w i); simpl in *; auto; discriminate).
  assert (HB : (forall i, i < r -> negb (sXm S i) || fXm w i = true) <-> (forall i, i < r -> sXm S i = true -> fXm w i = true))
    by (split; intros H i Hi; pose proof (H i Hi) as Hi0; destruct (sXm S i); destruct (fXm w i); simpl in *; auto; discriminate).
  assert (HY : (forall j, j < q -> negb (sYp S j) || fYp w j = true) <-> (forall j, j < q -> sYp S j = true -> fYp w j = true))
    by (split; intros H j Hj; pose proof (H j Hj) as Hj0; destruct (sYp S j); destruct (fYp w j); simpl in *; auto; discriminate).
  assert (HYb : (forall j, j < q -> negb (sYm S j) || fYm w j = true) <-> (forall j, j < q -> sYm S j = true -> fYm w j = true))
    by (split; intros H j Hj; pose proof (H j Hj) as Hj0; destruct (sYm S j); destruct (fYm w j); simpl in *; auto; discriminate).
  assert (HZ : (forall k, k < s -> negb (sZ S k) || fZ w k = true) <-> (forall k, k < s -> sZ S k = true -> fZ w k = true))
    by (split; intros H k Hk; pose proof (H k Hk) as Hk0; destruct (sZ S k); destruct (fZ w k); simpl in *; auto; discriminate).
  tauto.
Qed.

Lemma filter_le : forall {A : Type} (L : list A) (p1 p2 : A -> bool),
  (forall a, In a L -> p1 a = true -> p2 a = true) ->
  length (filter p1 L) <= length (filter p2 L).
Proof.
  induction L as [|a rest IH]; intros p1 p2 H; simpl; [lia|].
  assert (Hr : length (filter p1 rest) <= length (filter p2 rest))
    by (apply IH; intros x Hx; apply H; right; exact Hx).
  destruct (p1 a) eqn:E1; destruct (p2 a) eqn:E2; simpl; try lia.
  pose proof (H a (or_introl eq_refl) E1) as Hbad. rewrite E2 in Hbad. discriminate.
Qed.

Lemma filter_strict_lt : forall {A : Type} (L : list A) (p1 p2 : A -> bool),
  (forall a, In a L -> p1 a = true -> p2 a = true) ->
  (exists v, In v L /\ p2 v = true /\ p1 v = false) ->
  length (filter p1 L) < length (filter p2 L).
Proof.
  induction L as [|a rest IH]; intros p1 p2 Hle [v [Hv1 [Hv2 Hv3]]]; simpl in *; [contradiction|].
  destruct Hv1 as [Heq | Hrest].
  - subst v. rewrite Hv2, Hv3. simpl.
    assert (Hr : length (filter p1 rest) <= length (filter p2 rest))
      by (apply filter_le; intros x Hx; apply Hle; right; exact Hx).
    lia.
  - assert (Hsub : length (filter p1 rest) < length (filter p2 rest)).
    { apply IH; [intros x Hx; apply Hle; right; exact Hx | exists v; auto]. }
    destruct (p1 a) eqn:E1; destruct (p2 a) eqn:E2; simpl; try lia.
    pose proof (Hle a (or_introl eq_refl) E1) as Hbad. rewrite E2 in Hbad. discriminate.
Qed.

Lemma filter_length_le : forall {A : Type} (L : list A) (p : A -> bool),
  length (filter p L) <= length L.
Proof.
  induction L as [|a rest IH]; intro p; simpl; [lia|].
  destruct (p a); simpl; pose proof (IH p); lia.
Qed.

Definition cov_count_p1 (r q s : nat) (S : Sub) : nat :=
  length (filter (fun u => C_p1 r q u && agrees_bool r q s u S) (all_insts_p1 r q s)).

Lemma strictly_subsumes_cov_lt : forall r q s S1 S2,
  strictly_subsumes r q s S2 S1 ->
  cov_count_p1 r q s S1 < cov_count_p1 r q s S2.
Proof.
  intros r q s S1 S2 [Hsub [v [HvC [Hv2 Hv1]]]].
  unfold cov_count_p1. apply filter_strict_lt.
  - intros a _ Ha. apply Bool.andb_true_iff in Ha. destruct Ha as [HaC Ha1].
    apply Bool.andb_true_iff. split; [exact HaC|].
    apply agrees_bool_iff. apply Hsub; [exact HaC | apply agrees_bool_iff; exact Ha1].
  - destruct (all_insts_p1_complete r q s v) as [v0 [Hv0In Hsame]].
    exists v0. split; [exact Hv0In|]. split.
    + apply Bool.andb_true_iff. split.
      * rewrite (C_p1_same_inst r q s v0 v Hsame). exact HvC.
      * apply agrees_bool_iff. apply (proj2 (agrees_on_same_inst r q s v0 v S2 Hsame)). exact Hv2.
    + destruct (agrees_bool r q s v0 S1) eqn:E1; [|rewrite Bool.andb_false_r; reflexivity].
      exfalso. apply Hv1. apply (proj1 (agrees_on_same_inst r q s v0 v S1 Hsame)).
      apply agrees_bool_iff. exact E1.
Qed.

Lemma strictly_subsumes_trans : forall r q s S3 S2 S1,
  strictly_subsumes r q s S3 S2 ->
  strictly_subsumes r q s S2 S1 ->
  strictly_subsumes r q s S3 S1.
Proof.
  intros r q s S3 S2 S1 [H32 _] [H21 [v [HvC [Hv2 Hv1]]]].
  split.
  - intros u HuC Hu1. apply H32; [exact HuC | apply H21; assumption].
  - exists v. split; [exact HvC | split; [apply H32; assumption | exact Hv1]].
Qed.

Lemma weak_fair_to_pi_fair : forall r q s phi,
  dec_exist_fair_b r q s phi ->
  dec_exist_fair_pi r q s phi.
Proof.
  intros r q s phi [S0 [HS0fair [HS0w HS0no]]].
  assert (HS0fb : is_fair_bounded q s S0).
  { destruct HS0fair as [H1 [H2 [H3 H4]]]. repeat split; auto. }
  assert (Hfind : forall S,
    is_fair_bounded q s S ->
    weak_axp r q s phi S ->
    (forall T, is_unfair_bounded q s T -> weak_axp r q s phi T -> ~ strictly_subsumes r q s T S) ->
    exists S_max,
      is_fair_bounded q s S_max /\
      weak_axp r q s phi S_max /\
      (forall T, weak_axp r q s phi T -> ~ strictly_subsumes r q s T S_max)).
  { intros S HSf HSw HSno.
    remember (length (all_insts_p1 r q s) - cov_count_p1 r q s S) as m eqn:Hm.
    revert S Hm HSf HSw HSno.
    induction m as [m IH] using lt_wf_ind.
    intros S Hm HSf HSw HSno.
    destruct (classic (exists S1, is_fair_bounded q s S1 /\ weak_axp r q s phi S1 /\ strictly_subsumes r q s S1 S))
      as [[S1 [HS1f [HS1w HS1sub]]] | Hno_fair].
    - assert (Hcnt : cov_count_p1 r q s S < cov_count_p1 r q s S1) by (apply strictly_subsumes_cov_lt; exact HS1sub).
      assert (Hbd1 : cov_count_p1 r q s S1 <= length (all_insts_p1 r q s)) by (unfold cov_count_p1; apply filter_length_le).
      assert (Hm1 : length (all_insts_p1 r q s) - cov_count_p1 r q s S1 < m) by lia.
      apply (IH _ Hm1 S1 eq_refl HS1f HS1w).
      intros T HTu HTw Hsub1. apply (HSno T HTu HTw).
      exact (strictly_subsumes_trans r q s T S1 S Hsub1 HS1sub).
    - exists S. split; [exact HSf | split; [exact HSw |]].
      intros T HTw HsubT.
      destruct (classic (is_unfair_bounded q s T)) as [HTu | HTf].
      + exact (HSno T HTu HTw HsubT).
      + apply Hno_fair. exists T. split; [|split; assumption].
        repeat split.
        * destruct (sp T) eqn:Ep; [exfalso; apply HTf; left; exact Ep | reflexivity].
        * intros j Hj. destruct (sYp T j) eqn:EY; [exfalso; apply HTf; right; left; exists j; auto | reflexivity].
        * intros j Hj. destruct (sYm T j) eqn:EYb; [exfalso; apply HTf; right; right; left; exists j; auto | reflexivity].
        * intros k Hk. destruct (sZ T k) eqn:EZ; [exfalso; apply HTf; right; right; right; exists k; auto | reflexivity]. }
  destruct (Hfind S0 HS0fb HS0w HS0no) as [Smax [HSmaxf [HSmaxw HSmaxno]]].
  destruct (weak_axp_has_axp r q s phi Smax HSmaxw) as [Saxp [Hle Haxp]].
  exists Saxp. split.
  - destruct HSmaxf as [H1 [H2 [H3 H4]]]. destruct Hle as [_ [_ [_ [L4 [L5 [L6 L7]]]]]].
    repeat split.
    + destruct (sp Saxp) eqn:E; [pose proof (L4 eq_refl) as Htmp; congruence | reflexivity].
    + intros j Hj. destruct (sYp Saxp j) eqn:E; [pose proof (L5 j Hj E) as Htmp; pose proof (H2 j Hj); congruence | reflexivity].
    + intros j Hj. destruct (sYm Saxp j) eqn:E; [pose proof (L6 j Hj E) as Htmp; pose proof (H3 j Hj); congruence | reflexivity].
    + intros k Hk. destruct (sZ Saxp k) eqn:E; [pose proof (L7 k Hk E) as Htmp; pose proof (H4 k Hk); congruence | reflexivity].
  - split; [exact Haxp|].
    intros T [HTw _] [HcovT [v [HvC [HvT HvnS]]]].
    apply (HSmaxno T HTw). split.
    + intros u HuC HuMax. apply HcovT; [exact HuC | exact (agrees_sub_le r q s u Saxp Smax Hle HuMax)].
    + exists v. split; [exact HvC | split; [exact HvT |]].
      intro HvMax. apply HvnS. exact (agrees_sub_le r q s v Saxp Smax Hle HvMax).
Qed.

Lemma pi_fair_to_weak_fair : forall r q s phi,
  dec_exist_fair_pi r q s phi ->
  dec_exist_fair_b r q s phi.
Proof.
  intros r q s phi [S [HSf [[HSw _] HnoSub]]].
  exists (mkSub (sd S) (sXp S) (sXm S) false (fun _ => false) (fun _ => false) (fun _ => false)).
  assert (HeqAg : forall w, agrees_on r q s w (mkSub (sd S) (sXp S) (sXm S) false (fun _ => false) (fun _ => false) (fun _ => false)) <-> agrees_on r q s w S).
  { intro w. destruct HSf as [H1 [H2 [H3 H4]]].
    split; intros [A1 [A2 [A3 [A4 [A5 [A6 A7]]]]]]; repeat split; simpl in *; intros; auto;
    first [ rewrite H1 in H; discriminate
          | rewrite H2 in H0; [discriminate | exact H]
          | rewrite H3 in H0; [discriminate | exact H]
          | rewrite H4 in H0; [discriminate | exact H]
          | discriminate ]. }
  split; [repeat split; reflexivity |]. split.
  - intros w HwC Hwag. apply HSw; [exact HwC | apply (proj1 (HeqAg w)); exact Hwag].
  - intros T _ HTw [HcovT [v [HvC [HvT Hvn]]]].
    destruct (weak_axp_has_axp r q s phi T HTw) as [T' [HTle HTaxp]].
    apply (HnoSub T' HTaxp). split.
    + intros u HuC HuS. apply (agrees_sub_le r q s u T' T HTle).
      apply HcovT; [exact HuC | apply (proj2 (HeqAg u)); exact HuS].
    + exists v. split; [exact HvC | split; [apply (agrees_sub_le r q s v T' T HTle); exact HvT |]].
      intro HvS. apply Hvn. apply (proj2 (HeqAg v)); exact HvS.
Qed.

Theorem p1_sigma3p_equiv_literal :
  forall (r q s : nat) (phi : cnf),
    cnf_bounded (r + q + s) phi ->
    (three_qbf r q phi <-> dec_exist_fair_pi r q s phi).
Proof.
  intros r q s phi _. split.
  - intro H. apply weak_fair_to_pi_fair. apply (proj1 (p1_sigma3p_equiv r q s phi)). exact H.
  - intro H. apply (proj2 (p1_sigma3p_equiv r q s phi)). apply pi_fair_to_weak_fair. exact H.
Qed.

Print Assumptions p1_sigma3p_equiv_literal.
Print Assumptions p1_sigma3p_equiv.
