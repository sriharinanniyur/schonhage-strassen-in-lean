import Mathlib

set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option maxHeartbeats 3200000

-- =====================================================================
-- DEFINITIONS
-- =====================================================================

def fermat_ext (b n : Nat) : Nat := b ^ n + 1

lemma fermat_ext_pos (b n : Nat) : 0 < fermat_ext b n := by
  unfold fermat_ext; positivity

instance fermat_ext_neZero (b n : Nat) : NeZero (fermat_ext b n) :=
  ⟨Nat.pos_iff_ne_zero.mp (fermat_ext_pos b n)⟩

def decompose (A b : Nat) (K : Nat) : Fin K → Nat :=
  fun j =>
    if j.val < K - 1 then (A / b ^ j.val) % b
    else A / b ^ (K - 1)

def recompose_zmod {K : Nat} {F_outer : Nat} [NeZero F_outer]
    (d : Fin K → Int) (b : Nat) : ZMod F_outer :=
  ∑ j : Fin K, ((d j : Int) : ZMod F_outer) * ((b : ZMod F_outer) ^ j.val)

def NTT_zmod {K : Nat} {F : Nat} [NeZero F]
    (x : Fin K → ZMod F) (omega : ZMod F) : Fin K → ZMod F :=
  fun i => ∑ j : Fin K, x j * omega ^ (j.val * i.val)

def FFT {k : Nat} {F : Nat} [NeZero F]
    (x : Fin (2^k) → ZMod F) (omega : ZMod F) :
    Fin (2^k) → ZMod F :=
  match k with
  | 0     => x
  | k'+1  =>
    let evens : Fin (2^k') → ZMod F :=
      fun j => x ⟨2 * j.val, by
        have hj : j.val < 2^k' := j.isLt
        have hp : (2:Nat)^(k'+1) = 2 * 2^k' := by simp [pow_succ 2 k']; ring
        omega⟩
    let odds : Fin (2^k') → ZMod F :=
      fun j => x ⟨2 * j.val + 1, by
        have hj : j.val < 2^k' := j.isLt
        have hp : (2:Nat)^(k'+1) = 2 * 2^k' := by simp [pow_succ 2 k']; ring
        omega⟩
    let E := FFT evens (omega^2)
    let O := FFT odds  (omega^2)
    fun i =>
      let j : Fin (2^k') := ⟨i.val % 2^k', Nat.mod_lt _ (by positivity)⟩
      E j + (if i.val < 2^k' then 1 else -1) * omega^j.val * O j

def sign_recover {F : Nat} [NeZero F] (z : ZMod F) (threshold : Int) : Int :=
  let v : Int := z.val
  if v ≥ threshold then v - (F : Int) else v

def good_n (n : Nat) : Prop :=
  ∃ k : Nat, 2 ≤ k ∧ 2 ^ k ∣ n

lemma exists_suitable_n' (n : Nat) (hn : good_n n) (h_large : ¬(n < 16)) :
    let k := Nat.min (Classical.choose hn) (Nat.log 2 n - 1)
    let K := 2 ^ k
    let M := n / K
    ∃ n' : Nat, (n' ≥ 2*M + k) ∧ (n' < n) ∧ (good_n n') ∧ (2^k ∣ n') := by
  refine' ⟨ n - 2 ^ ( Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) ), _, _, _, _ ⟩ <;> norm_num at *;
  · refine' le_tsub_of_add_le_left _;
    have h_exp : 2 ^ (Nat.min (Classical.choose hn) (Nat.log 2 n - 1) + 1) ≤ n := by
      have h_exp : Nat.min (Classical.choose hn) (Nat.log 2 n - 1) + 1 ≤ Nat.log 2 n := by
        exact Nat.succ_le_of_lt ( lt_of_le_of_lt ( Nat.min_le_right _ _ ) ( Nat.pred_lt ( ne_bot_of_gt ( Nat.log_pos one_lt_two ( by linarith ) ) ) ) );
      exact Nat.pow_le_of_le_log ( by linarith ) h_exp;
    rcases k : Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ) with ( _ | _ | k ) <;> simp_all +decide [ pow_succ' ];
    · exact absurd ( k.resolve_left ( by linarith [ Classical.choose_spec hn ] ) ) ( Nat.ne_of_gt ( Nat.sub_pos_of_lt ( Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ) ) );
    · cases min_choice ( Classical.choose hn ) ( Nat.log 2 n - 1 ) <;> simp_all +decide [ Nat.log_eq_iff ];
      · have := Classical.choose_spec hn; aesop;
      · interval_cases n;
    · rename_i k';
      nlinarith [ Nat.div_mul_le_self n ( 2 * ( 2 * 2 ^ k' ) ), show k' < 2 ^ k' from Nat.recOn k' ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ Nat.one_le_pow n 2 zero_lt_two ] ];
  · linarith;
  · refine' ⟨ Nat.min ( Classical.choose hn ) ( Nat.log 2 n - 1 ), _, _ ⟩ <;> norm_num at *;
    · exact ⟨ Classical.choose_spec hn |>.1, Nat.le_sub_one_of_lt ( Nat.le_log_of_pow_le ( by decide ) ( by linarith ) ) ⟩;
    · exact Or.inl ( dvd_trans ( pow_dvd_pow _ ( Nat.min_le_left _ _ ) ) ( Classical.choose_spec hn |>.2 ) );
  · exact Or.inl ( dvd_trans ( pow_dvd_pow _ ( Nat.min_le_left _ _ ) ) ( Classical.choose_spec hn |>.2 ) )


lemma fermat_ext_eq_pow_pow (BASE K M : Nat) :
    fermat_ext BASE (K * M) = (BASE ^ M) ^ K + 1 := by
  rw [ ← pow_mul, mul_comm ]; rfl

lemma base_pow_eq_neg_one_mod_fermat_ext (BASE n : Nat) :
    (BASE : ZMod (fermat_ext BASE n)) ^ n = -1 := by
  rw [ eq_neg_iff_add_eq_zero ];
  norm_cast;
  erw [ ZMod.natCast_eq_zero_iff ];
  rfl

lemma theta_pow_2K_eq_one (BASE n K : Nat) (hK : 0 < K) (hKdvd : K ∣ n) :
    ((BASE : ZMod (fermat_ext BASE n)) ^ (n / K)) ^ (2 * K) = 1 := by
  have hTHETAK : ((BASE : ZMod (fermat_ext BASE n)) ^ (n / K)) ^ K = -1 := by
    rw [ ← pow_mul, Nat.div_mul_cancel hKdvd, base_pow_eq_neg_one_mod_fermat_ext ];
  linear_combination' hTHETAK * hTHETAK

lemma theta_pow_K_eq_neg_one (BASE n K : Nat) (hK : 0 < K) (hKdvd : K ∣ n) :
    ((BASE : ZMod (fermat_ext BASE n)) ^ (n / K)) ^ K = -1 := by
  rw [ ← pow_mul, Nat.div_mul_cancel hKdvd, base_pow_eq_neg_one_mod_fermat_ext ]

lemma omega_pow_K_eq_one (BASE n K : Nat) (hK : 0 < K) (hKdvd : K ∣ n) :
    (((BASE : ZMod (fermat_ext BASE n)) ^ (n / K)) ^ 2) ^ K = 1 := by
  rw [ ← pow_mul, mul_comm 2 K, pow_mul, theta_pow_K_eq_neg_one BASE n K hK hKdvd ]; ring

lemma decompose_sum (A b K : Nat) (hK : 0 < K) :
    ∑ j : Fin K, (decompose A b K j) * b ^ j.val = A := by
  induction' hK with K hK ih;
  · unfold decompose; aesop;
  · rcases K with ( _ | K ) <;> simp_all +decide [ Fin.sum_univ_castSucc, decompose ];
    convert ih using 1;
    rw [ ← Nat.mod_add_div ( A / b ^ K ) b ] ; ring;
    norm_num [ Nat.div_div_eq_div_mul ];
    exact Or.inl ( by rw [ mul_comm ] )

-- ====================================================================
-- CommRing-level NTT lemmas (unchanged)
-- ====================================================================

lemma ntt_pointwise_product_eq_conv {R : Type*} [CommRing R]
    (OMEGA : R) (k : ℕ) (hk : 0 < k)
    (hOMEGA_half : OMEGA ^ (2 ^ (k - 1)) = -1)
    (hOMEGAK : OMEGA ^ (2 ^ k) = 1)
    (a b : Fin (2 ^ k) → R) (i : Fin (2 ^ k)) :
    (∑ j : Fin (2 ^ k), a j * OMEGA ^ (j.val * i.val)) *
    (∑ j : Fin (2 ^ k), b j * OMEGA ^ (j.val * i.val)) =
    ∑ r : Fin (2 ^ k),
      (∑ l : Fin (2 ^ k), ∑ m : Fin (2 ^ k),
        if (l.val + m.val) % (2 ^ k) = r.val then a l * b m else 0) *
      OMEGA ^ (r.val * i.val) := by
  simp +decide only [Finset.sum_mul];
  rw [ Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun y hy => _;
  rw [ Finset.mul_sum _ _ _ ];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ];
  intro x hx
  have h_exp : OMEGA ^ ((y.val + x.val) * i.val) = OMEGA ^ (((y.val + x.val) % (2 ^ k)) * i.val) := by
    rw [ ← Nat.mod_add_div ( ( y + x ) : ℕ ) ( 2 ^ k ) ] ; simp +decide [ pow_add, pow_mul, hOMEGAK ] ;
  rw [ Finset.sum_eq_single ⟨ ( y + x ) % 2 ^ k, Nat.mod_lt _ ( by positivity ) ⟩ ] <;> simp +decide [ *, pow_mul ];
  · convert congr_arg ( fun z => a y * b x * z ) h_exp using 1 <;> ring;
  · exact fun z hz h => False.elim <| hz <| Fin.ext h.symm

lemma weighted_conv_eq_negacyclic {R : Type*} [CommRing R]
    (THETA THETAinv : R) (k : ℕ) (hk : 0 < k)
    (hTHETAK : THETA ^ (2 ^ k) = -1)
    (hTHETAinv : THETA * THETAinv = 1)
    (a b : Fin (2 ^ k) → R) (j : Fin (2 ^ k)) :
    (∑ l : Fin (2 ^ k), ∑ m : Fin (2 ^ k),
      if (l.val + m.val) % (2 ^ k) = j.val then
        (a l * THETA ^ l.val) * (b m * THETA ^ m.val) else 0) *
    THETAinv ^ j.val =
    ∑ l : Fin (2 ^ k), ∑ m : Fin (2 ^ k),
      if (l.val + m.val) % (2 ^ k) = j.val then
        (if l.val + m.val < 2 ^ k then a l * b m else -(a l * b m))
      else 0 := by
  have hTHETA_inv : ∀ l m : Fin (2 ^ k), (l.val + m.val) % 2 ^ k = j.val → (THETA ^ (l.val + m.val) * THETAinv ^ j.val) = if l.val + m.val < 2 ^ k then 1 else -1 := by
    intro l m hl
    have h_cases : (l.val + m.val) = j.val + 2 ^ k * ((l.val + m.val) / 2 ^ k) := by
      rw [ ← hl, Nat.mod_add_div ];
    rw [ h_cases, pow_add, pow_mul ];
    rcases Nat.even_or_odd' ( ( l + m ) / 2 ^ k ) with ⟨ c, d | d ⟩ <;> norm_num [ d, pow_add, pow_mul, hTHETAK ];
    · rcases c with ( _ | c ) <;> simp +decide [ d ] at *;
      · rw [ ← mul_pow, hTHETAinv, one_pow ];
      · nlinarith [ Fin.is_lt l, Fin.is_lt m, Fin.is_lt j, pow_pos ( zero_lt_two' ℕ ) k ];
    · rw [ if_neg ( by nlinarith [ Fin.is_lt j, pow_pos ( zero_lt_two' ℕ ) k ] ) ];
      rw [ ← mul_pow, hTHETAinv, one_pow ];
  simp +decide [ Finset.sum_mul _ _ _, mul_assoc, mul_left_comm, ← mul_add, ← hTHETA_inv ];
  refine' Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun m hm => _;
  grind

lemma geom_sum_pow2_eq_prod {R : Type*} [CommRing R]
    (x : R) (k : ℕ) :
    ∑ j : Fin (2 ^ k), x ^ j.val = ∏ i : Fin k, (1 + x ^ (2 ^ i.val)) := by
  induction' k with k ih;
  · simp +decide [ Fin.sum_univ_succ, Fin.prod_univ_succ ];
  · convert congr_arg ( fun y => ( 1 + x ^ 2 ^ k ) * y ) ih using 1;
    · have h_split : Finset.range (2 ^ (k + 1)) = Finset.range (2 ^ k) ∪ Finset.image (fun j => 2 ^ k + j) (Finset.range (2 ^ k)) := by
        ext j
        simp [Finset.mem_range, Finset.mem_union, Finset.mem_image];
        exact ⟨ fun h => or_iff_not_imp_left.mpr fun h' => ⟨ j - 2 ^ k, by rw [ tsub_lt_iff_left ] <;> linarith [ pow_succ' 2 k ], by rw [ add_tsub_cancel_of_le ] ; linarith [ pow_succ' 2 k ] ⟩, fun h => h.elim ( fun h => h.trans_le ( Nat.pow_le_pow_right ( by decide ) ( Nat.le_succ _ ) ) ) fun ⟨ a, ha, ha' ⟩ => by rw [ ← ha' ] ; linarith [ pow_succ' 2 k ] ⟩;
      convert congr_arg ( fun s => ∑ j ∈ s, x ^ j ) h_split using 1;
      · rw [ Finset.sum_range ];
      · rw [ Finset.sum_union ] <;> norm_num [ Finset.sum_range, pow_add, mul_assoc, Finset.mul_sum _ _ _ ];
        · simp +decide only [add_mul, one_mul, Finset.sum_add_distrib];
        · norm_num [ Finset.disjoint_right ];
    · rw [ Fin.prod_univ_castSucc, mul_comm ];
      rfl

lemma geom_sum_roots_pow2_eq_zero {R : Type*} [CommRing R]
    (OMEGA : R) (k : ℕ) (hk : 0 < k)
    (hOMEGA_half : OMEGA ^ (2 ^ (k - 1)) = -1)
    (s : ℕ) (hs_pos : 0 < s) (hs_lt : s < 2 ^ k) :
    ∑ j : Fin (2 ^ k), OMEGA ^ (j.val * s) = 0 := by
  set a := Nat.factorization s 2 with ha_def
  have ha : s = 2^a * (s / 2^a) := by
    rw [ Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) ]
  have ha_odd : Odd (s / 2^a) := by
    exact Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => absurd ( Nat.dvd_of_mod_eq_zero h ) ( Nat.not_dvd_ordCompl ( by norm_num ) ( by linarith ) ) )
  have ha_lt : a < k := by
    contrapose! hs_lt;
    exact Nat.le_of_dvd hs_pos ( ha.symm ▸ dvd_mul_of_dvd_left ( pow_dvd_pow _ hs_lt ) _ );
  have h_exp : OMEGA ^ (s * 2 ^ (k - 1 - a)) = -1 := by
    have h_exp_subst : OMEGA ^ (s * 2 ^ (k - 1 - a)) = OMEGA ^ (2 ^ (k - 1) * (s / 2 ^ a)) := by
      rw [ ha, mul_assoc, mul_comm ];
      rw [ mul_assoc, ← pow_add, tsub_add_cancel_of_le ( Nat.le_sub_one_of_lt ha_lt ) ] ; norm_num [ Nat.mul_div_cancel_left _ ( pow_pos ( zero_lt_two' ℕ ) _ ) ] ; ring;
    rw [ h_exp_subst, pow_mul, hOMEGA_half ];
    exact ha_odd.neg_one_pow;
  have h_prod : ∑ j : Fin (2 ^ k), OMEGA ^ (j.val * s) = ∏ i : Fin k, (1 + OMEGA ^ (s * 2 ^ i.val)) := by
    convert geom_sum_pow2_eq_prod ( OMEGA ^ s ) k using 1;
    · exact Finset.sum_congr rfl fun _ _ => by ring;
    · exact Finset.prod_congr rfl fun _ _ => by ring;
  rw [ h_prod, Finset.prod_eq_zero ( Finset.mem_univ ⟨ k - 1 - a, by omega ⟩ ) ] ; simp +decide [ h_exp ]

lemma ntt_inverse_property_pow2 {R : Type*} [CommRing R]
    (OMEGA OMEGAinv : R) (k : ℕ) (hk : 0 < k)
    (hOMEGA_half : OMEGA ^ (2 ^ (k - 1)) = -1)
    (hOMEGAK : OMEGA ^ (2 ^ k) = 1)
    (hOMEGAinv : OMEGA * OMEGAinv = 1)
    (x : Fin (2 ^ k) → R) (j : Fin (2 ^ k)) :
    (2 ^ k : ℕ) • x j = ∑ i : Fin (2 ^ k),
      (∑ l : Fin (2 ^ k), x l * OMEGA ^ (l.val * i.val)) * OMEGAinv ^ (i.val * j.val) := by
  have orthogonality : ∀ l j : Fin (2 ^ k), (∑ i : Fin (2 ^ k), OMEGA ^ (l.val * i.val : ℕ) * OMEGAinv ^ (j.val * i.val : ℕ)) = if l = j then 2 ^ k else 0 := by
    have hOMEGAinv_half : OMEGAinv ^ (2 ^ (k - 1)) = -1 := by
      have hOMEGAinv_half : OMEGA ^ (2 ^ (k - 1)) * OMEGAinv ^ (2 ^ (k - 1)) = 1 := by
        rw [ ← mul_pow, hOMEGAinv, one_pow ];
      grind;
    intro l j; split_ifs with h; simp_all +decide [ ← mul_pow ] ;
    by_cases h_cases : l.val > j.val;
    · convert geom_sum_roots_pow2_eq_zero OMEGA k hk hOMEGA_half ( l - j ) ( Nat.sub_pos_of_lt h_cases ) _ using 1;
      · refine' Finset.sum_congr rfl fun i hi => _;
        rw [ show ( l : ℕ ) * i = i * ( l - j ) + j * i by nlinarith [ Nat.sub_add_cancel h_cases.le ] ] ; simp +decide [ pow_add, pow_mul', hOMEGAinv ] ; ring;
        simp +decide [ mul_assoc, ← mul_pow, hOMEGAinv ];
      · exact lt_of_le_of_lt ( Nat.sub_le _ _ ) ( Fin.is_lt _ );
    · have h_ortho : ∑ i : Fin (2 ^ k), (OMEGAinv ^ (j.val - l.val)) ^ (i.val : ℕ) = 0 := by
        convert geom_sum_roots_pow2_eq_zero OMEGAinv k hk hOMEGAinv_half ( j - l ) _ _ using 1;
        · exact Finset.sum_congr rfl fun _ _ => by ring;
        · grind;
        · exact lt_of_le_of_lt ( Nat.sub_le _ _ ) ( Fin.is_lt _ );
      convert congr_arg ( fun x : R => x * OMEGA ^ ( l.val * 0 ) * OMEGAinv ^ ( l.val * 0 ) ) h_ortho using 1 <;> ring;
      refine' Finset.sum_congr rfl fun i hi => _;
      rw [ show ( j : ℕ ) = l + ( j - l ) by rw [ Nat.add_sub_of_le ( le_of_not_gt h_cases ) ] ] ; ring;
      simp +decide [ ← mul_pow, hOMEGAinv ];
  simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_mul, orthogonality ];
  rw [ Finset.sum_comm, Finset.sum_congr rfl fun i hi => ?_ ];
  rotate_left;
  use fun i => x i * ∑ x_1 : Fin ( 2 ^ k ), OMEGA ^ ( i.val * x_1.val ) * OMEGAinv ^ ( j.val * x_1.val );
  · simp +decide only [mul_comm, Finset.mul_sum _ _ _];
  · rw [ Finset.sum_eq_single j ] <;> aesop

noncomputable def negacyclic_conv (K : ℕ) (a b : Fin K → ℤ) : Fin K → ℤ :=
  fun j =>
    ∑ l : Fin K, ∑ m : Fin K,
      if (l.val + m.val) % K = j.val then
        (if l.val + m.val < K then a l * b m else -(a l * b m))
      else 0

-- Generic CommRing version of negacyclic_conv (for ZMod use).
noncomputable def negacyclic_conv_R {R : Type*} [CommRing R] (K : ℕ) (a b : Fin K → R) : Fin K → R :=
  fun j =>
    ∑ l : Fin K, ∑ m : Fin K,
      if (l.val + m.val) % K = j.val then
        (if l.val + m.val < K then a l * b m else -(a l * b m))
      else 0

lemma ntt_full_chain_comm_ring {R : Type*} [CommRing R]
    (OMEGA OMEGAinv THETA THETAinv : R) (k : ℕ) (hk : 0 < k)
    (hOMEGA_half : OMEGA ^ (2 ^ (k - 1)) = -1)
    (hOMEGAK : OMEGA ^ (2 ^ k) = 1)
    (hOMEGAinv : OMEGA * OMEGAinv = 1)
    (hTHETAK : THETA ^ (2 ^ k) = -1)
    (hTHETAinv : THETA * THETAinv = 1)
    (Kinv : R) (hKinv : (2 ^ k : ℕ) • Kinv = 1)
    (a b : Fin (2 ^ k) → R) (j : Fin (2 ^ k)) :
    (∑ i : Fin (2 ^ k),
      (∑ l : Fin (2 ^ k), a l * THETA ^ l.val * OMEGA ^ (l.val * i.val)) *
      (∑ l : Fin (2 ^ k), b l * THETA ^ l.val * OMEGA ^ (l.val * i.val)) *
      OMEGAinv ^ (i.val * j.val)) * Kinv * THETAinv ^ j.val =
    negacyclic_conv_R (2 ^ k) a b j := by
  unfold negacyclic_conv_R
  have := @ntt_inverse_property_pow2 R;
  specialize this OMEGA OMEGAinv k hk hOMEGA_half hOMEGAK hOMEGAinv ( fun i => ∑ l : Fin ( 2 ^ k ), ∑ m : Fin ( 2 ^ k ), if ( l.val + m.val ) % 2 ^ k = i.val then ( a l * THETA ^ l.val ) * ( b m * THETA ^ m.val ) else 0 ) j;
  convert congr_arg ( · * Kinv * THETAinv ^ ( j.val : ℕ ) ) this.symm using 1;
  · congr! 3;
    exact congr_arg₂ _ ( by simpa only [ Finset.sum_mul _ _ _ ] using ntt_pointwise_product_eq_conv OMEGA k hk hOMEGA_half hOMEGAK _ _ _ ) rfl;
  · rw [ mul_assoc, ← weighted_conv_eq_negacyclic THETA THETAinv k hk hTHETAK hTHETAinv a b j ];
    grind +splitImp

-- ====================================================================
-- DECOMPOSE / NEGACYCLIC BOUNDS (unchanged)
-- ====================================================================

lemma decompose_digit_lt (A b K : ℕ) (hb : 0 < b) (j : Fin K) (hj : j.val < K - 1) :
    decompose A b K j < b := by
  unfold decompose; simp [hj]; exact Nat.mod_lt _ hb

lemma decompose_digit_le (A b K : ℕ) (hK : 0 < K) (hb : 0 < b)
    (hA : A < b ^ K + 1) (j : Fin K) :
    decompose A b K j ≤ b := by
  unfold decompose;
  split_ifs;
  · exact Nat.le_of_lt ( Nat.mod_lt _ hb );
  · rcases K with ( _ | _ | K ) <;> simp_all +decide [ Nat.pow_succ' ];
    exact Nat.div_le_of_le_mul <| by nlinarith;

lemma negacyclic_pos_term_strict (A B b K : ℕ) (hK : 1 < K) (hb : 0 < b)
    (hA : A < b ^ K + 1) (hB : B < b ^ K + 1)
    (l m : Fin K) (hlm : l.val + m.val < K) :
    (decompose A b K l : ℤ) * (decompose B b K m : ℤ) < (b : ℤ) ^ 2 := by
  have h_l_lt_b : (decompose A b K l : ℤ) < b ∨ (decompose B b K m : ℤ) < b := by
    by_cases hl : l.val < K - 1;
    · exact Or.inl <| mod_cast decompose_digit_lt A b K hb l hl;
    · exact Or.inr ( mod_cast decompose_digit_lt B b K hb m <| by omega );
  cases h_l_lt_b <;> nlinarith [ show ( decompose A b K l : ℤ ) ≤ b by exact_mod_cast decompose_digit_le A b K ( by linarith ) hb hA l, show ( decompose B b K m : ℤ ) ≤ b by exact_mod_cast decompose_digit_le B b K ( by linarith ) hb hB m ]

lemma negacyclic_decompose_strict_pos_bound (A B b K : ℕ) (hK : 1 < K) (hb : 0 < b)
    (hA : A < b ^ K + 1) (hB : B < b ^ K + 1)
    (j : Fin K) :
    negacyclic_conv K (fun j => (decompose A b K j : ℤ))
      (fun j => (decompose B b K j : ℤ)) j
    < (j.val + 1) * (b : ℤ) ^ 2 := by
  refine' lt_of_le_of_lt ( Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun m hm => _ ) _;
  exact fun i m => if ( i + m : ℕ ) % K = j.val then if ( i + m : ℕ ) < K then ( b : ℤ ) ^ 2 - 1 else 0 else 0;
  · split_ifs <;> norm_num;
    · exact negacyclic_pos_term_strict A B b K hK hb hA hB i m ‹_›;
    · exact mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ );
  · refine' lt_of_le_of_lt ( Finset.sum_le_sum fun x hx => _ ) _;
    use fun x => if x.val ≤ j.val then ( b : ℤ ) ^ 2 - 1 else 0;
    · split_ifs;
      · rw [ Finset.sum_eq_single ( ⟨ j - x, by omega ⟩ : Fin K ) ] <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        intro y hy₁ hy₂ hy₃; rw [ Nat.mod_eq_of_lt hy₃ ] at hy₂; simp_all +decide [ Fin.ext_iff ] ;
        omega;
      · refine' Finset.sum_nonpos fun y hy => _;
        split_ifs <;> norm_num;
        linarith [ Nat.mod_eq_of_lt ‹_› ];
    · norm_num [ Finset.sum_ite ];
      rw [ show ( Finset.univ.filter fun x : Fin K => x ≤ j ) = Finset.Iic j by ext; simp +decide ] ; norm_num

lemma negacyclic_coeff_neg_bound (K : ℕ) (hK : 0 < K)
    (a b : Fin K → ℤ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (ha' : ∀ j, a j ≤ C) (hb' : ∀ j, b j ≤ C)
    (j : Fin K) :
    -(↑(K - 1 - j.val) * C ^ 2) ≤ negacyclic_conv K a b j := by
  have h_sum_pairs : ∑ l : Fin K, ∑ m : Fin K, (if (l.val + m.val) % K = j.val ∧ l.val + m.val ≥ K then -(a l * b m) else 0) ≥ -(K - 1 - j.val) * C ^ 2 := by
    have h_card_pairs : Finset.card (Finset.filter (fun p : Fin K × Fin K => p.1.val + p.2.val = j.val + K) (Finset.univ : Finset (Fin K × Fin K))) ≤ K - 1 - j.val := by
      rw [ Finset.card_eq_of_bijective ];
      use fun i hi => ⟨ ⟨ i + j.val + 1, by omega ⟩, ⟨ K - 1 - i, by omega ⟩ ⟩;
      · simp +zetaDelta at *;
        intro a b hab;
        refine' ⟨ a - j - 1, _, _ ⟩ <;> norm_num [ Fin.ext_iff ];
        · omega;
        · omega;
      · grind;
      · aesop;
    have h_contribution : ∑ p ∈ Finset.filter (fun p : Fin K × Fin K => p.1.val + p.2.val = j.val + K) (Finset.univ : Finset (Fin K × Fin K)), -(a p.1 * b p.2) ≥ -(K - 1 - j.val) * C ^ 2 := by
      refine' le_trans _ ( Finset.sum_le_sum fun p hp => show - ( a p.1 * b p.2 ) ≥ -C ^ 2 from _ );
      · norm_num;
        nlinarith [ show ( Finset.card ( Finset.filter ( fun p : Fin K × Fin K => ( p.1 : ℕ ) + p.2 = j + K ) Finset.univ ) : ℤ ) ≤ K - 1 - j from by omega ];
      · nlinarith only [ ha p.1, hb p.2, ha' p.1, hb' p.2 ];
    refine le_trans h_contribution ?_;
    rw [ ← Finset.sum_product' ];
    rw [ ← Finset.sum_filter ];
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_;
    · intro p hp; simp_all +decide [ Nat.mod_eq_of_lt ] ;
    · simp +zetaDelta at *;
      intro i j hij hK hne; contrapose! hne;
      rw [ ← hij, Nat.mod_eq_sub_mod hK ];
      rw [ Nat.mod_eq_of_lt ] <;> omega;
  simp_all +decide [ negacyclic_conv ];
  convert h_sum_pairs.trans _ using 1;
  · rw [ Nat.cast_sub <| Nat.le_sub_one_of_lt <| Fin.is_lt j ] ; rw [ Nat.cast_sub <| by linarith [ Fin.is_lt j ] ] ; push_cast ; ring;
  · gcongr with x y ; split_ifs <;> first | linarith | simp_all +decide [ Nat.mod_eq_of_lt ] ;
    exact mul_nonneg ( ha _ ) ( hb _ )

lemma fermat_ext_gt_K_mul_sq (BASE k M : ℕ) (n' : ℕ)
    (hBASE : 2 ≤ BASE) (hM : 0 < M)
    (hn' : n' ≥ 2 * M + k) :
    2 ^ k * (BASE ^ M) ^ 2 < fermat_ext BASE n' := by
  have h_exp_ge : BASE^n' ≥ BASE^(2*M + k) := by
    exact Nat.pow_le_pow_right ( by linarith ) hn';
  have h_exp_ge_simplified : BASE^n' ≥ (BASE^M)^2 * 2^k := by
    exact le_trans ( by rw [ pow_add, pow_mul' ] ; gcongr ) h_exp_ge;
  exact lt_add_of_le_of_pos ( by simpa only [ mul_comm ] using h_exp_ge_simplified ) zero_lt_one

lemma correction_exact (cj neg_conv F threshold : ℤ)
    (hF_pos : 0 < F)
    (hcj_lo : 0 ≤ cj) (hcj_hi : cj < F)
    (hcong : F ∣ (cj - neg_conv))
    (h_pos_bound : neg_conv < threshold)
    (h_neg_bound : -(F - threshold) < neg_conv)
    (h_threshold_pos : 0 ≤ threshold)
    (h_threshold_lt : threshold ≤ F) :
    (if cj ≥ threshold then cj - F else cj) = neg_conv := by
  by_cases h_case : cj ≥ threshold;
  · obtain ⟨ k, hk ⟩ := hcong;
    split_ifs ; nlinarith [ show k = 1 by nlinarith ];
  · cases' hcong with k hk ; split_ifs at * ; nlinarith [ show k = 0 by nlinarith ]

lemma h_neg_helper (K : ℕ) (C F : ℤ) (j : Fin K)
    (hF_gt : ↑K * C^2 < F)
    (neg_conv : ℤ)
    (h_neg_bound : -(↑(K - 1 - j.val) * C^2) ≤ neg_conv) :
    -(F - ↑(j.val + 1) * C^2) < neg_conv := by
  have hK_eq : (↑(K - 1 - j.val) : ℤ) + ↑(j.val + 1) = ↑K := by push_cast; omega
  nlinarith [sq_nonneg C]

-- ====================================================================
-- CLAUDE
-- ====================================================================

-- Simpler proof using existing pattern from old file:
lemma base_isUnit_zmod' (BASE n' : ℕ) (hn'_pos : 0 < n') :
    IsUnit ((BASE : ZMod (fermat_ext BASE n'))) := by
  have h_neg_one : (BASE : ZMod (fermat_ext BASE n')) ^ n' = -1 :=
    base_pow_eq_neg_one_mod_fermat_ext BASE n'
  have h_neg_unit : IsUnit ((BASE : ZMod (fermat_ext BASE n')) ^ n') := by
    rw [h_neg_one]; exact isUnit_one.neg
  exact isUnit_of_dvd_unit (dvd_pow_self _ hn'_pos.ne') h_neg_unit

-- 2^k is a unit in ZMod (fermat_ext BASE n') when BASE is even and n' ≥ 1.
lemma K_isUnit_zmod (BASE n' k : ℕ) (hBASE_even : Even BASE) (hn'_pos : 0 < n') :
    IsUnit ((2 ^ k : ℕ) : ZMod (fermat_ext BASE n')) := by
  have hF_odd : ¬ (2 ∣ fermat_ext BASE n') := by
    unfold fermat_ext
    intro ⟨c, hc⟩
    have hBASE_dvd : 2 ∣ BASE ^ n' := by
      obtain ⟨r, hr⟩ := hBASE_even
      exact dvd_pow ⟨r, by linarith⟩ hn'_pos.ne'
    obtain ⟨d, hd⟩ := hBASE_dvd
    have : 2 ∣ 1 := ⟨c - d, by grind⟩
    omega
  have h_coprime : Nat.Coprime (2 ^ k) (fermat_ext BASE n') := by
    apply Nat.Coprime.pow_left
    exact (Nat.prime_two.coprime_iff_not_dvd).mpr hF_odd
  exact (ZMod.isUnit_iff_coprime _ _).mpr h_coprime

-- (BETA : ZMod F)^j cast as Int via .val agrees with (BETA^j : Nat) cast via Int → ZMod (mod F).
-- Used to lift Int-valued recompositions into ZMod recompositions.
lemma zmod_int_cast_natCast (m : ℕ) [NeZero m] (n : ℕ) :
    ((n : Int) : ZMod m) = ((n : Nat) : ZMod m) := by
  push_cast; rfl

-- Decompose-sum lifted into ZMod F_outer.
lemma decompose_sum_zmod {F_outer : ℕ} [NeZero F_outer]
    (A b K : ℕ) (hK : 0 < K) :
    ∑ j : Fin K, ((decompose A b K j : Int) : ZMod F_outer) * ((b : ZMod F_outer) ^ j.val) =
    ((A : Nat) : ZMod F_outer) := by
  have h := decompose_sum A b K hK
  have : ((A : Nat) : ZMod F_outer) =
         ((∑ j : Fin K, (decompose A b K j) * b ^ j.val : Nat) : ZMod F_outer) := by
    rw [h]
  rw [this]
  push_cast
  rfl

-- The "good_n_bigger_than_log" condition: when n is large enough, log₂ n ≥ 4.
lemma log_two_n_ge_four_of_large (n : ℕ) (hn : ¬ n < 16) : Nat.log 2 n ≥ 4 := by
  have : n ≥ 16 := by omega
  have : (2 : ℕ) ^ 4 ≤ n := by norm_num; omega
  exact (Nat.le_log_iff_pow_le (by norm_num : 1 < 2) (by omega : n ≠ 0)).mpr this



-- ====================================================================
-- Lift integer-valued negacyclic conv into ZMod via the cast.
-- ====================================================================

lemma negacyclic_conv_cast_eq {F : ℕ} [NeZero F] (K : ℕ)
    (a b : Fin K → ZMod F) (j : Fin K) :
    ((negacyclic_conv K (fun l => ((a l).val : ℤ)) (fun l => ((b l).val : ℤ)) j : ℤ) : ZMod F) =
    negacyclic_conv_R K a b j := by
  unfold negacyclic_conv negacyclic_conv_R
  push_cast
  apply Finset.sum_congr rfl; intro l _
  apply Finset.sum_congr rfl; intro m _
  by_cases hmod : (l.val + m.val) % K = j.val
  · by_cases hlt : l.val + m.val < K
    · simp [hmod, hlt]
    · simp [hmod, hlt]
  · simp [hmod]

/-
====================================================================
KEY ALGEBRAIC IDENTITY: negacyclic conv recomposed = product
====================================================================

In ZMod F where b^K = -1, the recomposition of the negacyclic convolution
of two sequences equals the product of their recompositions.
-/
lemma negacyclic_recompose_eq_mul {F : ℕ} [NeZero F]
    (K : ℕ) (hK : 0 < K)
    (b : ℕ) (hb_neg : (b : ZMod F) ^ K = -1)
    (a c : Fin K → ℤ) :
    (recompose_zmod (negacyclic_conv K a c) b : ZMod F) =
    (recompose_zmod a b : ZMod F) * (recompose_zmod c b : ZMod F) := by
  unfold recompose_zmod negacyclic_conv;
  simp +decide [ Finset.sum_mul _ _ _, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm, Finset.sum_add_distrib ];
  rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => _;
  rw [ Finset.sum_eq_single ⟨ ( i + j ) % K, Nat.mod_lt _ hK ⟩ ] <;> simp +decide [ ← pow_add ];
  · split_ifs <;> simp_all +decide [ ← mul_assoc, ← pow_add ];
    · rw [ Nat.mod_eq_of_lt ‹_› ];
    · rw [ ← Nat.mod_add_div ( i + j ) K ] ; simp_all +decide [ pow_add, pow_mul ] ;
      rcases Nat.even_or_odd' ( ( i + j ) / K ) with ⟨ k, hk | hk ⟩ <;> simp_all +decide [ pow_add, pow_mul ];
      have := Nat.div_add_mod ( i + j ) K; simp_all +decide [ Nat.mod_eq_of_lt ] ;
      rcases k with ( _ | k ) <;> simp_all +decide [ Nat.mul_succ, pow_succ' ];
      · grind;
      · nlinarith [ Fin.is_lt i, Fin.is_lt j, Nat.zero_le ( ( i + j ) % K ), Nat.mod_lt ( i + j ) hK ];
  · exact fun k hk₁ hk₂ => False.elim <| hk₁ <| Fin.ext hk₂.symm

/-
BETA'^K = -1 in ZMod (fermat_ext BASE n) when K * M = n
-/
lemma BETA'_pow_K_eq_neg_one (BASE n : ℕ) (K M : ℕ) (hKM : K * M = n) :
    ((BASE ^ M : ℕ) : ZMod (fermat_ext BASE n)) ^ K = -1 := by
  -- By definition of fermat_ext, we know that fermat_ext BASE n = (BASE ^ M) ^ K + 1.
  have h_fermat_ext : fermat_ext BASE n = (BASE ^ M) ^ K + 1 := by
    rw [ ← hKM, fermat_ext_eq_pow_pow ];
  rw [ eq_neg_iff_add_eq_zero ];
  norm_cast;
  erw [ ZMod.natCast_eq_zero_iff ] ; aesop


-- ====================================================================
-- RECURSIVE CASE LEMMA
-- ====================================================================

-- Helper: natCast of ZMod.val is identity
lemma zmod_natCast_val_eq {n : ℕ} [NeZero n] (x : ZMod n) : ((x.val : ℕ) : ZMod n) = x :=
  ZMod.val_injective n (ZMod.val_natCast_of_lt (ZMod.val_lt x))

-- If x = (z : ZMod m), then m | (x.val - z) as integers
lemma zmod_eq_int_dvd {m : ℕ} [NeZero m] (x : ZMod m) (z : ℤ)
    (h : x = ((z : ℤ) : ZMod m)) : (↑m : ℤ) ∣ ((x.val : ℤ) - z) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have : ((x.val : ℕ) : ZMod m) = x := zmod_natCast_val_eq x
  push_cast
  rw [this, h, sub_self]

-- NTT chain with correct pointwise products gives negacyclic convolution
lemma ntt_chain_eq_negacyclic_conv_R
    {F : ℕ} [NeZero F]
    (OMEGA OMEGAInv THETA THETAInv KInv : ZMod F)
    (k : ℕ) (hk : 0 < k)
    (hOMEGA_half : OMEGA ^ (2 ^ (k - 1)) = -1)
    (hOMEGAK : OMEGA ^ (2 ^ k) = 1)
    (hOMEGAInv : OMEGA * OMEGAInv = 1)
    (hTHETAK : THETA ^ (2 ^ k) = -1)
    (hTHETAInv : THETA * THETAInv = 1)
    (hKInv : (2 ^ k : ℕ) • KInv = 1)
    (aD bD : Fin (2 ^ k) → ZMod F)
    (cF : Fin (2 ^ k) → ZMod F)
    (hcF : ∀ i, cF i =
      (NTT_zmod (fun j => aD j * THETA ^ j.val) OMEGA i) *
      (NTT_zmod (fun j => bD j * THETA ^ j.val) OMEGA i))
    (j : Fin (2 ^ k)) :
    (NTT_zmod cF OMEGAInv j) * KInv * THETAInv ^ j.val =
    negacyclic_conv_R (2 ^ k) aD bD j := by
  have h2 : ∀ i : Fin (2^k),
    cF i =
    (∑ l : Fin (2^k), aD l * THETA ^ l.val * OMEGA ^ (l.val * i.val)) *
    (∑ l : Fin (2^k), bD l * THETA ^ l.val * OMEGA ^ (l.val * i.val)) := by
    intro i; rw [hcF i]; simp only [NTT_zmod]
  simp only [NTT_zmod]
  simp_rw [h2]
  exact ntt_full_chain_comm_ring OMEGA OMEGAInv THETA THETAInv k hk
    hOMEGA_half hOMEGAK hOMEGAInv hTHETAK hTHETAInv KInv hKInv aD bD j

-- Helper: decompose values are < fermat_ext BASE n'
lemma decompose_lt_fermat (A BASE M K n' : ℕ)
    (hBASE_ge : 2 ≤ BASE) (hM_pos : 0 < M) (hn'_ge_M : M ≤ n')
    (hK_pos : 0 < K)
    (hA : A < (BASE^M)^K + 1)
    (l : Fin K) :
    decompose A (BASE^M) K l < fermat_ext BASE n' := by
  have h1 : decompose A (BASE^M) K l ≤ BASE^M :=
    decompose_digit_le A (BASE^M) K hK_pos (by positivity) hA l
  have h2 : BASE^M ≤ BASE^n' := Nat.pow_le_pow_right (by omega) hn'_ge_M
  have h3 : BASE^n' < fermat_ext BASE n' := by unfold fermat_ext; omega
  omega




private lemma two_pow_succ_eq (k' : Nat) : (2:Nat)^(k'+1) = 2 * 2^k' := by
  simp [pow_succ 2 k']; ring
private lemma even_idx_lt (k' : Nat) (j : Fin (2^k')) : 2 * j.val < 2^(k'+1) := by
  have := two_pow_succ_eq k'; omega
private lemma odd_idx_lt (k' : Nat) (j : Fin (2^k')) : 2 * j.val + 1 < 2^(k'+1) := by
  have := two_pow_succ_eq k'; omega

-- ====================================================================
-- NTT Cooley-Tukey decomposition lemmas
-- ====================================================================
lemma ntt_zmod_cooley_tukey_first_half {k' : Nat} {F : Nat} [NeZero F]
    (x : Fin (2^(k'+1)) → ZMod F) (omega : ZMod F)
    (i : Fin (2^k')) :
    NTT_zmod x omega ⟨i.val, by have := i.isLt; have := two_pow_succ_eq k'; omega⟩ =
    (∑ j : Fin (2^k'), x ⟨2 * j.val, even_idx_lt k' j⟩ *
      (omega^2) ^ (j.val * i.val)) +
    omega ^ i.val *
    (∑ j : Fin (2^k'), x ⟨2 * j.val + 1, odd_idx_lt k' j⟩ *
      (omega^2) ^ (j.val * i.val)) := by
  unfold NTT_zmod;
  rw [ Finset.mul_sum _ _ _ ];
  rw [ show ( Finset.univ : Finset ( Fin ( 2 ^ ( k' + 1 ) ) ) ) = Finset.image ( fun j : Fin ( 2 ^ k' ) => ⟨ 2 * j, by
        rw [ pow_succ' ] ; linarith [ Fin.is_lt j ] ⟩ ) Finset.univ ∪ Finset.image ( fun j : Fin ( 2 ^ k' ) => ⟨ 2 * j + 1, by
        exact odd_idx_lt k' j ⟩ ) Finset.univ from ?_, Finset.sum_union ];
  · rw [ Finset.sum_image, Finset.sum_image ] <;> norm_num [ Fin.ext_iff, pow_mul' ];
    · exact congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun _ _ => by ring ) ( Finset.sum_congr rfl fun _ _ => by ring );
    · exact fun a b h => by simpa [ Fin.ext_iff ] using h;
    · exact fun a b h => by simpa [ Fin.ext_iff ] using h;
  · norm_num [ Finset.disjoint_left ];
    exact fun a x => ne_of_apply_ne ( fun n => n % 2 ) ( by norm_num [ Nat.add_mod, Nat.mul_mod ] );
  · ext ⟨ j, hj ⟩ ; simp +decide [ Fin.ext_iff ];
    rcases Nat.even_or_odd' j with ⟨ c, rfl | rfl ⟩ <;> [ left; right ] <;> use ⟨ c, by linarith [ pow_succ' 2 k' ] ⟩
lemma ntt_zmod_cooley_tukey_second_half {k' : Nat} {F : Nat} [NeZero F]
    (x : Fin (2^(k'+1)) → ZMod F) (omega : ZMod F)
    (hω : omega ^ (2^k') = -1)
    (i : Fin (2^k')) :
    NTT_zmod x omega ⟨i.val + 2^k', by have := i.isLt; have := two_pow_succ_eq k'; omega⟩ =
    (∑ j : Fin (2^k'), x ⟨2 * j.val, even_idx_lt k' j⟩ *
      (omega^2) ^ (j.val * i.val)) -
    omega ^ i.val *
    (∑ j : Fin (2^k'), x ⟨2 * j.val + 1, odd_idx_lt k' j⟩ *
      (omega^2) ^ (j.val * i.val)) := by
  have h_split : ∑ m : Fin (2 ^ (k' + 1)), x m * omega ^ (m.val * (i.val + 2 ^ k')) =
    (∑ j : Fin (2 ^ k'), x ⟨2 * j.val, even_idx_lt k' j⟩ * omega ^ ((2 * j.val) * (i.val + 2 ^ k'))) +
    (∑ j : Fin (2 ^ k'), x ⟨2 * j.val + 1, odd_idx_lt k' j⟩ * omega ^ ((2 * j.val + 1) * (i.val + 2 ^ k'))) := by
      have h_split : Finset.range (2 ^ (k' + 1)) = Finset.image (fun j => 2 * j) (Finset.range (2 ^ k')) ∪ Finset.image (fun j => 2 * j + 1) (Finset.range (2 ^ k')) := by
        ext j
        simp [Finset.mem_range, Finset.mem_image];
        exact ⟨ fun hj => by rcases Nat.even_or_odd' j with ⟨ c, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ c, by rw [ pow_succ' ] at hj; linarith, rfl ⟩, fun hj => by rcases hj with ( ⟨ c, hc, rfl ⟩ | ⟨ c, hc, rfl ⟩ ) <;> rw [ pow_succ' ] <;> linarith ⟩;
      rw [ Finset.sum_fin_eq_sum_range ];
      rw [ h_split, Finset.sum_union ];
      · norm_num [ Finset.sum_range, Nat.lt_succ_iff ];
        grind;
      · norm_num [ Finset.disjoint_right ];
        intros; omega;
  convert h_split using 1;
  norm_num [ pow_add, pow_mul', mul_assoc, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
  simp_all +decide [ mul_pow, pow_right_comm ];
  ring;
  norm_num [ pow_mul', mul_assoc, mul_comm, mul_left_comm ]
-- ====================================================================
-- FFT = NTT_zmod
-- ====================================================================
lemma FFT_eq_NTT_zmod {k : Nat} {F : Nat} [NeZero F]
    (x : Fin (2^k) → ZMod F) (omega : ZMod F)
    (hk : 0 < k)
    (hω_half : omega ^ (2^(k-1)) = -1) :
    FFT x omega = NTT_zmod x omega := by
  revert hk hω_half x omega;
  induction' k with k ih;
  · tauto;
  · intro x omega hk hω_half
    funext i;
    by_cases hi : i.val < 2 ^ k <;> simp_all +decide [ Fin.add_def, two_pow_succ_eq ];
    · by_cases hk : 0 < k <;> simp_all +decide [ pow_succ' ];
      · rw [ show FFT x omega i = FFT ( fun j => x ⟨ 2 * j.val, even_idx_lt k j ⟩ ) ( omega ^ 2 ) ⟨ i.val, hi ⟩ + omega ^ i.val * FFT ( fun j => x ⟨ 2 * j.val + 1, odd_idx_lt k j ⟩ ) ( omega ^ 2 ) ⟨ i.val, hi ⟩ from ?_ ];
        · rw [ ih, ih ];
          · convert ntt_zmod_cooley_tukey_first_half x omega ⟨ i.val, hi ⟩ |> Eq.symm using 1;
          · cases k <;> simp_all +decide [ pow_succ', pow_mul ];
          · cases k <;> simp_all +decide [ pow_succ', pow_mul ];
        · rw [ FFT ];
          simp +decide [ Nat.mod_eq_of_lt hi ];
          grind +locals;
      · unfold FFT NTT_zmod; aesop;
    · obtain ⟨j, hj⟩ : ∃ j : Fin (2 ^ k), i = ⟨j.val + 2 ^ k, by
        rw [ pow_succ' ] ; linarith [ Fin.is_lt j ]⟩ := by
        exact ⟨ ⟨ i - 2 ^ k, by rw [ tsub_lt_iff_left hi ] ; linarith [ Fin.is_lt i, pow_succ' 2 k ] ⟩, by erw [ Fin.ext_iff ] ; simp +decide [ Nat.sub_add_cancel hi ] ⟩
      generalize_proofs at *;
      by_cases hk : 0 < k <;> simp_all +decide [ pow_succ' ];
      · rw [ FFT ];
        simp +decide [ Nat.mod_eq_of_lt, hk, hω_half ];
        rw [ ntt_zmod_cooley_tukey_second_half ];
        · rw [ ih, ih ];
          · unfold NTT_zmod; ring;
          · rw [ ← pow_mul, ← pow_succ', Nat.sub_add_cancel hk, hω_half ];
          · rw [ ← pow_mul, ← pow_succ', Nat.sub_add_cancel hk, hω_half ];
        · exact hω_half;
      · unfold FFT NTT_zmod; aesop;


noncomputable def schonhage_strassen_FFT
(BETA A B n : Nat)
(hA : A < fermat_ext BETA n)
(hB : B < fermat_ext BETA n)
(hBETA : Even BETA)
(hn : good_n n)
: Nat :=
  if _hn : n < 16 then
    (A * B) % (fermat_ext BETA n)
  else
    let k := Nat.min (Classical.choose hn) ((Nat.log 2 n) - 1)
    let K := 2 ^ k
    let M := n / K
    let BETA' := BETA ^ M
    have h_exists_n' : ∃ n' : Nat,
        (n' ≥ 2*M + k) ∧ (n' < n) ∧ (good_n n') ∧ (2^k ∣ n') :=
      exists_suitable_n' n hn _hn
    let n' := Classical.choose h_exists_n'
    let THETA    : ZMod (fermat_ext BETA n') := (BETA : ZMod (fermat_ext BETA n')) ^ (n' / K)
    let OMEGA    : ZMod (fermat_ext BETA n') := THETA ^ 2
    let THETAInv : ZMod (fermat_ext BETA n') := THETA⁻¹
    let OMEGAInv : ZMod (fermat_ext BETA n') := OMEGA⁻¹
    let KInv     : ZMod (fermat_ext BETA n') := ((K : Nat) : ZMod (fermat_ext BETA n'))⁻¹
    let aD : Fin K → ZMod (fermat_ext BETA n') :=
      fun j => ((decompose A BETA' K j : Nat) : ZMod (fermat_ext BETA n'))
    let bD : Fin K → ZMod (fermat_ext BETA n') :=
      fun j => ((decompose B BETA' K j : Nat) : ZMod (fermat_ext BETA n'))
    let aT : Fin K → ZMod (fermat_ext BETA n') := fun j => aD j * THETA ^ j.val
    let bT : Fin K → ZMod (fermat_ext BETA n') := fun j => bD j * THETA ^ j.val
    let aF : Fin K → ZMod (fermat_ext BETA n') := FFT aT OMEGA
    let bF : Fin K → ZMod (fermat_ext BETA n') := FFT bT OMEGA
    have h_good_n' : good_n n' := by grind
    have hA' : ∀ j, (aF j).val < fermat_ext BETA n' := fun j => ZMod.val_lt _
    have hB' : ∀ j, (bF j).val < fermat_ext BETA n' := fun j => ZMod.val_lt _
    let cF : Fin K → ZMod (fermat_ext BETA n') := fun j =>
      ((schonhage_strassen_FFT BETA (aF j).val (bF j).val n'
         (hA' j) (hB' j) hBETA h_good_n' : Nat) : ZMod (fermat_ext BETA n'))
    let cB : Fin K → ZMod (fermat_ext BETA n') := FFT cF OMEGAInv
    let cFinZ : Fin K → ZMod (fermat_ext BETA n') := fun j =>
      cB j * KInv * THETAInv ^ j.val
    let cFin : Fin K → Int := fun j =>
      sign_recover (cFinZ j) (Int.ofNat (j.val + 1) * (BETA' : Int) ^ 2)
    let result : ZMod (fermat_ext BETA n) := recompose_zmod cFin BETA'
    result.val
termination_by n
decreasing_by
  exact (Classical.choose_spec h_exists_n').2.1
-- ====================================================================
-- Helper: IH for FFT version gives correct pointwise products
-- ====================================================================
lemma ih_gives_product_fft (BASE n n' : ℕ) (hBASE : Even BASE)
    (hn'_good : good_n n') (hn'_lt : n' < n)
    (ih : ∀ m, m < n → ∀ A B, ∀ hnk : good_n m,
      ∀ hA : A < fermat_ext BASE m, ∀ hB : B < fermat_ext BASE m,
      schonhage_strassen_FFT BASE A B m hA hB hBASE hnk =
        (A * B) % fermat_ext BASE m)
    (a b : ZMod (fermat_ext BASE n')) :
    ((schonhage_strassen_FFT BASE a.val b.val n'
      (ZMod.val_lt a) (ZMod.val_lt b) hBASE hn'_good : ℕ) : ZMod (fermat_ext BASE n')) =
    a * b := by
  rw [ih n' hn'_lt]
  rw [ZMod.natCast_mod, Nat.cast_mul, zmod_natCast_val_eq, zmod_natCast_val_eq]
/-
====================================================================
Helper: OMEGAInv half condition
====================================================================
-/
lemma omega_inv_half_eq_neg_one {F : Nat} [NeZero F]
    (OMEGA : ZMod F) (k : Nat) (hk : 0 < k)
    (hOMEGA_half : OMEGA ^ (2^(k-1)) = -1)
    (hOMEGA_unit : IsUnit OMEGA) :
    OMEGA⁻¹ ^ (2^(k-1)) = -1 := by
  -- By multiplying both sides of the equation OMEGA^(2^(k-1)) = -1 by OMEGA⁻¹^(2^(k-1)), we get 1 = -OMEGA⁻¹^(2^(k-1)).
  have h_mul_inv : OMEGA ^ (2 ^ (k - 1)) * OMEGA⁻¹ ^ (2 ^ (k - 1)) = 1 := by
    obtain ⟨ u, hu ⟩ := hOMEGA_unit;
    simp +decide [ ← mul_pow, ← hu ];
  grind
-- ====================================================================
-- Direct correctness proof
-- ====================================================================
lemma schonhage_strassen_FFT_recursive
    (BASE : ℕ) (hBASE : Even BASE) (hBASE_ge : 2 ≤ BASE)
    (n : ℕ) (h_large : ¬ n < 16) (A B : ℕ) (hnk : good_n n)
    (hA : A < fermat_ext BASE n) (hB : B < fermat_ext BASE n)
    (ih : ∀ m, m < n → ∀ A B, ∀ hnk : good_n m,
      ∀ hA : A < fermat_ext BASE m, ∀ hB : B < fermat_ext BASE m,
      schonhage_strassen_FFT BASE A B m hA hB hBASE hnk =
        (A * B) % fermat_ext BASE m) :
    schonhage_strassen_FFT BASE A B n hA hB hBASE hnk =
      (A * B) % fermat_ext BASE n := by
  set output := schonhage_strassen_FFT BASE A B n hA hB hBASE hnk with output_def
  rw [schonhage_strassen_FFT.eq_1, dif_neg h_large] at output_def
  have h_lt : output < fermat_ext BASE n := by rw [output_def]; exact ZMod.val_lt _
  have h_zmod : (output : ZMod (fermat_ext BASE n)) =
      ((A * B : ℕ) : ZMod (fermat_ext BASE n)) := by
    rw [output_def]
    simp only [zmod_natCast_val_eq]
    set k := (Classical.choose hnk).min (Nat.log 2 n - 1) with k_def
    set K := 2 ^ k with K_def
    set M := n / K with M_def
    set BETA' := BASE ^ M with BETA'_def
    have hk_ge : 2 ≤ k := Nat.le_min.mpr ⟨(Classical.choose_spec hnk).1,
      Nat.le_sub_one_of_lt (Nat.le_log_of_pow_le (by decide) (by omega))⟩
    have hk_pos : 0 < k := by omega
    have hKdvd : K ∣ n := dvd_trans (pow_dvd_pow 2 (Nat.min_le_left _ _)) (Classical.choose_spec hnk).2
    have hKM : K * M = n := Nat.mul_div_cancel' hKdvd
    have hK_gt : 1 < K := by rw [K_def]; exact one_lt_pow₀ (by norm_num) (by omega)
    have hM_pos : 0 < M := Nat.div_pos (Nat.le_of_dvd (by omega) hKdvd) (by positivity)
    set h_exists_n' := exists_suitable_n' n hnk h_large with h_exists_def
    set n' := Classical.choose h_exists_n' with n'_def
    have hn'_spec := Classical.choose_spec h_exists_n'
    have hn'_ge : n' ≥ 2 * M + k := hn'_spec.1
    have hn'_lt : n' < n := hn'_spec.2.1
    have hn'_good : good_n n' := hn'_spec.2.2.1
    have hn'_Kdvd : K ∣ n' := hn'_spec.2.2.2
    have hn'_pos : 0 < n' := by omega
    have hBETA'_neg : (BETA' : ZMod (fermat_ext BASE n)) ^ K = -1 :=
      BETA'_pow_K_eq_neg_one BASE n K M hKM
    -- OMEGA conditions
    set THETA_v := (BASE : ZMod (fermat_ext BASE n')) ^ (n' / K) with THETA_def
    set OMEGA_v := THETA_v ^ 2 with OMEGA_def
    have hTHETA_K : THETA_v ^ K = -1 :=
      theta_pow_K_eq_neg_one BASE n' K (by positivity) hn'_Kdvd
    have hOMEGA_half : OMEGA_v ^ (2 ^ (k - 1)) = -1 := by
      change (THETA_v ^ 2) ^ (2 ^ (k - 1)) = -1
      rw [← pow_mul]
      convert hTHETA_K using 2
      nth_rw 1 [show (2 : ℕ) = 2 ^ 1 from rfl]
      rw [← pow_add]; congr 1; omega
    have hOMEGA_K : OMEGA_v ^ K = 1 :=
      omega_pow_K_eq_one BASE n' K (by positivity) hn'_Kdvd
    have hTHETA_unit : IsUnit THETA_v :=
      (base_isUnit_zmod' BASE n' hn'_pos).pow (n' / K)
    have hOMEGA_unit : IsUnit OMEGA_v := hTHETA_unit.pow 2
    have hOMEGA_inv : OMEGA_v * OMEGA_v⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hOMEGA_unit
    have hTHETA_inv : THETA_v * THETA_v⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hTHETA_unit
    have hKInv : (2 ^ k : ℕ) • ((↑K : ZMod (fermat_ext BASE n'))⁻¹) = 1 := by
      rw [nsmul_eq_mul]
      exact ZMod.mul_inv_of_unit _ (K_isUnit_zmod BASE n' k hBASE hn'_pos)
    -- OMEGAInv half condition
    have hOMEGAInv_half : OMEGA_v⁻¹ ^ (2 ^ (k - 1)) = -1 :=
      omega_inv_half_eq_neg_one OMEGA_v k hk_pos hOMEGA_half hOMEGA_unit
    -- KEY: FFT = NTT_zmod for forward and inverse transforms
    have h_fft_fwd : ∀ (y : Fin K → ZMod (fermat_ext BASE n')),
        FFT y OMEGA_v = NTT_zmod y OMEGA_v :=
      fun y => FFT_eq_NTT_zmod y OMEGA_v hk_pos hOMEGA_half
    have h_fft_inv : ∀ (y : Fin K → ZMod (fermat_ext BASE n')),
        FFT y OMEGA_v⁻¹ = NTT_zmod y OMEGA_v⁻¹ :=
      fun y => FFT_eq_NTT_zmod y OMEGA_v⁻¹ hk_pos hOMEGAInv_half
    -- Step 1: negacyclic recomposition = A * B
    have h_neg_recomp :
        (recompose_zmod (negacyclic_conv K
          (fun j => (decompose A BETA' K j : ℤ))
          (fun j => (decompose B BETA' K j : ℤ))) BETA'
        : ZMod (fermat_ext BASE n)) = ↑(A * B) := by
      rw [negacyclic_recompose_eq_mul K (by positivity) BETA' hBETA'_neg]
      unfold recompose_zmod
      rw [decompose_sum_zmod A BETA' K (by positivity)]
      rw [decompose_sum_zmod B BETA' K (by positivity)]
      push_cast; ring
    rw [← h_neg_recomp]
    congr 1
    funext j
    set neg_conv_j := negacyclic_conv K (fun j => ↑(decompose A BETA' K j))
      (fun j => ↑(decompose B BETA' K j)) j with neg_conv_j_def
    unfold sign_recover
    simp only []
    apply correction_exact
    · exact_mod_cast fermat_ext_pos BASE n'
    · exact Int.ofNat_nonneg _
    · grind
    · -- F' | (cj - neg_conv_j)  (congruence)
      simp only [← BETA'_def, ← n'_def, ← K_def, ← M_def, ← k_def] at *
      apply zmod_eq_int_dvd
      -- The key step: use FFT_eq_NTT_zmod to convert FFTs to NTTs
      -- After rewriting, the forward FFTs become NTTs and we can use ntt_chain_eq_negacyclic_conv_R
      -- The cF values use ih_gives_product_fft (recursive call correctness via IH)
      have hcF_eq : ∀ i : Fin K,
        (fun j : Fin K =>
          ((schonhage_strassen_FFT BASE
            ((FFT (fun j => (↑(decompose A BETA' K j) : ZMod (fermat_ext BASE n')) * THETA_v ^ j.val) OMEGA_v) j).val
            ((FFT (fun j => (↑(decompose B BETA' K j) : ZMod (fermat_ext BASE n')) * THETA_v ^ j.val) OMEGA_v) j).val
            n' (ZMod.val_lt _) (ZMod.val_lt _) hBASE hn'_good : Nat) : ZMod (fermat_ext BASE n'))) i =
        (NTT_zmod (fun j => (↑(decompose A BETA' K j) : ZMod (fermat_ext BASE n')) * THETA_v ^ j.val) OMEGA_v i) *
        (NTT_zmod (fun j => (↑(decompose B BETA' K j) : ZMod (fermat_ext BASE n')) * THETA_v ^ j.val) OMEGA_v i) := by
        intro i
        rw [h_fft_fwd, h_fft_fwd]
        exact ih_gives_product_fft BASE n n' hBASE hn'_good hn'_lt ih _ _
      -- Now use ntt_chain_eq_negacyclic_conv_R
      -- We need to show that the inverse FFT + scaling gives the negacyclic conv
      -- The cB uses FFT on cF with OMEGAInv
      -- After rewriting FFT to NTT_zmod, this becomes the NTT inverse
      -- Which combined with the forward NTT chain gives negacyclic conv
      have h_chain := ntt_chain_eq_negacyclic_conv_R OMEGA_v OMEGA_v⁻¹ THETA_v THETA_v⁻¹
        ((↑K : ZMod (fermat_ext BASE n'))⁻¹) k hk_pos
        hOMEGA_half hOMEGA_K hOMEGA_inv hTHETA_K hTHETA_inv hKInv
        (fun l => ((↑(decompose A BETA' K l) : ZMod (fermat_ext BASE n'))))
        (fun l => ((↑(decompose B BETA' K l) : ZMod (fermat_ext BASE n'))))
        (fun i =>
          ((schonhage_strassen_FFT BASE
            ((FFT (fun j => (↑(decompose A BETA' K j) : ZMod (fermat_ext BASE n')) * THETA_v ^ j.val) OMEGA_v) i).val
            ((FFT (fun j => (↑(decompose B BETA' K j) : ZMod (fermat_ext BASE n')) * THETA_v ^ j.val) OMEGA_v) i).val
            n' (ZMod.val_lt _) (ZMod.val_lt _) hBASE hn'_good : Nat) : ZMod (fermat_ext BASE n')))
        hcF_eq j
      -- h_chain says: NTT_zmod cF OMEGAInv j * KInv * THETAInv^j = negacyclic_conv_R ...
      -- But the algorithm uses FFT cF OMEGAInv, which equals NTT_zmod cF OMEGAInv
      rw [show FFT
        (fun i =>
          ((schonhage_strassen_FFT BASE
            ((FFT (fun j => (↑(decompose A BETA' K j) : ZMod (fermat_ext BASE n')) * THETA_v ^ j.val) OMEGA_v) i).val
            ((FFT (fun j => (↑(decompose B BETA' K j) : ZMod (fermat_ext BASE n')) * THETA_v ^ j.val) OMEGA_v) i).val
            n' (ZMod.val_lt _) (ZMod.val_lt _) hBASE hn'_good : Nat) : ZMod (fermat_ext BASE n')))
        OMEGA_v⁻¹ = NTT_zmod _ OMEGA_v⁻¹ from h_fft_inv _]
      exact h_chain.trans (by
        have hFn_eq : fermat_ext BASE n = BETA' ^ K + 1 := by rw [← hKM, fermat_ext_eq_pow_pow]
        have h_dA : ∀ l : Fin K, decompose A BETA' K l < fermat_ext BASE n' :=
          fun l => decompose_lt_fermat _ BASE M K n' hBASE_ge hM_pos (by omega) (by positivity) (hFn_eq ▸ hA) l
        have h_dB : ∀ l : Fin K, decompose B BETA' K l < fermat_ext BASE n' :=
          fun l => decompose_lt_fermat _ BASE M K n' hBASE_ge hM_pos (by omega) (by positivity) (hFn_eq ▸ hB) l
        show negacyclic_conv_R K
          (fun l => ((↑(decompose A BETA' K l) : ZMod (fermat_ext BASE n'))))
          (fun l => ((↑(decompose B BETA' K l) : ZMod (fermat_ext BASE n')))) j =
          ((↑neg_conv_j : ℤ) : ZMod (fermat_ext BASE n'))
        rw [neg_conv_j_def, ← negacyclic_conv_cast_eq]
        simp_rw [show ∀ l : Fin K,
          ((↑(decompose A BETA' K l) : ZMod (fermat_ext BASE n')).val : ℤ) =
          ↑(decompose A BETA' K l) from
          fun l => congr_arg _ (ZMod.val_natCast_of_lt (h_dA l))]
        simp_rw [show ∀ l : Fin K,
          ((↑(decompose B BETA' K l) : ZMod (fermat_ext BASE n')).val : ℤ) =
          ↑(decompose B BETA' K l) from
          fun l => congr_arg _ (ZMod.val_natCast_of_lt (h_dB l))])
    · -- neg_conv_j < threshold  (upper bound)
      simp only [← BETA'_def, ← n'_def, ← K_def, ← M_def, ← k_def] at *
      rw [neg_conv_j_def]
      have hFn_eq : fermat_ext BASE n = BETA' ^ K + 1 := by rw [← hKM, fermat_ext_eq_pow_pow]
      exact negacyclic_decompose_strict_pos_bound A B BETA' K hK_gt
        (by positivity) (hFn_eq ▸ hA) (hFn_eq ▸ hB) j
    · -- -(F' - threshold) < neg_conv_j  (lower bound)
      simp only [← BETA'_def, ← n'_def, ← K_def, ← M_def, ← k_def] at *
      rw [neg_conv_j_def]
      have hF'_gt : (↑K : ℤ) * (↑BETA') ^ 2 < ↑(fermat_ext BASE n') := by
        exact_mod_cast fermat_ext_gt_K_mul_sq BASE k M n' hBASE_ge hM_pos hn'_ge
      have hFn_eq : fermat_ext BASE n = BETA' ^ K + 1 := by rw [← hKM, fermat_ext_eq_pow_pow]
      apply h_neg_helper K (↑BETA') _ j hF'_gt
      exact negacyclic_coeff_neg_bound K (by positivity)
        (fun j => ↑(decompose A BETA' K j)) (fun j => ↑(decompose B BETA' K j))
        (fun j => Nat.cast_nonneg _) (fun j => Nat.cast_nonneg _)
        (fun j => Nat.cast_le.mpr (decompose_digit_le A BETA' K (by positivity) (by positivity)
          (hFn_eq ▸ hA) j))
        (fun j => Nat.cast_le.mpr (decompose_digit_le B BETA' K (by positivity) (by positivity)
          (hFn_eq ▸ hB) j))
        j
    · exact mul_nonneg (Int.natCast_nonneg _) (sq_nonneg _)
    · simp only [← BETA'_def, ← n'_def, ← K_def, ← M_def, ← k_def] at *
      have hF'_gt := fermat_ext_gt_K_mul_sq BASE k M n' hBASE_ge hM_pos hn'_ge
      have hj_le_K := Nat.succ_le_of_lt j.isLt
      have h1 : (j.val + 1) * BETA' ^ 2 ≤ K * BETA' ^ 2 :=
        Nat.mul_le_mul_right _ hj_le_K
      have h2 : K * BETA' ^ 2 < fermat_ext BASE n' := hF'_gt
      have h3 : (j.val + 1) * BETA' ^ 2 ≤ fermat_ext BASE n' := le_of_lt (lt_of_le_of_lt h1 h2)
      zify at h3 ⊢
      simp only [Int.ofNat_eq_coe, Nat.cast_add, Nat.cast_one, Nat.cast_mul] at *
      linarith
  rw [← Nat.mod_eq_of_lt h_lt]
  have h3 := congr_arg ZMod.val h_zmod
  rw [ZMod.val_natCast, ZMod.val_natCast] at h3
  exact h3
-- ====================================================================
-- TOP-LEVEL CORRECTNESS
-- ====================================================================
theorem schonhage_strassen_FFT_correct_aux
    (BASE : Nat) (hBASE : Even BASE) :
    ∀ n, ∀ A B,
    ∀ (hnk : good_n n),
    ∀ (hA : A < fermat_ext BASE n),
    ∀ (hB : B < fermat_ext BASE n),
    schonhage_strassen_FFT BASE A B n hA hB hBASE hnk =
      (A * B) % (fermat_ext BASE n) := by
  -- General bound: the output is always < fermat_ext
  have h_output_lt : ∀ BETA' A' B' n' (hA' : A' < fermat_ext BETA' n') (hB' : B' < fermat_ext BETA' n')
      (hBASE' : Even BETA') (hnk' : good_n n'),
      schonhage_strassen_FFT BETA' A' B' n' hA' hB' hBASE' hnk' < fermat_ext BETA' n' := by
    intro BETA' A' B' n' hA' hB' hBASE' hnk'
    rw [schonhage_strassen_FFT.eq_1]
    split
    · exact Nat.mod_lt _ (fermat_ext_pos _ _)
    · exact ZMod.val_lt _
  rcases Nat.eq_zero_or_pos BASE with rfl | hBASE_pos
  · -- BASE = 0 case: for n ≥ 1, fermat_ext 0 n = 0^n + 1 = 1, so A = 0, B = 0
    intro n A B hnk hA hB
    rcases n with _ | n
    · -- n = 0: fermat_ext 0 0 = 2
      unfold schonhage_strassen_FFT; simp [show (0 : Nat) < 16 from by omega]
    · -- n ≥ 1: fermat_ext 0 (n+1) = 1, so both output and (A*B)%1 are 0
      have hF : fermat_ext 0 (n + 1) = 1 := by unfold fermat_ext; simp
      have h1 := h_output_lt 0 A B (n+1) hA hB hBASE hnk
      have h2 : (A * B) % fermat_ext 0 (n+1) < fermat_ext 0 (n+1) := Nat.mod_lt _ (fermat_ext_pos _ _)
      omega
  · have hBASE_ge : 2 ≤ BASE := by obtain ⟨k, hk⟩ := hBASE; omega
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro A B hnk hA hB
      by_cases h : n < 16
      · unfold schonhage_strassen_FFT; simp [h]
      · exact schonhage_strassen_FFT_recursive BASE hBASE hBASE_ge n h A B hnk hA hB
          (fun m hm A' B' hm' hA' hB' => ih m hm A' B' hm' hA' hB')
theorem schonhage_strassen_FFT_correct
    (BASE A B n : Nat)
    (hBASE : Even BASE)
    (hnk : ∃ k : Nat, 2 ≤ k ∧ 2 ^ k ∣ n)
    (hA : A < fermat_ext BASE n) (hB : B < fermat_ext BASE n) :
    schonhage_strassen_FFT BASE A B n hA hB hBASE hnk =
      (A * B) % (fermat_ext BASE n) :=
  schonhage_strassen_FFT_correct_aux BASE hBASE n A B hnk hA hB
