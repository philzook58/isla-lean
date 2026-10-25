import IslaLean.Basic

/-! Memory accesses in the Sail RISC-V model check alignment (`srem` by the width) and walk the
platform memory map with 128-bit signed comparisons of zero-extended addresses. These simp lemmas
turn each guard shape into a `Nat` comparison that `omega` can decide, and `RamRegion` states
the precondition under which an access is served from RAM without faulting or splitting. -/
namespace IslaLean

theorem zext_toInt (x : BitVec 64) : (x.setWidth 128).toInt = x.toNat := by
  have hx : x.toNat < 2 ^ 64 := x.isLt
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp; omega
  · simp [BitVec.msb_eq_getLsbD_last]

theorem ofNat_toInt (c : Nat) (hc : c < 2 ^ 127) : (BitVec.ofNat 128 c).toInt = c := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp; omega
  · rw [BitVec.msb_eq_decide]; simp; omega

@[simp] theorem zext_sle_ofNat (x : BitVec 64) (c : Nat) (hc : c < 2 ^ 64 := by decide) :
    (x.setWidth 128).sle (BitVec.ofNat 128 c) = decide (x.toNat ≤ c) := by
  rw [Bool.eq_iff_iff, BitVec.sle_iff_toInt_le, zext_toInt, ofNat_toInt c (by omega)]; simp

@[simp] theorem ofNat_sle_zext (x : BitVec 64) (c : Nat) (hc : c < 2 ^ 64 := by decide) :
    (BitVec.ofNat 128 c).sle (x.setWidth 128) = decide (c ≤ x.toNat) := by
  rw [Bool.eq_iff_iff, BitVec.sle_iff_toInt_le, zext_toInt, ofNat_toInt c (by omega)]; simp

@[simp] theorem zext_sle_zext (x y : BitVec 64) :
    (x.setWidth 128).sle (y.setWidth 128) = decide (x.toNat ≤ y.toNat) := by
  rw [Bool.eq_iff_iff, BitVec.sle_iff_toInt_le, zext_toInt, zext_toInt]; simp

@[simp] theorem zext_slt_zext (x y : BitVec 64) :
    (x.setWidth 128).slt (y.setWidth 128) = decide (x.toNat < y.toNat) := by
  rw [Bool.eq_iff_iff, BitVec.slt_iff_toInt_lt, zext_toInt, zext_toInt]; simp

@[simp] theorem zext_add_sle_ofNat (x : BitVec 64) (k c : Nat) (hk : k < 2 ^ 64 := by decide)
    (hc : c < 2 ^ 64 := by decide) :
    ((x.setWidth 128) + BitVec.ofNat 128 k).sle (BitVec.ofNat 128 c) =
      decide (x.toNat + k ≤ c) := by
  have hx : x.toNat < 2 ^ 64 := x.isLt
  have hsum : (x.setWidth 128) + BitVec.ofNat 128 k = BitVec.ofNat 128 (x.toNat + k) := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [hsum, Bool.eq_iff_iff, BitVec.sle_iff_toInt_le, ofNat_toInt _ (by omega),
    ofNat_toInt c (by omega)]
  simp only [decide_eq_true_eq]; omega

@[simp] theorem srem_zext_ofNat (x : BitVec 64) (k : Nat) (hk : 0 < k ∧ k < 2 ^ 64 := by decide) :
    BitVec.srem (x.setWidth 128) (BitVec.ofNat 128 k) = BitVec.ofNat 128 (x.toNat % k) := by
  have hx : x.toNat < 2 ^ 64 := x.isLt
  have hmx : (x.setWidth 128).msb = false := by simp [BitVec.msb_eq_getLsbD_last]
  have hmk : (BitVec.ofNat 128 k).msb = false := by rw [BitVec.msb_eq_decide]; simp; omega
  rw [BitVec.srem_eq, hmx, hmk]
  apply BitVec.eq_of_toNat_eq
  have hm : x.toNat % k < k := Nat.mod_lt _ hk.1
  have h1 : x.toNat < 2 ^ 128 := by omega
  have h2 : k < 2 ^ 128 := by omega
  have h3 : x.toNat % k < 2 ^ 128 := by omega
  simp [BitVec.toNat_umod, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]

/-- Store data arrives as the full-width slice `extractLsb 63 0`. -/
@[simp] theorem extractLsb_full (x : BitVec 64) : BitVec.extractLsb 63 0 x = x := by
  ext i hi; simp [BitVec.getLsbD_eq_getElem (show i < 64 by omega)]

/-- Alignment guards compare `ofNat 128 (x % k)` with zero after the `srem` rewrite. -/
@[simp] theorem ofNat128_mod_eq_zero (x k : Nat) (hk : 0 < k ∧ k < 2 ^ 64 := by decide) :
    BitVec.ofNat 128 (x % k) = 0#128 ↔ x % k = 0 := by
  have : x % k < k := Nat.mod_lt _ hk.1
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp at this; omega
  · intro h; simp [h]

/-- The low word of a sign-extended word (`lw` results, `addw` operands). -/
@[simp] theorem low_signExtend (v : BitVec 32) : BitVec.extractLsb 31 0 (v.signExtend 64) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h3 : i < 32 := by omega
  simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_signExtend]
  simp [h3, BitVec.getLsbD_eq_getElem]
  omega

/-- Byte stores take `extractLsb 7 0` of a zero-extended byte load (`lbu`/`sb`). -/
@[simp] theorem low8_zext (v : BitVec 8) : BitVec.extractLsb 7 0 (v.setWidth 64) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h : i < 8 := by omega
  simp only [BitVec.getLsbD_extractLsb, BitVec.getLsbD_setWidth]
  simp [h]; omega

@[simp] theorem extractLsb_full8 (v : BitVec 8) : BitVec.extractLsb 7 0 v = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h : i < 8 := by omega
  simp only [BitVec.getLsbD_extractLsb]
  simp [h]

/-- Lets `omega` use `x ≠ 0` facts about counters. -/
theorem eq_zero_iff_toNat (x : BitVec 64) : x = 0#64 ↔ x.toNat = 0 := by
  constructor
  · intro h; simp [h]
  · intro h; apply BitVec.eq_of_toNat_eq; simpa using h

/-- The `jalr` alignment assertion of `ret` always holds once bit 0 is cleared. -/
@[simp] theorem ret_aligned (x : BitVec 64) :
    BitVec.extractLsb 0 0 (x &&& 0xfffffffffffffffe#64) = 0#1 := by
  ext i hi
  have : i = 0 := by omega
  subst this
  simp

/-- A 64-bit register holding a sign-extended 32-bit value, as the psABI passes `uint32_t`. -/
def Canonical32 (x : BitVec 64) : Prop := x.toNat < 2 ^ 31 ∨ 2 ^ 64 - 2 ^ 31 ≤ x.toNat

theorem canonical_signExtend (x : BitVec 64) (h : Canonical32 x) :
    (BitVec.extractLsb 31 0 x).signExtend 64 = x := by
  unfold Canonical32 at h
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hlow : (BitVec.extractLsb 31 0 x).toNat = x.toNat % 2 ^ 32 := by
    simp [BitVec.extractLsb_toNat]
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide, BitVec.toNat_setWidth, hlow]
  split <;> simp_all <;> omega

theorem signExtend_inj {a b : BitVec 32} (h : a.signExtend 64 = b.signExtend 64) : a = b := by
  simpa using congrArg (BitVec.extractLsb 31 0) h

/-- A canonical register is its low 32 bits, as a number, sign-extended. -/
theorem canonical_ofNat (x : BitVec 64) (h : Canonical32 x) :
    x = (BitVec.ofNat 32 (x.toNat % 2 ^ 32)).signExtend 64 := by
  conv => lhs; rw [← canonical_signExtend x h]
  congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.extractLsb_toNat]

theorem signExtend_ofNat_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : (BitVec.ofNat 32 a).signExtend 64 = (BitVec.ofNat 32 b).signExtend 64) : a = b := by
  have := congrArg BitVec.toNat (signExtend_inj h)
  simp at this; omega

theorem ofNat32_succ (i : Nat) (h : i + 1 < 2 ^ 32) :
    BitVec.ofNat 32 i + 1#32 = BitVec.ofNat 32 (i + 1) := by
  apply BitVec.eq_of_toNat_eq; simp

/-- A cursor `x` that is `4 * i` bytes past `b`, with no wraparound. -/
theorem cursor_eq (b x : BitVec 64) (hle : b.toNat ≤ x.toNat) (hm : (x.toNat - b.toNat) % 4 = 0) :
    b + BitVec.ofNat 64 (4 * ((x.toNat - b.toNat) / 4)) = x := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Decrementing a nonzero counter. -/
theorem toNat_sub_one (x : BitVec 64) (h : 0 < x.toNat) : (x - 1#64).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub]; simp; omega

/-- Generated code writes `1#64`; specs write `1`. -/
theorem sub1_add1 (x : BitVec 64) : x - 1#64 + 1 = x := BitVec.sub_add_cancel x 1
theorem add1_sub1 (x : BitVec 64) : x + 1#64 - 1 = x := BitVec.add_sub_cancel x 1

/-- `n` consecutive 8-byte limbs at `p`, all 8-aligned and inside the platform's RAM window
`[0x80000000, 0x100000000)`. -/
def RamRegion (p : BitVec 64) (n : Nat) : Prop :=
  0x80000000 ≤ p.toNat ∧ p.toNat + 8 * n ≤ 0x100000000 ∧ p.toNat % 8 = 0

/-- `n` consecutive `width`-byte items at `p`, all `width`-aligned and inside RAM. Byte buffers
(`width = 1`) need no alignment. -/
def RamWords (p : BitVec 64) (width n : Nat) : Prop :=
  0x80000000 ≤ p.toNat ∧ p.toNat + width * n ≤ 0x100000000 ∧ p.toNat % width = 0

theorem RamRegion.next (h : RamRegion p n) (hn : 0 < n) : RamRegion (p + 8#64) (n - 1) := by
  unfold RamRegion at *
  rw [BitVec.toNat_add]; simp
  omega

end IslaLean
