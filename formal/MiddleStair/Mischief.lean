import Mathlib.Tactic

/-!
# The finite mischief certificate

Jiang--Scully--Zhang reduce nonnegativity of the `mischief` of two cyclic
binary words to absence of a negative cycle in a 64-vertex directed graph.
Their appendix checks the graph with Bellman--Ford.  Here we replace that
external computation by a small, kernel-reduced potential certificate.

`LocalState` stores the eight bits

`(pᵢ₋₁, pᵢ, sᵖᵢ, sᵖᵢ₊₁, qᵢ₋₁, qᵢ, sᑫᵢ, sᑫᵢ₊₁)`.

The Boolean predicates `valid` and `follows` are literal translations of the
two sector constraints and the state-overlap constraint in the published
appendix.  The integer `potential` is a Bellman--Ford distance certificate.
The only exhaustive step is `reducedCost_nonnegative`; it checks at most
`256^2` pairs by ordinary kernel reduction (`by decide`, not
`native_decide`).  The subsequent cyclic telescoping theorem is symbolic.
-/

namespace MiddleStair.Mischief

open scoped BigOperators

/--
One local state of the Jiang--Scully--Zhang mischief automaton.  The eight
bits are stored in the exact least-significant-bit-first order used by the
published checker.  Using `Fin 256` makes the exhaustive certificate reduce
without relying on a generated `Fintype` instance for an eight-field record.
-/
abbrev LocalState := Fin 256

namespace LocalState

def pPrev (u : LocalState) : Bool := u.val.testBit 0
def pNow (u : LocalState) : Bool := u.val.testBit 1
def pSector (u : LocalState) : Bool := u.val.testBit 2
def pSectorNext (u : LocalState) : Bool := u.val.testBit 3
def qPrev (u : LocalState) : Bool := u.val.testBit 4
def qNow (u : LocalState) : Bool := u.val.testBit 5
def qSector (u : LocalState) : Bool := u.val.testBit 6
def qSectorNext (u : LocalState) : Bool := u.val.testBit 7

end LocalState

/-- Interpret a bit as an integer in `{0,1}`. -/
def bit (b : Bool) : ℤ := if b then 1 else 0

/-- Interpret a bit as a natural number in `{0,1}`. -/
def natBit (b : Bool) : ℕ := if b then 1 else 0

/-- Pack eight named bits into the published least-significant-bit-first code. -/
def encode (pPrev pNow pSector pSectorNext qPrev qNow qSector qSectorNext : Bool) :
    LocalState :=
  ⟨natBit pPrev + 2 * natBit pNow + 4 * natBit pSector + 8 * natBit pSectorNext +
    16 * natBit qPrev + 32 * natBit qNow + 64 * natBit qSector +
      128 * natBit qSectorNext, by
    cases pPrev <;> cases pNow <;> cases pSector <;> cases pSectorNext <;>
      cases qPrev <;> cases qNow <;> cases qSector <;> cases qSectorNext <;>
      decide⟩

@[simp] theorem encode_pPrev (a b c d e f g h : Bool) :
    (encode a b c d e f g h).pPrev = a := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases e <;> cases f <;> cases g <;> cases h <;> decide

@[simp] theorem encode_pNow (a b c d e f g h : Bool) :
    (encode a b c d e f g h).pNow = b := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases e <;> cases f <;> cases g <;> cases h <;> decide

@[simp] theorem encode_pSector (a b c d e f g h : Bool) :
    (encode a b c d e f g h).pSector = c := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases e <;> cases f <;> cases g <;> cases h <;> decide

@[simp] theorem encode_pSectorNext (a b c d e f g h : Bool) :
    (encode a b c d e f g h).pSectorNext = d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases e <;> cases f <;> cases g <;> cases h <;> decide

@[simp] theorem encode_qPrev (a b c d e f g h : Bool) :
    (encode a b c d e f g h).qPrev = e := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases e <;> cases f <;> cases g <;> cases h <;> decide

@[simp] theorem encode_qNow (a b c d e f g h : Bool) :
    (encode a b c d e f g h).qNow = f := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases e <;> cases f <;> cases g <;> cases h <;> decide

@[simp] theorem encode_qSector (a b c d e f g h : Bool) :
    (encode a b c d e f g h).qSector = g := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases e <;> cases f <;> cases g <;> cases h <;> decide

@[simp] theorem encode_qSectorNext (a b c d e f g h : Bool) :
    (encode a b c d e f g h).qSectorNext = h := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    cases e <;> cases f <;> cases g <;> cases h <;> decide

/-- Interpret a sector bit as its sign in `{-1,1}`. -/
def sign (b : Bool) : ℤ := if b then 1 else -1

/-- Indicator that two sector bits differ. -/
def sectorSwitch (a b : Bool) : ℤ := if a = b then 0 else 1

/-- The two local constraints imposed by the definition of sectors. -/
def valid (u : LocalState) : Bool :=
  (if u.pPrev == u.pNow then u.pPrev == u.pSector
    else u.pSector == u.pSectorNext) &&
  (if u.qPrev == u.qNow then u.qPrev == u.qSector
    else u.qSector == u.qSectorNext)

/-- Consecutive local states agree on their four overlapping bits. -/
def follows (u v : LocalState) : Bool :=
  (u.pNow == v.pPrev) &&
  (u.qNow == v.qPrev) &&
  (u.pSectorNext == v.pSector) &&
  (u.qSectorNext == v.qSector)

/-- The local mischief weight `Mᵢ(p,q)`. -/
def weight (u : LocalState) : ℤ :=
  sign u.pSector * (bit u.pNow - bit u.qPrev) +
  sign u.qSector * (bit u.qNow - bit u.pPrev) -
  sectorSwitch u.pSector u.pSectorNext -
  sectorSwitch u.qSector u.qSectorNext

/-- Eight-bit encoding, using the bit order of the published Python appendix. -/
def code (u : LocalState) : ℕ :=
  u.val

/-- Codes whose Bellman--Ford potential is zero. -/
def potentialZeroCodes : List ℕ :=
  [0, 2, 8, 32, 34, 40, 119, 125, 127,
   128, 130, 136, 215, 221, 223, 247, 253, 255]

/-- Codes whose Bellman--Ford potential is `-1`. -/
def potentialNegOneCodes : List ℕ :=
  [1, 14, 16, 18, 23, 24, 29, 31, 33, 46,
   113, 126, 129, 142, 209, 222, 224, 226,
   231, 232, 237, 239, 241, 254]

/-- A shortest-path potential for the finite mischief graph. -/
def potential (u : LocalState) : ℤ :=
  if code u ∈ potentialZeroCodes then 0
  else if code u ∈ potentialNegOneCodes then -1
  else -2

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/--
Every valid transition has nonnegative reduced cost.  This is the complete
finite certificate behind the published Bellman--Ford computation.
-/
theorem reducedCost_nonnegative :
    ∀ u v : LocalState,
      valid u = true → valid v = true → follows u v = true →
        0 ≤ weight u + potential u - potential v := by
  decide

/-- A symbolic no-negative-cycle consequence of the finite certificate. -/
theorem sum_weight_nonnegative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (next : Equiv.Perm ι) (μ : ι → LocalState)
    (hvalid : ∀ i, valid (μ i) = true)
    (hfollow : ∀ i, follows (μ i) (μ (next i)) = true) :
    0 ≤ ∑ i, weight (μ i) := by
  have hpoint : ∀ i, 0 ≤ weight (μ i) + potential (μ i) - potential (μ (next i)) :=
    fun i => reducedCost_nonnegative (μ i) (μ (next i))
      (hvalid i) (hvalid (next i)) (hfollow i)
  have hsum := Finset.sum_nonneg fun i (_hi : i ∈ Finset.univ) => hpoint i
  have hperm : (∑ i, potential (μ (next i))) = ∑ i, potential (μ i) := by
    exact Equiv.sum_comp next (fun i => potential (μ i))
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hperm] at hsum
  simpa using hsum

end MiddleStair.Mischief
