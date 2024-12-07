/-
Copyright (c) 2024 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Polynomial.Content
import Mathlib
/-!
# The generalized factorial function over subsets of a Dedekind Domain

## References

 * https://www.jstor.org/stable/2695734
 * https://pdf.sciencedirectassets.com/272482/1-s2.0-S0022314X00X00534/1-s2.0-S0022314X9892220X/main.pdf?X-Amz-Security-Token=IQoJb3JpZ2luX2VjEHkaCXVzLWVhc3QtMSJIMEYCIQCi4U%2BQq8XXsNyCFxOOB1z3779RcF1x5SgA3cEo0TChjwIhAOIeVRwHVjJLumM8vZQHR1y3zWmWiFoCWmiRXgNCgNksKrMFCDIQBRoMMDU5MDAzNTQ2ODY1IgzCehXHeTR%2FbAkQ1vUqkAXZQZ1uzW2ORh%2BxjPJSYFGOBvOaKRfNOH0fEfAKDO915O5jhejV1NpDCxsJ%2FVenTzqNQolhp3W1Ud3YwxfmJE9%2BHmOK81cXfDG2%2FiCCP3RLUGBo5NYG6UulB1hC2HuqF3db4hO1F3AU1qdap%2FigWk0kI567w9Zx3Fg1jDONDuSwvFnfrbq%2FzAWYFUXVNNgWq3RFbL4moZkvd2Oi92uI00mgNjO2q2gNoxQ5cpEJgzstAjGZ0t1GVDL0%2FinHDW1QOVoutv%2FnX1s%2BguKrJ%2F1KWtXyi2PSBYruBtPNm2jG%2BWSe2cH4GS%2FnKOmgZQds7If0Djn5IdiwXtLv%2BiznazuSKQsCVdb6rIWu0NSY5IieqxYqqf1jlhpSNWxONbtyUDxtSVh1WVE%2FbJNAyrkipq1mKHoDuyEuutIQQvm2EZxP%2F%2BLuuzo%2BE5in70q6UM%2Fyxvx0zDgQivRmhLCbRCd2eZLtpufKE5TSNVeF3MW1iLRi74GeJIo%2FkoeJBSVMdEKUO%2BsLu0lM3iO06tk2mHAz7F8hxthYuqNGausolbRjjacQD2NWL%2BLXzSj1kklmXbqGrB%2BNdCH3Xj7omcs3qDm3ofdJwvsT3rRCKPHKn2UWw%2FB1voNR6ug7H5t8EbEmfgpLlHcXUp6JtkuspWovHg98Kq5gnx%2BdXADm58qi73oJjRDYZdBEYy5S0SNjxBAZkhA4baZNnp2fhpN%2FcGP68AWpEU9lZvt8mxzjHL%2FxGtzsIjHqDj9OB%2FoPcJt3GDCBsz8bW6%2F7zMvdPQPbqYoG7y84%2Br1VBdEhFsGtzlIz7Hjum8a7khtvM1JoTma%2BbCOmW%2BbnsyG%2F6dgVSWUZsk8AlYuMz6fB8ib7L9laJvUVYE833mD06wmwUTCX1My6BjqwAQvbAglYdP7vv8fDLWJ6M5V1WTCHj2SZ5yVhrlx8kTbGO28MGihwVK1xXOZ2L%2BH462Dfyh0SdjCfbDriFbTlCAbtRMvfA8bKCdNdR88s21GwKvtGvhOoaREnpiwyIUqvZ4lWClEF%2FC0lxUXC92zUAc%2F0Gmu0LXtv63Ef8lZyxiVeeGTEAotj1Ot93DCuLKku58C8aDIz2iBdh83wAZKeub5%2B3DLqKEzUa5TY0sfaglxo&X-Amz-Algorithm=AWS4-HMAC-SHA256&X-Amz-Date=20241206T174540Z&X-Amz-SignedHeaders=host&X-Amz-Expires=300&X-Amz-Credential=ASIAQ3PHCVTYTSABWTT7%2F20241206%2Fus-east-1%2Fs3%2Faws4_request&X-Amz-Signature=a8c185e03d8f01e9c8cda0181dea98082cfdfc647a729536d5e4483417e2a8af&hash=6d39e45f4a1d3b9f09e6ee51ebb0768816354b07db3b3047ebf4402a5d3d2afb&host=68042c943591013ac2b2430a89b270f6af2c76d8dfd086a07176afe7c76c2c61&pii=S0022314X9892220X&tid=spdf-d9c90067-67e5-47f5-b707-b0ed31f3c86d&sid=b54c02540a819-44f4-85bd-e2390804978cgxrqa&type=client&tsoh=d3d3LnNjaWVuY2VkaXJlY3QuY29t&ua=13115606040b52595100&rr=8ede174ad9b2903f&cc=us
 * https://en.wikipedia.org/wiki/Bhargava_factorial

 * https://www.youtube.com/watch?v=1YB-5occzSk
 * https://www.cip.ifi.lmu.de/~grinberg/algebra/fps20gfv.pdf
 * https://arxiv.org/pdf/2310.12949

## Tags
dedekind domain, factorial ideal, factorial, ideal
-/

open BigOperators
open scoped Nat Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] (S : Set R)

namespace Polynomial

def fixedDivisor (F : R[X]) : Ideal R := Ideal.span <| F.eval '' S

end Polynomial

variable (p : ℕ) [Fact p.Prime]

structure Set.pOrdering where
  elems : ℕ → S
  emultiplicity_le (k : ℕ) (s : S) :
    0 < k →  -- TODO: Maybe this isn't necessary?
      emultiplicity ↑p (∏ i ∈ Finset.range k, ((elems k).val - (elems i).val)) ≤
        emultiplicity ↑p (∏ i ∈ Finset.range k, (s.val - (elems i).val))

instance : CoeFun (S.pOrdering p) (fun _ ↦ ℕ → R) := ⟨fun ν k ↦ ν.elems k |>.val⟩

example : emultiplicity 3 18 = 2 := by
  erw [emultiplicity_eq_coe]
  decide


/-- The associated p-sequence for a p-ordering.

  Technically in the paper, this sequence is defined to be the powers, rather than the exponents
  themselves, but it seems like this perhaps shouldn't make much difference?
-/
noncomputable def Set.pOrdering.pSequence {ν : S.pOrdering p} (k : ℕ) :=
  emultiplicity ↑p <| ∏ i : Fin k, (ν k - ν i)


def pSequence.eq (ν₁ ν₂ : S.pOrdering p) : ν₁.pSequence = ν₂.pSequence := by
  ext n
  sorry


/-- ℕ is a p-ordering of ℤ for any prime `p`. -/
def natPOrdering : (Set.univ : Set ℤ).pOrdering p where
  elems := (⟨·, Set.mem_univ _⟩)
  emultiplicity_le := by
    intro i s hi
    simp?
    -- induction k with
    -- | zero => sorry
    -- | succ i hi =>
    have this1 := Nat.descFactorial_eq_prod_range i i
    simp? [this1]
    -- push_cast at this
    -- rw_mod_cast [← this]
    -- refine Finset.prod_congr ?_ ?_
    have this2 : ((∏ x ∈ Finset.range i, ((i - x) : ℕ)) : ℤ)
      = (∏ x ∈ Finset.range (i), ((i : ℤ) - (x :ℤ))) := by
        apply Finset.prod_congr
        rfl
        intro x hx
        simp at hx
        rw [Int.natCast_sub]
        -- simp [hx]
        linarith
    rw [←this2]
    -- have this3 : ∏ x ∈ Finset.range (i + 1), (i + 1 - x)
    --   = ∏ x ∈ Finset.range (i + 1), ((i + 1 - x) : ℤ) := by sorry
    zify at this1
    rw [←this1]
    have fact_dvd_descfact := Nat.factorial_dvd_descFactorial i i
    have fact_eq_descfact : i ! = Nat.descFactorial  i i :=
      by exact
        Eq.symm (Nat.descFactorial_self i)
    rw [←fact_eq_descfact]
    have this1' := Nat.descFactorial_eq_prod_range

      -- erw [emultiplicity_eq_coe]

      -- constructor
      -- rw [Nat.descFactorial_eq_fac]
      -- rw [←this]
      -- rw [Nat.descFactorial_eq_prod_range]
    -- n.le_refl,

#check Nat.factorial_dvd_descFactorial
#check Int.natCast_sub
#check Int.subNatNat_of_sub_eq_succ
#check Finset.prod_congr
#check Nat.descFactorial
#check Nat.descFactorial_eq_prod_range


namespace Polynomial

/-- A special case originally proved by Pòlya. -/
theorem polya_dvd {𝒻 : ℤ[X]} {k : ℕ} (hP : 𝒻.IsPrimitive) (hD : 𝒻.natDegree = k) :
    𝒻.fixedDivisor ∣ k ! :=
  sorry

/-- A special case originally proved by Pòlya. -/
theorem polya_exists (k : ℕ) : ∃ 𝒻 : ℤ[X], 𝒻.IsPrimitive ∧ 𝒻.natDegree = k ∧ 𝒻.fixedDivisor = k ! :=
  sorry

end Polynomial
