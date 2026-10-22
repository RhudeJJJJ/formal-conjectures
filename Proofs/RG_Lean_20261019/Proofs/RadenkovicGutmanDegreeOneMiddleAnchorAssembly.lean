/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeOneMiddleAnchorData
import Proofs.RadenkovicGutmanOriginalAssembly

/-! Exact assembly of the paid anchors and the eight finite residual parameter
instances. The 680 analytic integral bounds remain explicit obligations. -/
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
open CoreQuotient ActualFusionIntegral OriginalAssembly
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem covered_sound (n p q : ℕ) (hc : covered n p q=true) :
    (n,p,q) ∈ residual ∨ ∃ a ∈ anchors.toList,
      a.p=p ∧ a.q=q ∧ n ≤ a.n ∧ |(2 : ℝ)/(n : ℝ)-2/(a.n : ℝ)| < (a.lower : ℝ) := by
  by_cases hr : (n,p,q) ∈ residual
  · exact Or.inl hr
  · right
    cases ho : chosen n p q with
    | none => simp only [covered,if_neg hr,ho,Bool.false_eq_true] at hc
    | some a =>
      have ha : accepts n p q a=true := by simpa only [covered,if_neg hr,ho] using hc
      change anchors[lookup n p q]?=some a at ho
      refine ⟨a,Array.mem_toList_iff.mpr (Array.mem_of_getElem? ho),?_⟩
      obtain ⟨hp,hq,hn,hgap⟩ := of_decide_eq_true ha
      exact ⟨hp,hq,hn,by exact_mod_cast hgap⟩

def Checks : Prop := ∀ n : ℕ, 14 ≤ n → n ≤ 52 → checkAt n=true

def AnalyticCertificates : Prop :=
  ∀ a ∈ anchors.toList, ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → C.degree u=1 →
      ((p=a.p ∧ q=a.q) ∨ (p=a.q ∧ q=a.p)) → order C p q ≤ a.n →
        (a.lower : ℝ) ≤ normalizedIntegral C u p q (2-2/(a.n : ℝ))

def ResidualCases : Prop :=
  ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
    (source C u p q).IsTree → C.degree u=1 →
      (order C p q,min p q,max p q) ∈ residual → 0 < meanIntegral C u p q

/-- All original middle-family quantifiers and the actual mean threshold are
retained. An unpaid anchor is discharged only by its finite residual family. -/
theorem input_family_of_certificates (hchecks : Checks) (hanchors : AnalyticCertificates)
    (hresidual : ResidualCases) :
    ∀ (m : ℕ) (C : SimpleGraph (Fin m)) (u : Fin m) (p q : ℕ),
      (source C u p q).IsTree → C.degree u=1 → 14 ≤ order C p q → order C p q ≤ 52 →
        0 < meanIntegral C u p q := by
  intro m C u p q hT hd h14 h52
  have hdeg : C.degree u < m := by
    simpa only [Fintype.card_fin] using C.degree_lt_card_verts u
  have horder : order C p q=m+p+q+2 := by
    simp only [order,Fintype.card_sum,Fintype.card_fin]
    omega
  have hsum : min p q+max p q=p+q := by omega
  have hlo : min p q ≤ max p q := by omega
  have hp : min p q < 49 := by omega
  have hq : max p q < 49 := by omega
  have hsize : min p q+max p q+4 ≤ order C p q := by omega
  have hh : ∀ r s : Fin 49, r.val ≤ s.val → r.val+s.val+4 ≤ order C p q →
      covered (order C p q) r.val s.val=true :=
    of_decide_eq_true (hchecks _ h14 h52)
  have hc := hh ⟨min p q,hp⟩ ⟨max p q,hq⟩ hlo hsize
  rcases covered_sound _ _ _ hc with hr | ⟨a,ha,hap,haq,hn,hgap⟩
  · exact hresidual m C u p q hT hd hr
  · have hor : (p=a.p ∧ q=a.q) ∨ (p=a.q ∧ q=a.p) := by
      by_cases hpq : p ≤ q
      · rw [min_eq_left hpq] at hap
        rw [max_eq_right hpq] at haq
        exact Or.inl ⟨hap.symm,haq.symm⟩
      · have hqp : q ≤ p := by omega
        rw [min_eq_right hqp] at hap
        rw [max_eq_left hqp] at haq
        exact Or.inr ⟨haq.symm,hap.symm⟩
    have hb := hanchors a ha m C u p q hT hd hor hn
    have ht := anchor_transport C u p q a.n hT (by omega)
    change normalizedIntegral C u p q (2-2/(a.n : ℝ))-
      |2/(order C p q : ℝ)-2/(a.n : ℝ)| ≤ meanIntegral C u p q at ht
    linarith

#print axioms covered_sound
#print axioms input_family_of_certificates
end
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleAnchors
