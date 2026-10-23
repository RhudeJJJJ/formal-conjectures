/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanComputedHornerArithmetic

/-! Complete coefficient programs retain arbitrary original rational shifts and
finite arms. Every generated field has the existing polynomial contract. -/
namespace Gebendorfer.RadenkovicGutman.ComputedGeneralPathData
open PolynomialPathMap
abbrev Poly := HornerCertificates.Poly
set_option maxHeartbeats 0
set_option maxRecDepth 100000

structure Data where
  a : Poly
  b : Poly
  c : Poly
  e : Poly
  U : Poly
  V : Poly
  J : Poly
  N : Poly
  E : Poly

def build (x : ℚ) (p q : ℕ) : Data :=
  let a := ComputedHornerArithmetic.trimZeros (FastGeneralPathCertificates.sourceSlopeList x p q)
  let b := ComputedHornerArithmetic.trimZeros (FastGeneralPathCertificates.sourceCenterList x p q)
  let c := ComputedHornerArithmetic.trimZeros (FastGeneralPathCertificates.fusedSlopeList x p q)
  let e := ComputedHornerArithmetic.trimZeros (FastGeneralPathCertificates.fusedCenterList x p q)
  {a:=a,b:=b,c:=c,e:=e,
   U:=ComputedHornerArithmetic.trimZeros (FastGeneralPathCertificates.UList a b c e),
   V:=ComputedHornerArithmetic.trimZeros (FastGeneralPathCertificates.VList a b c e),
   J:=ComputedHornerArithmetic.trimZeros (FastGeneralPathCertificates.JList a b),
   N:=ComputedHornerArithmetic.trimZeros (FastGeneralPathCertificates.NList a b),
   E:=ComputedHornerArithmetic.trimZeros (FastGeneralPathCertificates.EList c e)}

theorem path_checked (x : ℚ) (p q : ℕ) :
    GeneralPathPolynomials.accepts x p q (build x p q).a (build x p q).b
      (build x p q).c (build x p q).e=true := by
  rw [GeneralPathPolynomials.accepts,decide_eq_true_eq]
  exact ⟨(ComputedHornerArithmetic.ofList_trim _).trans (FastGeneralPathCertificates.sourceSlopeList_sound x p q),
    (ComputedHornerArithmetic.ofList_trim _).trans (FastGeneralPathCertificates.sourceCenterList_sound x p q),
    (ComputedHornerArithmetic.ofList_trim _).trans (FastGeneralPathCertificates.fusedSlopeList_sound x p q),
    (ComputedHornerArithmetic.ofList_trim _).trans (FastGeneralPathCertificates.fusedCenterList_sound x p q)⟩

theorem norms_checked (x : ℚ) (p q : ℕ) :
    RationalMobiusPolynomials.accepts (build x p q).a (build x p q).b (build x p q).c (build x p q).e
      (build x p q).U (build x p q).V (build x p q).J (build x p q).N (build x p q).E=true := by
  rw [RationalMobiusPolynomials.accepts,decide_eq_true_eq]
  exact ⟨(ComputedHornerArithmetic.ofList_trim _).trans (FastGeneralPathCertificates.UList_sound _ _ _ _),
    (ComputedHornerArithmetic.ofList_trim _).trans (FastGeneralPathCertificates.VList_sound _ _ _ _),
    (ComputedHornerArithmetic.ofList_trim _).trans (FastGeneralPathCertificates.JList_sound _ _),
    (ComputedHornerArithmetic.ofList_trim _).trans (FastGeneralPathCertificates.NList_sound _ _),
    (ComputedHornerArithmetic.ofList_trim _).trans (FastGeneralPathCertificates.EList_sound _ _)⟩

theorem path_swapped (x : ℚ) (p q : ℕ) :
    GeneralPathPolynomials.accepts x q p (build x p q).a (build x p q).b
      (build x p q).c (build x p q).e=true := by
  obtain ⟨ha,hb,hc,he⟩ := of_decide_eq_true (path_checked x p q)
  have hA : GeneralPathPolynomials.sourceSlope x p q=GeneralPathPolynomials.sourceSlope x q p := by
    unfold GeneralPathPolynomials.sourceSlope
    ring
  have hO : GeneralPathPolynomials.sourceOffset x p q=GeneralPathPolynomials.sourceOffset x q p := by
    unfold GeneralPathPolynomials.sourceOffset
    ring
  have hB : GeneralPathPolynomials.sourceCenter x p q=GeneralPathPolynomials.sourceCenter x q p := by
    simp only [GeneralPathPolynomials.sourceCenter,hA,hO]
  have hC : GeneralPathPolynomials.fusedSlope x p q=GeneralPathPolynomials.fusedSlope x q p := by
    simp only [GeneralPathPolynomials.fusedSlope,Nat.add_comm p q]
  have hE : GeneralPathPolynomials.fusedCenter x p q=GeneralPathPolynomials.fusedCenter x q p := by
    simp only [GeneralPathPolynomials.fusedCenter,GeneralPathPolynomials.fusedSlope,
      GeneralPathPolynomials.fusedOffset,Nat.add_comm p q]
  rw [GeneralPathPolynomials.accepts,decide_eq_true_eq]
  exact ⟨ha.trans hA,hb.trans hB,hc.trans hC,he.trans hE⟩

#print axioms path_checked
#print axioms norms_checked
#print axioms path_swapped
end Gebendorfer.RadenkovicGutman.ComputedGeneralPathData
