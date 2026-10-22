/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0211 : Family 9 := level9.get ⟨14,by decide⟩
def sourceMap0211 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap0211 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0211_checked : acceptsGraphIso
    (source (graph core0211) (root 9) 2 2) DegreeOneMiddleResidualSpectrum634.graph sourceMap0211=true := by decide +kernel
theorem fusedMap0211_checked : acceptsGraphIso
    (fused (graph core0211) (root 9) 2 2) DegreeTwoThreeSpectrum3859.graph fusedMap0211=true := by decide +kernel
theorem certified0211 : Certified (graph core0211) (root 9) 2 2 :=
  of_native_maps core0211 DegreeOneMiddleResidualSpectrum634.graph DegreeTwoThreeSpectrum3859.graph
    sourceMap0211 fusedMap0211 sourceMap0211_checked fusedMap0211_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0211
#print axioms sourceMap0211_checked
#print axioms fusedMap0211_checked
#print axioms certified0211
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
