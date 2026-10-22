/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0288 : Family 9 := level9.get ⟨121,by decide⟩
def sourceMap0288 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,10,11,12,13,14,15,8,9,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0288 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0288_checked : acceptsGraphIso
    (source (graph core0288) (root 9) 2 2) DegreeOneMiddleResidualSpectrum698.graph sourceMap0288=true := by decide +kernel
theorem fusedMap0288_checked : acceptsGraphIso
    (fused (graph core0288) (root 9) 2 2) DegreeTwoThreeSpectrum4143.graph fusedMap0288=true := by decide +kernel
theorem certified0288 : Certified (graph core0288) (root 9) 2 2 :=
  of_native_maps core0288 DegreeOneMiddleResidualSpectrum698.graph DegreeTwoThreeSpectrum4143.graph
    sourceMap0288 fusedMap0288 sourceMap0288_checked fusedMap0288_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0288
#print axioms sourceMap0288_checked
#print axioms fusedMap0288_checked
#print axioms certified0288
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
