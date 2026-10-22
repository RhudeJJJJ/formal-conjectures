/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0463 : Family 9 := level9.get ⟨543,by decide⟩
def sourceMap0463 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0463 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0463_checked : acceptsGraphIso
    (source (graph core0463) (root 9) 2 2) DegreeOneMiddleResidualSpectrum907.graph sourceMap0463=true := by decide +kernel
theorem fusedMap0463_checked : acceptsGraphIso
    (fused (graph core0463) (root 9) 2 2) DegreeTwoThreeSpectrum4171.graph fusedMap0463=true := by decide +kernel
theorem certified0463 : Certified (graph core0463) (root 9) 2 2 :=
  of_native_maps core0463 DegreeOneMiddleResidualSpectrum907.graph DegreeTwoThreeSpectrum4171.graph
    sourceMap0463 fusedMap0463 sourceMap0463_checked fusedMap0463_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0463
#print axioms sourceMap0463_checked
#print axioms fusedMap0463_checked
#print axioms certified0463
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
