/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0708 : Family 10 := level10.get ⟨318,by decide⟩
def sourceMap0708 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap0708 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0708_checked : acceptsGraphIso
    (source (graph core0708) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1779.graph sourceMap0708=true := by decide +kernel
theorem fusedMap0708_checked : acceptsGraphIso
    (fused (graph core0708) (root 10) 2 2) DegreeTwoThreeSpectrum5532.graph fusedMap0708=true := by decide +kernel
theorem certified0708 : Certified (graph core0708) (root 10) 2 2 :=
  of_native_maps core0708 DegreeOneMiddleResidualSpectrum1779.graph DegreeTwoThreeSpectrum5532.graph
    sourceMap0708 fusedMap0708 sourceMap0708_checked fusedMap0708_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0708
#print axioms sourceMap0708_checked
#print axioms fusedMap0708_checked
#print axioms certified0708
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
