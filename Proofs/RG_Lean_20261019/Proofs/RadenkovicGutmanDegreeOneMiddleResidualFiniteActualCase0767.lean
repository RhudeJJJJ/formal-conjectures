/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0767 : Family 10 := level10.get ⟨416,by decide⟩
def sourceMap0767 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0767 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0767_checked : acceptsGraphIso
    (source (graph core0767) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1841.graph sourceMap0767=true := by decide +kernel
theorem fusedMap0767_checked : acceptsGraphIso
    (fused (graph core0767) (root 10) 2 2) DegreeTwoThreeSpectrum5798.graph fusedMap0767=true := by decide +kernel
theorem certified0767 : Certified (graph core0767) (root 10) 2 2 :=
  of_native_maps core0767 DegreeOneMiddleResidualSpectrum1841.graph DegreeTwoThreeSpectrum5798.graph
    sourceMap0767 fusedMap0767 sourceMap0767_checked fusedMap0767_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0767
#print axioms sourceMap0767_checked
#print axioms fusedMap0767_checked
#print axioms certified0767
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
