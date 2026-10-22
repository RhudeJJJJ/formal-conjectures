/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0672 : Family 10 := level10.get ⟨260,by decide⟩
def sourceMap0672 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0672 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0672_checked : acceptsGraphIso
    (source (graph core0672) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1687.graph sourceMap0672=true := by decide +kernel
theorem fusedMap0672_checked : acceptsGraphIso
    (fused (graph core0672) (root 10) 2 2) DegreeTwoThreeSpectrum5371.graph fusedMap0672=true := by decide +kernel
theorem certified0672 : Certified (graph core0672) (root 10) 2 2 :=
  of_native_maps core0672 DegreeOneMiddleResidualSpectrum1687.graph DegreeTwoThreeSpectrum5371.graph
    sourceMap0672 fusedMap0672 sourceMap0672_checked fusedMap0672_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0672
#print axioms sourceMap0672_checked
#print axioms fusedMap0672_checked
#print axioms certified0672
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
