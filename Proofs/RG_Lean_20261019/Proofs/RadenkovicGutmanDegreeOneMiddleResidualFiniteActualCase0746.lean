/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0746 : Family 10 := level10.get ⟨381,by decide⟩
def sourceMap0746 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0746 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0746_checked : acceptsGraphIso
    (source (graph core0746) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1904.graph sourceMap0746=true := by decide +kernel
theorem fusedMap0746_checked : acceptsGraphIso
    (fused (graph core0746) (root 10) 2 2) DegreeTwoThreeSpectrum5707.graph fusedMap0746=true := by decide +kernel
theorem certified0746 : Certified (graph core0746) (root 10) 2 2 :=
  of_native_maps core0746 DegreeOneMiddleResidualSpectrum1904.graph DegreeTwoThreeSpectrum5707.graph
    sourceMap0746 fusedMap0746 sourceMap0746_checked fusedMap0746_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0746
#print axioms sourceMap0746_checked
#print axioms fusedMap0746_checked
#print axioms certified0746
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
