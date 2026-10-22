/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0539 : Family 10 := level10.get ⟨67,by decide⟩
def sourceMap0539 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0539 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0539_checked : acceptsGraphIso
    (source (graph core0539) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1672.graph sourceMap0539=true := by decide +kernel
theorem fusedMap0539_checked : acceptsGraphIso
    (fused (graph core0539) (root 10) 2 2) DegreeTwoThreeSpectrum4981.graph fusedMap0539=true := by decide +kernel
theorem certified0539 : Certified (graph core0539) (root 10) 2 2 :=
  of_native_maps core0539 DegreeOneMiddleResidualSpectrum1672.graph DegreeTwoThreeSpectrum4981.graph
    sourceMap0539 fusedMap0539 sourceMap0539_checked fusedMap0539_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0539
#print axioms sourceMap0539_checked
#print axioms fusedMap0539_checked
#print axioms certified0539
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
