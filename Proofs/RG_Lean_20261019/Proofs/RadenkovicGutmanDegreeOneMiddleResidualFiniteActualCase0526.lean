/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0526 : Family 10 := level10.get ⟨49,by decide⟩
def sourceMap0526 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,9,10,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0526 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (fusedLabel 10 2 2 v)
theorem sourceMap0526_checked : acceptsGraphIso
    (source (graph core0526) (root 10) 2 2) DegreeTwoThreeSpectrum5663.graph sourceMap0526=true := by decide +kernel
theorem fusedMap0526_checked : acceptsGraphIso
    (fused (graph core0526) (root 10) 2 2) DegreeTwoThreeSpectrum5134.graph fusedMap0526=true := by decide +kernel
theorem certified0526 : Certified (graph core0526) (root 10) 2 2 :=
  of_native_maps core0526 DegreeTwoThreeSpectrum5663.graph DegreeTwoThreeSpectrum5134.graph
    sourceMap0526 fusedMap0526 sourceMap0526_checked fusedMap0526_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0526
#print axioms sourceMap0526_checked
#print axioms fusedMap0526_checked
#print axioms certified0526
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
