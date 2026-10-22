/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0525 : Family 10 := level10.get ⟨48,by decide⟩
def sourceMap0525 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,11,12,13,14,15,16,9,10,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0525 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (fusedLabel 10 2 2 v)
theorem sourceMap0525_checked : acceptsGraphIso
    (source (graph core0525) (root 10) 2 2) DegreeTwoThreeSpectrum5662.graph sourceMap0525=true := by decide +kernel
theorem fusedMap0525_checked : acceptsGraphIso
    (fused (graph core0525) (root 10) 2 2) DegreeTwoThreeSpectrum5133.graph fusedMap0525=true := by decide +kernel
theorem certified0525 : Certified (graph core0525) (root 10) 2 2 :=
  of_native_maps core0525 DegreeTwoThreeSpectrum5662.graph DegreeTwoThreeSpectrum5133.graph
    sourceMap0525 fusedMap0525 sourceMap0525_checked fusedMap0525_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0525
#print axioms sourceMap0525_checked
#print axioms fusedMap0525_checked
#print axioms certified0525
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
