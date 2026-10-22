/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons11
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0581 : Family 10 := level10.get ⟨123,by decide⟩
def sourceMap0581 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,16,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0581 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0581_checked : acceptsGraphIso
    (source (graph core0581) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1907.graph sourceMap0581=true := by decide +kernel
theorem fusedMap0581_checked : acceptsGraphIso
    (fused (graph core0581) (root 10) 2 2) DegreeTwoThreeSpectrum5052.graph fusedMap0581=true := by decide +kernel
theorem certified0581 : Certified (graph core0581) (root 10) 2 2 :=
  of_native_maps core0581 DegreeOneMiddleResidualSpectrum1907.graph DegreeTwoThreeSpectrum5052.graph
    sourceMap0581 fusedMap0581 sourceMap0581_checked fusedMap0581_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0581
#print axioms sourceMap0581_checked
#print axioms fusedMap0581_checked
#print axioms certified0581
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
