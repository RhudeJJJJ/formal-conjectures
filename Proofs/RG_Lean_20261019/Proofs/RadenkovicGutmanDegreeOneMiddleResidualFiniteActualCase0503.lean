/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0503 : Family 10 := level10.get ⟨21,by decide⟩
def sourceMap0503 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0503 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0503_checked : acceptsGraphIso
    (source (graph core0503) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1354.graph sourceMap0503=true := by decide +kernel
theorem fusedMap0503_checked : acceptsGraphIso
    (fused (graph core0503) (root 10) 2 2) DegreeTwoThreeSpectrum5033.graph fusedMap0503=true := by decide +kernel
theorem certified0503 : Certified (graph core0503) (root 10) 2 2 :=
  of_native_maps core0503 DegreeOneMiddleResidualSpectrum1354.graph DegreeTwoThreeSpectrum5033.graph
    sourceMap0503 fusedMap0503 sourceMap0503_checked fusedMap0503_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0503
#print axioms sourceMap0503_checked
#print axioms fusedMap0503_checked
#print axioms certified0503
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
