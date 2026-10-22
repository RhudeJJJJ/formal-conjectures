/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0517 : Family 10 := level10.get ⟨37,by decide⟩
def sourceMap0517 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![2,1,0,10,11,12,13,14,15,16,9,3,4,5,6,7,8] (sourceLabel 10 2 2 v)
def fusedMap0517 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap0517_checked : acceptsGraphIso
    (source (graph core0517) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1371.graph sourceMap0517=true := by decide +kernel
theorem fusedMap0517_checked : acceptsGraphIso
    (fused (graph core0517) (root 10) 2 2) DegreeTwoThreeSpectrum5105.graph fusedMap0517=true := by decide +kernel
theorem certified0517 : Certified (graph core0517) (root 10) 2 2 :=
  of_native_maps core0517 DegreeOneMiddleResidualSpectrum1371.graph DegreeTwoThreeSpectrum5105.graph
    sourceMap0517 fusedMap0517 sourceMap0517_checked fusedMap0517_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0517
#print axioms sourceMap0517_checked
#print axioms fusedMap0517_checked
#print axioms certified0517
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
