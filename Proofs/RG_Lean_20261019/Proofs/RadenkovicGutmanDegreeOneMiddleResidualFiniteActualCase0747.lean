/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0747 : Family 10 := level10.get ⟨382,by decide⟩
def sourceMap0747 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0747 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0747_checked : acceptsGraphIso
    (source (graph core0747) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1905.graph sourceMap0747=true := by decide +kernel
theorem fusedMap0747_checked : acceptsGraphIso
    (fused (graph core0747) (root 10) 2 2) DegreeTwoThreeSpectrum5709.graph fusedMap0747=true := by decide +kernel
theorem certified0747 : Certified (graph core0747) (root 10) 2 2 :=
  of_native_maps core0747 DegreeOneMiddleResidualSpectrum1905.graph DegreeTwoThreeSpectrum5709.graph
    sourceMap0747 fusedMap0747 sourceMap0747_checked fusedMap0747_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0747
#print axioms sourceMap0747_checked
#print axioms fusedMap0747_checked
#print axioms certified0747
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
