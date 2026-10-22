/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0718 : Family 10 := level10.get ⟨333,by decide⟩
def sourceMap0718 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0718 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0718_checked : acceptsGraphIso
    (source (graph core0718) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1803.graph sourceMap0718=true := by decide +kernel
theorem fusedMap0718_checked : acceptsGraphIso
    (fused (graph core0718) (root 10) 2 2) DegreeTwoThreeSpectrum5577.graph fusedMap0718=true := by decide +kernel
theorem certified0718 : Certified (graph core0718) (root 10) 2 2 :=
  of_native_maps core0718 DegreeOneMiddleResidualSpectrum1803.graph DegreeTwoThreeSpectrum5577.graph
    sourceMap0718 fusedMap0718 sourceMap0718_checked fusedMap0718_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0718
#print axioms sourceMap0718_checked
#print axioms fusedMap0718_checked
#print axioms certified0718
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
