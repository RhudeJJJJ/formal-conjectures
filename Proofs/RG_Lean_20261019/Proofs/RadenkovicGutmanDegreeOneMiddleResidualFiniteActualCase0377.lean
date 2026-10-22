/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0377 : Family 9 := level9.get ⟨287,by decide⟩
def sourceMap0377 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0377 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0377_checked : acceptsGraphIso
    (source (graph core0377) (root 9) 2 2) DegreeOneMiddleResidualSpectrum897.graph sourceMap0377=true := by decide +kernel
theorem fusedMap0377_checked : acceptsGraphIso
    (fused (graph core0377) (root 9) 2 2) DegreeTwoThreeSpectrum4115.graph fusedMap0377=true := by decide +kernel
theorem certified0377 : Certified (graph core0377) (root 9) 2 2 :=
  of_native_maps core0377 DegreeOneMiddleResidualSpectrum897.graph DegreeTwoThreeSpectrum4115.graph
    sourceMap0377 fusedMap0377 sourceMap0377_checked fusedMap0377_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0377
#print axioms sourceMap0377_checked
#print axioms fusedMap0377_checked
#print axioms certified0377
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
