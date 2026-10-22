/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0298 : Family 9 := level9.get ⟨143,by decide⟩
def sourceMap0298 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0298 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0298_checked : acceptsGraphIso
    (source (graph core0298) (root 9) 2 2) DegreeOneMiddleResidualSpectrum755.graph sourceMap0298=true := by decide +kernel
theorem fusedMap0298_checked : acceptsGraphIso
    (fused (graph core0298) (root 9) 2 2) DegreeTwoThreeSpectrum3898.graph fusedMap0298=true := by decide +kernel
theorem certified0298 : Certified (graph core0298) (root 9) 2 2 :=
  of_native_maps core0298 DegreeOneMiddleResidualSpectrum755.graph DegreeTwoThreeSpectrum3898.graph
    sourceMap0298 fusedMap0298 sourceMap0298_checked fusedMap0298_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0298
#print axioms sourceMap0298_checked
#print axioms fusedMap0298_checked
#print axioms certified0298
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
