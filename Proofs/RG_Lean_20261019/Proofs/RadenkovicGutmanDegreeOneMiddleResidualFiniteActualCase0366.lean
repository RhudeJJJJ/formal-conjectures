/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0366 : Family 9 := level9.get ⟨260,by decide⟩
def sourceMap0366 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0366 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0366_checked : acceptsGraphIso
    (source (graph core0366) (root 9) 2 2) DegreeOneMiddleResidualSpectrum885.graph sourceMap0366=true := by decide +kernel
theorem fusedMap0366_checked : acceptsGraphIso
    (fused (graph core0366) (root 9) 2 2) DegreeTwoThreeSpectrum4069.graph fusedMap0366=true := by decide +kernel
theorem certified0366 : Certified (graph core0366) (root 9) 2 2 :=
  of_native_maps core0366 DegreeOneMiddleResidualSpectrum885.graph DegreeTwoThreeSpectrum4069.graph
    sourceMap0366 fusedMap0366 sourceMap0366_checked fusedMap0366_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0366
#print axioms sourceMap0366_checked
#print axioms fusedMap0366_checked
#print axioms certified0366
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
