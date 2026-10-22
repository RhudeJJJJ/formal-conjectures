/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0083 : Family 8 := level8.get ⟨29,by decide⟩
def sourceMap0083 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,10,11,12,13,14,8,9,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0083 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0083_checked : acceptsGraphIso
    (source (graph core0083) (root 8) 2 2) DegreeOneMiddleResidualSpectrum235.graph sourceMap0083=true := by decide +kernel
theorem fusedMap0083_checked : acceptsGraphIso
    (fused (graph core0083) (root 8) 2 2) DegreeTwoThreeSpectrum2431.graph fusedMap0083=true := by decide +kernel
theorem certified0083 : Certified (graph core0083) (root 8) 2 2 :=
  of_native_maps core0083 DegreeOneMiddleResidualSpectrum235.graph DegreeTwoThreeSpectrum2431.graph
    sourceMap0083 fusedMap0083 sourceMap0083_checked fusedMap0083_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0083
#print axioms sourceMap0083_checked
#print axioms fusedMap0083_checked
#print axioms certified0083
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
