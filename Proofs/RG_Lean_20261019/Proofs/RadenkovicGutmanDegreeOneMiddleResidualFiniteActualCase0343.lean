/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0343 : Family 9 := level9.get ⟨218,by decide⟩
def sourceMap0343 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (sourceLabel 9 2 2 v)
def fusedMap0343 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0343_checked : acceptsGraphIso
    (source (graph core0343) (root 9) 2 2) DegreeOneMiddleResidualSpectrum847.graph sourceMap0343=true := by decide +kernel
theorem fusedMap0343_checked : acceptsGraphIso
    (fused (graph core0343) (root 9) 2 2) DegreeTwoThreeSpectrum4005.graph fusedMap0343=true := by decide +kernel
theorem certified0343 : Certified (graph core0343) (root 9) 2 2 :=
  of_native_maps core0343 DegreeOneMiddleResidualSpectrum847.graph DegreeTwoThreeSpectrum4005.graph
    sourceMap0343 fusedMap0343 sourceMap0343_checked fusedMap0343_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0343
#print axioms sourceMap0343_checked
#print axioms fusedMap0343_checked
#print axioms certified0343
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
