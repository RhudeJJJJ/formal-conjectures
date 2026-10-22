/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0223 : Family 9 := level9.get ⟨29,by decide⟩
def sourceMap0223 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,9,10,11,12,13,14,15,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap0223 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0223_checked : acceptsGraphIso
    (source (graph core0223) (root 9) 2 2) DegreeOneMiddleResidualSpectrum723.graph sourceMap0223=true := by decide +kernel
theorem fusedMap0223_checked : acceptsGraphIso
    (fused (graph core0223) (root 9) 2 2) DegreeTwoThreeSpectrum3877.graph fusedMap0223=true := by decide +kernel
theorem certified0223 : Certified (graph core0223) (root 9) 2 2 :=
  of_native_maps core0223 DegreeOneMiddleResidualSpectrum723.graph DegreeTwoThreeSpectrum3877.graph
    sourceMap0223 fusedMap0223 sourceMap0223_checked fusedMap0223_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0223
#print axioms sourceMap0223_checked
#print axioms fusedMap0223_checked
#print axioms certified0223
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
