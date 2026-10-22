/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0325 : Family 9 := level9.get ⟨183,by decide⟩
def sourceMap0325 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap0325 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0325_checked : acceptsGraphIso
    (source (graph core0325) (root 9) 2 2) DegreeOneMiddleResidualSpectrum811.graph sourceMap0325=true := by decide +kernel
theorem fusedMap0325_checked : acceptsGraphIso
    (fused (graph core0325) (root 9) 2 2) DegreeTwoThreeSpectrum3951.graph fusedMap0325=true := by decide +kernel
theorem certified0325 : Certified (graph core0325) (root 9) 2 2 :=
  of_native_maps core0325 DegreeOneMiddleResidualSpectrum811.graph DegreeTwoThreeSpectrum3951.graph
    sourceMap0325 fusedMap0325 sourceMap0325_checked fusedMap0325_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0325
#print axioms sourceMap0325_checked
#print axioms fusedMap0325_checked
#print axioms certified0325
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
