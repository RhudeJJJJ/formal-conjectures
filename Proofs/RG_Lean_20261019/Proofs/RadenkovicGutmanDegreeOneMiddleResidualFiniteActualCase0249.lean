/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0249 : Family 9 := level9.get ⟨64,by decide⟩
def sourceMap0249 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap0249 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0249_checked : acceptsGraphIso
    (source (graph core0249) (root 9) 2 2) DegreeOneMiddleResidualSpectrum632.graph sourceMap0249=true := by decide +kernel
theorem fusedMap0249_checked : acceptsGraphIso
    (fused (graph core0249) (root 9) 2 2) DegreeTwoThreeSpectrum3974.graph fusedMap0249=true := by decide +kernel
theorem certified0249 : Certified (graph core0249) (root 9) 2 2 :=
  of_native_maps core0249 DegreeOneMiddleResidualSpectrum632.graph DegreeTwoThreeSpectrum3974.graph
    sourceMap0249 fusedMap0249 sourceMap0249_checked fusedMap0249_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0249
#print axioms sourceMap0249_checked
#print axioms fusedMap0249_checked
#print axioms certified0249
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
