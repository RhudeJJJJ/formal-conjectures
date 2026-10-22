/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0023 : Family 7 := level7.get ⟨31,by decide⟩
def sourceMap0023 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0023 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0023_checked : acceptsGraphIso
    (source (graph core0023) (root 7) 2 2) DegreeOneMiddleResidualSpectrum064.graph sourceMap0023=true := by decide +kernel
theorem fusedMap0023_checked : acceptsGraphIso
    (fused (graph core0023) (root 7) 2 2) DegreeTwoThreeSpectrum1764.graph fusedMap0023=true := by decide +kernel
theorem certified0023 : Certified (graph core0023) (root 7) 2 2 :=
  of_native_maps core0023 DegreeOneMiddleResidualSpectrum064.graph DegreeTwoThreeSpectrum1764.graph
    sourceMap0023 fusedMap0023 sourceMap0023_checked fusedMap0023_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0023
#print axioms sourceMap0023_checked
#print axioms fusedMap0023_checked
#print axioms certified0023
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
