/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0020 : Family 7 := level7.get ⟨27,by decide⟩
def sourceMap0020 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0020 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0020_checked : acceptsGraphIso
    (source (graph core0020) (root 7) 2 2) DegreeOneMiddleResidualSpectrum059.graph sourceMap0020=true := by decide +kernel
theorem fusedMap0020_checked : acceptsGraphIso
    (fused (graph core0020) (root 7) 2 2) DegreeTwoThreeSpectrum1746.graph fusedMap0020=true := by decide +kernel
theorem certified0020 : Certified (graph core0020) (root 7) 2 2 :=
  of_native_maps core0020 DegreeOneMiddleResidualSpectrum059.graph DegreeTwoThreeSpectrum1746.graph
    sourceMap0020 fusedMap0020 sourceMap0020_checked fusedMap0020_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0020
#print axioms sourceMap0020_checked
#print axioms fusedMap0020_checked
#print axioms certified0020
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
