/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0044 : Family 7 := level7.get ⟨81,by decide⟩
def sourceMap0044 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 2 2 v)
def fusedMap0044 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0044_checked : acceptsGraphIso
    (source (graph core0044) (root 7) 2 2) DegreeOneMiddleResidualSpectrum101.graph sourceMap0044=true := by decide +kernel
theorem fusedMap0044_checked : acceptsGraphIso
    (fused (graph core0044) (root 7) 2 2) DegreeTwoThreeSpectrum1804.graph fusedMap0044=true := by decide +kernel
theorem certified0044 : Certified (graph core0044) (root 7) 2 2 :=
  of_native_maps core0044 DegreeOneMiddleResidualSpectrum101.graph DegreeTwoThreeSpectrum1804.graph
    sourceMap0044 fusedMap0044 sourceMap0044_checked fusedMap0044_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0044
#print axioms sourceMap0044_checked
#print axioms fusedMap0044_checked
#print axioms certified0044
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
