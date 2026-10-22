/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0015 : Family 7 := level7.get ⟨18,by decide⟩
def sourceMap0015 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,2,3,4,5,6,7] (sourceLabel 7 2 2 v)
def fusedMap0015 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0015_checked : acceptsGraphIso
    (source (graph core0015) (root 7) 2 2) DegreeTwoThreeSpectrum2188.graph sourceMap0015=true := by decide +kernel
theorem fusedMap0015_checked : acceptsGraphIso
    (fused (graph core0015) (root 7) 2 2) DegreeTwoThreeSpectrum1724.graph fusedMap0015=true := by decide +kernel
theorem certified0015 : Certified (graph core0015) (root 7) 2 2 :=
  of_native_maps core0015 DegreeTwoThreeSpectrum2188.graph DegreeTwoThreeSpectrum1724.graph
    sourceMap0015 fusedMap0015 sourceMap0015_checked fusedMap0015_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0015
#print axioms sourceMap0015_checked
#print axioms fusedMap0015_checked
#print axioms certified0015
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
