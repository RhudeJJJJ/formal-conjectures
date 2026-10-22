/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0004 : Family 7 := level7.get ⟨4,by decide⟩
def sourceMap0004 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 3) → Fin 14 :=
  fun v => ![1,0,8,9,10,11,12,13,2,3,4,5,6,7] (sourceLabel 7 2 2 v)
def fusedMap0004 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (fusedLabel 7 2 2 v)
theorem sourceMap0004_checked : acceptsGraphIso
    (source (graph core0004) (root 7) 2 2) DegreeTwoThreeSpectrum1860.graph sourceMap0004=true := by decide +kernel
theorem fusedMap0004_checked : acceptsGraphIso
    (fused (graph core0004) (root 7) 2 2) DegreeTwoThreeSpectrum1734.graph fusedMap0004=true := by decide +kernel
theorem certified0004 : Certified (graph core0004) (root 7) 2 2 :=
  of_native_maps core0004 DegreeTwoThreeSpectrum1860.graph DegreeTwoThreeSpectrum1734.graph
    sourceMap0004 fusedMap0004 sourceMap0004_checked fusedMap0004_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0004
#print axioms sourceMap0004_checked
#print axioms fusedMap0004_checked
#print axioms certified0004
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
