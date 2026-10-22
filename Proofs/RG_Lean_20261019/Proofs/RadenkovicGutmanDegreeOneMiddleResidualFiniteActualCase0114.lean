/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0114 : Family 8 := level8.get ⟨76,by decide⟩
def sourceMap0114 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,8,9,10,11,12,13,14,2,3,4,5,6,7] (sourceLabel 8 2 2 v)
def fusedMap0114 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0114_checked : acceptsGraphIso
    (source (graph core0114) (root 8) 2 2) DegreeTwoThreeSpectrum3632.graph sourceMap0114=true := by decide +kernel
theorem fusedMap0114_checked : acceptsGraphIso
    (fused (graph core0114) (root 8) 2 2) DegreeTwoThreeSpectrum2388.graph fusedMap0114=true := by decide +kernel
theorem certified0114 : Certified (graph core0114) (root 8) 2 2 :=
  of_native_maps core0114 DegreeTwoThreeSpectrum3632.graph DegreeTwoThreeSpectrum2388.graph
    sourceMap0114 fusedMap0114 sourceMap0114_checked fusedMap0114_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0114
#print axioms sourceMap0114_checked
#print axioms fusedMap0114_checked
#print axioms certified0114
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
