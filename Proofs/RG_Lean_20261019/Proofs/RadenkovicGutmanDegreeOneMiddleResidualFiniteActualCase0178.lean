/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0178 : Family 6 := level6.get ⟨4,by decide⟩
def sourceMap0178 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11] (sourceLabel 6 2 4 v)
def fusedMap0178 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap0178_checked : acceptsGraphIso
    (source (graph core0178) (root 6) 2 4) DegreeTwoThreeSpectrum2989.graph sourceMap0178=true := by decide +kernel
theorem fusedMap0178_checked : acceptsGraphIso
    (fused (graph core0178) (root 6) 2 4) DegreeTwoThreeSpectrum2312.graph fusedMap0178=true := by decide +kernel
theorem certified0178 : Certified (graph core0178) (root 6) 2 4 :=
  of_native_maps core0178 DegreeTwoThreeSpectrum2989.graph DegreeTwoThreeSpectrum2312.graph
    sourceMap0178 fusedMap0178 sourceMap0178_checked fusedMap0178_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0178
#print axioms sourceMap0178_checked
#print axioms fusedMap0178_checked
#print axioms certified0178
def sourceMap0178swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 6 4 2 v)
def fusedMap0178swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap0178swap_checked : acceptsGraphIso
    (source (graph core0178) (root 6) 4 2) DegreeTwoThreeSpectrum2989.graph sourceMap0178swap=true := by decide +kernel
theorem fusedMap0178swap_checked : acceptsGraphIso
    (fused (graph core0178) (root 6) 4 2) DegreeTwoThreeSpectrum2312.graph fusedMap0178swap=true := by decide +kernel
theorem certified0178swap : Certified (graph core0178) (root 6) 4 2 :=
  of_native_maps core0178 DegreeTwoThreeSpectrum2989.graph DegreeTwoThreeSpectrum2312.graph
    sourceMap0178swap fusedMap0178swap sourceMap0178swap_checked fusedMap0178swap_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0178
#print axioms sourceMap0178swap_checked
#print axioms fusedMap0178swap_checked
#print axioms certified0178swap
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
