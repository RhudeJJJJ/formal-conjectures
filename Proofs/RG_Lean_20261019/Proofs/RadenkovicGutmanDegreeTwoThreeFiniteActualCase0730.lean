/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0730 : Family 10 := level10.get ⟨1039,by decide⟩
def sourceMap0730 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0730 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0730_checked : acceptsGraphIso
    (source (graph core0730) (root 10) 0 0) DegreeTwoThreeSpectrum1374.graph sourceMap0730=true := by decide +kernel
theorem fusedMap0730_checked : acceptsGraphIso
    (fused (graph core0730) (root 10) 0 0) DegreeOneSmallSpectrum1628.graph fusedMap0730=true := by decide +kernel
theorem certified0730 : Certified (graph core0730) (root 10) 0 0 :=
  of_native_maps core0730 DegreeTwoThreeSpectrum1374.graph DegreeOneSmallSpectrum1628.graph
    sourceMap0730 fusedMap0730 sourceMap0730_checked fusedMap0730_checked
    DegreeTwoThreeFiniteComparisons.comparison0730
#print axioms sourceMap0730_checked
#print axioms fusedMap0730_checked
#print axioms certified0730
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
