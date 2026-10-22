/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0820 : Family 10 := level10.get ⟨1262,by decide⟩
def sourceMap0820 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0820 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0820_checked : acceptsGraphIso
    (source (graph core0820) (root 10) 0 0) DegreeTwoThreeSpectrum1411.graph sourceMap0820=true := by decide +kernel
theorem fusedMap0820_checked : acceptsGraphIso
    (fused (graph core0820) (root 10) 0 0) DegreeOneSmallSpectrum1910.graph fusedMap0820=true := by decide +kernel
theorem certified0820 : Certified (graph core0820) (root 10) 0 0 :=
  of_native_maps core0820 DegreeTwoThreeSpectrum1411.graph DegreeOneSmallSpectrum1910.graph
    sourceMap0820 fusedMap0820 sourceMap0820_checked fusedMap0820_checked
    DegreeTwoThreeFiniteComparisons.comparison0820
#print axioms sourceMap0820_checked
#print axioms fusedMap0820_checked
#print axioms certified0820
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
