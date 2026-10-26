/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3813 : Family 7 := level7.get ⟨74,by decide⟩
def sourceMap3813 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,8,9,0,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3813 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3813_checked : acceptsGraphIso
    (source (graph core3813) (root 7) 1 4) DegreeTwoThreeSpectrum3221.graph sourceMap3813=true := by decide +kernel
theorem fusedMap3813_checked : acceptsGraphIso
    (fused (graph core3813) (root 7) 1 4) DegreeTwoThreeSpectrum2525.graph fusedMap3813=true := by decide +kernel
theorem certified3813 : Certified (graph core3813) (root 7) 1 4 :=
  of_native_maps core3813 DegreeTwoThreeSpectrum3221.graph DegreeTwoThreeSpectrum2525.graph
    sourceMap3813 fusedMap3813 sourceMap3813_checked fusedMap3813_checked
    DegreeTwoThreeFiniteComparisons.comparison3813
#print axioms sourceMap3813_checked
#print axioms fusedMap3813_checked
#print axioms certified3813
def sourceMap3813swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,10,0,11,12,13,14,8,9] (sourceLabel 7 4 1 v)
def fusedMap3813swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3813swap_checked : acceptsGraphIso
    (source (graph core3813) (root 7) 4 1) DegreeTwoThreeSpectrum3221.graph sourceMap3813swap=true := by decide +kernel
theorem fusedMap3813swap_checked : acceptsGraphIso
    (fused (graph core3813) (root 7) 4 1) DegreeTwoThreeSpectrum2525.graph fusedMap3813swap=true := by decide +kernel
theorem certified3813swap : Certified (graph core3813) (root 7) 4 1 :=
  of_native_maps core3813 DegreeTwoThreeSpectrum3221.graph DegreeTwoThreeSpectrum2525.graph
    sourceMap3813swap fusedMap3813swap sourceMap3813swap_checked fusedMap3813swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3813
#print axioms sourceMap3813swap_checked
#print axioms fusedMap3813swap_checked
#print axioms certified3813swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
