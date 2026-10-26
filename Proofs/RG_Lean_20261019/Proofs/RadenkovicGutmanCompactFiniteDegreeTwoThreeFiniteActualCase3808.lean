/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons76
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3808 : Family 7 := level7.get ⟨59,by decide⟩
def sourceMap3808 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 7 1 4 v)
def fusedMap3808 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 1 4 v)
theorem sourceMap3808_checked : acceptsGraphIso
    (source (graph core3808) (root 7) 1 4) DegreeTwoThreeSpectrum2965.graph sourceMap3808=true := by decide +kernel
theorem fusedMap3808_checked : acceptsGraphIso
    (fused (graph core3808) (root 7) 1 4) DegreeTwoThreeSpectrum2409.graph fusedMap3808=true := by decide +kernel
theorem certified3808 : Certified (graph core3808) (root 7) 1 4 :=
  of_native_maps core3808 DegreeTwoThreeSpectrum2965.graph DegreeTwoThreeSpectrum2409.graph
    sourceMap3808 fusedMap3808 sourceMap3808_checked fusedMap3808_checked
    DegreeTwoThreeFiniteComparisons.comparison3808
#print axioms sourceMap3808_checked
#print axioms fusedMap3808_checked
#print axioms certified3808
def sourceMap3808swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 2) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,10,11,12,13,14,8,9] (sourceLabel 7 4 1 v)
def fusedMap3808swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 4 1 v)
theorem sourceMap3808swap_checked : acceptsGraphIso
    (source (graph core3808) (root 7) 4 1) DegreeTwoThreeSpectrum2965.graph sourceMap3808swap=true := by decide +kernel
theorem fusedMap3808swap_checked : acceptsGraphIso
    (fused (graph core3808) (root 7) 4 1) DegreeTwoThreeSpectrum2409.graph fusedMap3808swap=true := by decide +kernel
theorem certified3808swap : Certified (graph core3808) (root 7) 4 1 :=
  of_native_maps core3808 DegreeTwoThreeSpectrum2965.graph DegreeTwoThreeSpectrum2409.graph
    sourceMap3808swap fusedMap3808swap sourceMap3808swap_checked fusedMap3808swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3808
#print axioms sourceMap3808swap_checked
#print axioms fusedMap3808swap_checked
#print axioms certified3808swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
