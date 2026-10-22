/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3945 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap3945 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3945 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3945_checked : acceptsGraphIso
    (source (graph core3945) (root 6) 1 5) DegreeTwoThreeSpectrum2815.graph sourceMap3945=true := by decide +kernel
theorem fusedMap3945_checked : acceptsGraphIso
    (fused (graph core3945) (root 6) 1 5) DegreeTwoThreeSpectrum2381.graph fusedMap3945=true := by decide +kernel
theorem certified3945 : Certified (graph core3945) (root 6) 1 5 :=
  of_native_maps core3945 DegreeTwoThreeSpectrum2815.graph DegreeTwoThreeSpectrum2381.graph
    sourceMap3945 fusedMap3945 sourceMap3945_checked fusedMap3945_checked
    DegreeTwoThreeFiniteComparisons.comparison3945
#print axioms sourceMap3945_checked
#print axioms fusedMap3945_checked
#print axioms certified3945
def sourceMap3945swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,10,11,12,13,14,8,9] (sourceLabel 6 5 1 v)
def fusedMap3945swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3945swap_checked : acceptsGraphIso
    (source (graph core3945) (root 6) 5 1) DegreeTwoThreeSpectrum2815.graph sourceMap3945swap=true := by decide +kernel
theorem fusedMap3945swap_checked : acceptsGraphIso
    (fused (graph core3945) (root 6) 5 1) DegreeTwoThreeSpectrum2381.graph fusedMap3945swap=true := by decide +kernel
theorem certified3945swap : Certified (graph core3945) (root 6) 5 1 :=
  of_native_maps core3945 DegreeTwoThreeSpectrum2815.graph DegreeTwoThreeSpectrum2381.graph
    sourceMap3945swap fusedMap3945swap sourceMap3945swap_checked fusedMap3945swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3945
#print axioms sourceMap3945swap_checked
#print axioms fusedMap3945swap_checked
#print axioms certified3945swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
