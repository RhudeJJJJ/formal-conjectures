/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3647 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap3647 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (sourceLabel 6 0 7 v)
def fusedMap3647 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 0 7 v)
theorem sourceMap3647_checked : acceptsGraphIso
    (source (graph core3647) (root 6) 0 7) DegreeTwoThreeSpectrum3965.graph sourceMap3647=true := by decide +kernel
theorem fusedMap3647_checked : acceptsGraphIso
    (fused (graph core3647) (root 6) 0 7) DegreeTwoThreeSpectrum3857.graph fusedMap3647=true := by decide +kernel
theorem certified3647 : Certified (graph core3647) (root 6) 0 7 :=
  of_native_maps core3647 DegreeTwoThreeSpectrum3965.graph DegreeTwoThreeSpectrum3857.graph
    sourceMap3647 fusedMap3647 sourceMap3647_checked fusedMap3647_checked
    DegreeTwoThreeFiniteComparisons.comparison3647
#print axioms sourceMap3647_checked
#print axioms fusedMap3647_checked
#print axioms certified3647
def sourceMap3647swap : (Vertices 6 ⊕ Fin 8 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,9] (sourceLabel 6 7 0 v)
def fusedMap3647swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 7 0 v)
theorem sourceMap3647swap_checked : acceptsGraphIso
    (source (graph core3647) (root 6) 7 0) DegreeTwoThreeSpectrum3965.graph sourceMap3647swap=true := by decide +kernel
theorem fusedMap3647swap_checked : acceptsGraphIso
    (fused (graph core3647) (root 6) 7 0) DegreeTwoThreeSpectrum3857.graph fusedMap3647swap=true := by decide +kernel
theorem certified3647swap : Certified (graph core3647) (root 6) 7 0 :=
  of_native_maps core3647 DegreeTwoThreeSpectrum3965.graph DegreeTwoThreeSpectrum3857.graph
    sourceMap3647swap fusedMap3647swap sourceMap3647swap_checked fusedMap3647swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3647
#print axioms sourceMap3647swap_checked
#print axioms fusedMap3647swap_checked
#print axioms certified3647swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
