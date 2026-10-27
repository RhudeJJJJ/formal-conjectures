/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3999 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap3999 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13,14,15] (sourceLabel 6 1 6 v)
def fusedMap3999 : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 1 6 v)
theorem sourceMap3999_checked : acceptsGraphIso
    (source (graph core3999) (root 6) 1 6) DegreeTwoThreeSpectrum3961.graph sourceMap3999=true := by decide +kernel
theorem fusedMap3999_checked : acceptsGraphIso
    (fused (graph core3999) (root 6) 1 6) DegreeTwoThreeSpectrum3857.graph fusedMap3999=true := by decide +kernel
theorem certified3999 : Certified (graph core3999) (root 6) 1 6 :=
  of_native_maps core3999 DegreeTwoThreeSpectrum3961.graph DegreeTwoThreeSpectrum3857.graph
    sourceMap3999 fusedMap3999 sourceMap3999_checked fusedMap3999_checked
    DegreeTwoThreeFiniteComparisons.comparison3999
#print axioms sourceMap3999_checked
#print axioms fusedMap3999_checked
#print axioms certified3999
def sourceMap3999swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,14,15,7,8] (sourceLabel 6 6 1 v)
def fusedMap3999swap : (Vertices 6 ⊕ Fin 9) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15] (fusedLabel 6 6 1 v)
theorem sourceMap3999swap_checked : acceptsGraphIso
    (source (graph core3999) (root 6) 6 1) DegreeTwoThreeSpectrum3961.graph sourceMap3999swap=true := by decide +kernel
theorem fusedMap3999swap_checked : acceptsGraphIso
    (fused (graph core3999) (root 6) 6 1) DegreeTwoThreeSpectrum3857.graph fusedMap3999swap=true := by decide +kernel
theorem certified3999swap : Certified (graph core3999) (root 6) 6 1 :=
  of_native_maps core3999 DegreeTwoThreeSpectrum3961.graph DegreeTwoThreeSpectrum3857.graph
    sourceMap3999swap fusedMap3999swap sourceMap3999swap_checked fusedMap3999swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3999
#print axioms sourceMap3999swap_checked
#print axioms fusedMap3999swap_checked
#print axioms certified3999swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
