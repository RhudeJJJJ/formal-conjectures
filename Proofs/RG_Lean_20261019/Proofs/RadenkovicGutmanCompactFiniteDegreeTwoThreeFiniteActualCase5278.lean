/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5278 : Family 7 := level7.get ⟨104,by decide⟩
def sourceMap5278 : (Vertices 7 ⊕ Fin 3 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,2,3,4,0,12,13,14,15,16] (sourceLabel 7 2 5 v)
def fusedMap5278 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 2 5 v)
theorem sourceMap5278_checked : acceptsGraphIso
    (source (graph core5278) (root 7) 2 5) DegreeTwoThreeSpectrum6872.graph sourceMap5278=true := by decide +kernel
theorem fusedMap5278_checked : acceptsGraphIso
    (fused (graph core5278) (root 7) 2 5) DegreeTwoThreeSpectrum5159.graph fusedMap5278=true := by decide +kernel
theorem certified5278 : Certified (graph core5278) (root 7) 2 5 :=
  of_native_maps core5278 DegreeTwoThreeSpectrum6872.graph DegreeTwoThreeSpectrum5159.graph
    sourceMap5278 fusedMap5278 sourceMap5278_checked fusedMap5278_checked
    DegreeTwoThreeFiniteComparisons.comparison5278
#print axioms sourceMap5278_checked
#print axioms fusedMap5278_checked
#print axioms certified5278
def sourceMap5278swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,5,6,7,8,9,10,11,0,12,13,14,15,16,2,3,4] (sourceLabel 7 5 2 v)
def fusedMap5278swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,2,1,0,11,12,13,14,15,16] (fusedLabel 7 5 2 v)
theorem sourceMap5278swap_checked : acceptsGraphIso
    (source (graph core5278) (root 7) 5 2) DegreeTwoThreeSpectrum6872.graph sourceMap5278swap=true := by decide +kernel
theorem fusedMap5278swap_checked : acceptsGraphIso
    (fused (graph core5278) (root 7) 5 2) DegreeTwoThreeSpectrum5159.graph fusedMap5278swap=true := by decide +kernel
theorem certified5278swap : Certified (graph core5278) (root 7) 5 2 :=
  of_native_maps core5278 DegreeTwoThreeSpectrum6872.graph DegreeTwoThreeSpectrum5159.graph
    sourceMap5278swap fusedMap5278swap sourceMap5278swap_checked fusedMap5278swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5278
#print axioms sourceMap5278swap_checked
#print axioms fusedMap5278swap_checked
#print axioms certified5278swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
