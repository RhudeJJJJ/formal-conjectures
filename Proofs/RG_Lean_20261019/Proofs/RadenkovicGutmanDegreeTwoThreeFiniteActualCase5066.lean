/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5066 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap5066 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,14,11,12,13,6,7,8,9,10] (sourceLabel 6 2 4 v)
def fusedMap5066 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 2 4 v)
theorem sourceMap5066_checked : acceptsGraphIso
    (source (graph core5066) (root 6) 2 4) DegreeTwoThreeSpectrum2994.graph sourceMap5066=true := by decide +kernel
theorem fusedMap5066_checked : acceptsGraphIso
    (fused (graph core5066) (root 6) 2 4) DegreeTwoThreeSpectrum2313.graph fusedMap5066=true := by decide +kernel
theorem certified5066 : Certified (graph core5066) (root 6) 2 4 :=
  of_native_maps core5066 DegreeTwoThreeSpectrum2994.graph DegreeTwoThreeSpectrum2313.graph
    sourceMap5066 fusedMap5066 sourceMap5066_checked fusedMap5066_checked
    DegreeTwoThreeFiniteComparisons.comparison5066
#print axioms sourceMap5066_checked
#print axioms fusedMap5066_checked
#print axioms certified5066
def sourceMap5066swap : (Vertices 6 ⊕ Fin 5 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,14,6,7,8,9,10,11,12,13] (sourceLabel 6 4 2 v)
def fusedMap5066swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12,13,14] (fusedLabel 6 4 2 v)
theorem sourceMap5066swap_checked : acceptsGraphIso
    (source (graph core5066) (root 6) 4 2) DegreeTwoThreeSpectrum2994.graph sourceMap5066swap=true := by decide +kernel
theorem fusedMap5066swap_checked : acceptsGraphIso
    (fused (graph core5066) (root 6) 4 2) DegreeTwoThreeSpectrum2313.graph fusedMap5066swap=true := by decide +kernel
theorem certified5066swap : Certified (graph core5066) (root 6) 4 2 :=
  of_native_maps core5066 DegreeTwoThreeSpectrum2994.graph DegreeTwoThreeSpectrum2313.graph
    sourceMap5066swap fusedMap5066swap sourceMap5066swap_checked fusedMap5066swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5066
#print axioms sourceMap5066swap_checked
#print axioms fusedMap5066swap_checked
#print axioms certified5066swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
