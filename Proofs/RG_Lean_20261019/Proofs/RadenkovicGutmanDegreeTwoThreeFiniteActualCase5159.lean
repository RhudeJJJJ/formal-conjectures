/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5159 : Family 8 := level8.get ⟨138,by decide⟩
def sourceMap5159 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5159 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5159_checked : acceptsGraphIso
    (source (graph core5159) (root 8) 2 4) DegreeTwoThreeSpectrum6552.graph sourceMap5159=true := by decide +kernel
theorem fusedMap5159_checked : acceptsGraphIso
    (fused (graph core5159) (root 8) 2 4) DegreeTwoThreeSpectrum5453.graph fusedMap5159=true := by decide +kernel
theorem certified5159 : Certified (graph core5159) (root 8) 2 4 :=
  of_native_maps core5159 DegreeTwoThreeSpectrum6552.graph DegreeTwoThreeSpectrum5453.graph
    sourceMap5159 fusedMap5159 sourceMap5159_checked fusedMap5159_checked
    DegreeTwoThreeFiniteComparisons.comparison5159
#print axioms sourceMap5159_checked
#print axioms fusedMap5159_checked
#print axioms certified5159
def sourceMap5159swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5159swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5159swap_checked : acceptsGraphIso
    (source (graph core5159) (root 8) 4 2) DegreeTwoThreeSpectrum6552.graph sourceMap5159swap=true := by decide +kernel
theorem fusedMap5159swap_checked : acceptsGraphIso
    (fused (graph core5159) (root 8) 4 2) DegreeTwoThreeSpectrum5453.graph fusedMap5159swap=true := by decide +kernel
theorem certified5159swap : Certified (graph core5159) (root 8) 4 2 :=
  of_native_maps core5159 DegreeTwoThreeSpectrum6552.graph DegreeTwoThreeSpectrum5453.graph
    sourceMap5159swap fusedMap5159swap sourceMap5159swap_checked fusedMap5159swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5159
#print axioms sourceMap5159swap_checked
#print axioms fusedMap5159swap_checked
#print axioms certified5159swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
