/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons102
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5138 : Family 8 := level8.get ⟨80,by decide⟩
def sourceMap5138 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,13,14,15,8,9,10,11,12] (sourceLabel 8 2 4 v)
def fusedMap5138 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5138_checked : acceptsGraphIso
    (source (graph core5138) (root 8) 2 4) DegreeTwoThreeSpectrum6985.graph sourceMap5138=true := by decide +kernel
theorem fusedMap5138_checked : acceptsGraphIso
    (fused (graph core5138) (root 8) 2 4) DegreeTwoThreeSpectrum5063.graph fusedMap5138=true := by decide +kernel
theorem certified5138 : Certified (graph core5138) (root 8) 2 4 :=
  of_native_maps core5138 DegreeTwoThreeSpectrum6985.graph DegreeTwoThreeSpectrum5063.graph
    sourceMap5138 fusedMap5138 sourceMap5138_checked fusedMap5138_checked
    DegreeTwoThreeFiniteComparisons.comparison5138
#print axioms sourceMap5138_checked
#print axioms fusedMap5138_checked
#print axioms certified5138
def sourceMap5138swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,16,8,9,10,11,12,13,14,15] (sourceLabel 8 4 2 v)
def fusedMap5138swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5138swap_checked : acceptsGraphIso
    (source (graph core5138) (root 8) 4 2) DegreeTwoThreeSpectrum6985.graph sourceMap5138swap=true := by decide +kernel
theorem fusedMap5138swap_checked : acceptsGraphIso
    (fused (graph core5138) (root 8) 4 2) DegreeTwoThreeSpectrum5063.graph fusedMap5138swap=true := by decide +kernel
theorem certified5138swap : Certified (graph core5138) (root 8) 4 2 :=
  of_native_maps core5138 DegreeTwoThreeSpectrum6985.graph DegreeTwoThreeSpectrum5063.graph
    sourceMap5138swap fusedMap5138swap sourceMap5138swap_checked fusedMap5138swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5138
#print axioms sourceMap5138swap_checked
#print axioms fusedMap5138swap_checked
#print axioms certified5138swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
