/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5154 : Family 8 := level8.get ⟨125,by decide⟩
def sourceMap5154 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,8,9,10,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5154 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5154_checked : acceptsGraphIso
    (source (graph core5154) (root 8) 2 4) DegreeTwoThreeSpectrum6390.graph sourceMap5154=true := by decide +kernel
theorem fusedMap5154_checked : acceptsGraphIso
    (fused (graph core5154) (root 8) 2 4) DegreeTwoThreeSpectrum5333.graph fusedMap5154=true := by decide +kernel
theorem certified5154 : Certified (graph core5154) (root 8) 2 4 :=
  of_native_maps core5154 DegreeTwoThreeSpectrum6390.graph DegreeTwoThreeSpectrum5333.graph
    sourceMap5154 fusedMap5154 sourceMap5154_checked fusedMap5154_checked
    DegreeTwoThreeFiniteComparisons.comparison5154
#print axioms sourceMap5154_checked
#print axioms fusedMap5154_checked
#print axioms certified5154
def sourceMap5154swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,11,12,13,14,15,16,8,9,10] (sourceLabel 8 4 2 v)
def fusedMap5154swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5154swap_checked : acceptsGraphIso
    (source (graph core5154) (root 8) 4 2) DegreeTwoThreeSpectrum6390.graph sourceMap5154swap=true := by decide +kernel
theorem fusedMap5154swap_checked : acceptsGraphIso
    (fused (graph core5154) (root 8) 4 2) DegreeTwoThreeSpectrum5333.graph fusedMap5154swap=true := by decide +kernel
theorem certified5154swap : Certified (graph core5154) (root 8) 4 2 :=
  of_native_maps core5154 DegreeTwoThreeSpectrum6390.graph DegreeTwoThreeSpectrum5333.graph
    sourceMap5154swap fusedMap5154swap sourceMap5154swap_checked fusedMap5154swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5154
#print axioms sourceMap5154swap_checked
#print axioms fusedMap5154swap_checked
#print axioms certified5154swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
