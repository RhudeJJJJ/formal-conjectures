/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5160 : Family 8 := level8.get ⟨139,by decide⟩
def sourceMap5160 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,7,8,9,12,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5160 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5160_checked : acceptsGraphIso
    (source (graph core5160) (root 8) 2 4) DegreeTwoThreeSpectrum6566.graph sourceMap5160=true := by decide +kernel
theorem fusedMap5160_checked : acceptsGraphIso
    (fused (graph core5160) (root 8) 2 4) DegreeTwoThreeSpectrum5463.graph fusedMap5160=true := by decide +kernel
theorem certified5160 : Certified (graph core5160) (root 8) 2 4 :=
  of_native_maps core5160 DegreeTwoThreeSpectrum6566.graph DegreeTwoThreeSpectrum5463.graph
    sourceMap5160 fusedMap5160 sourceMap5160_checked fusedMap5160_checked
    DegreeTwoThreeFiniteComparisons.comparison5160
#print axioms sourceMap5160_checked
#print axioms fusedMap5160_checked
#print axioms certified5160
def sourceMap5160swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,10,11,12,13,14,15,16,7,8,9] (sourceLabel 8 4 2 v)
def fusedMap5160swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5160swap_checked : acceptsGraphIso
    (source (graph core5160) (root 8) 4 2) DegreeTwoThreeSpectrum6566.graph sourceMap5160swap=true := by decide +kernel
theorem fusedMap5160swap_checked : acceptsGraphIso
    (fused (graph core5160) (root 8) 4 2) DegreeTwoThreeSpectrum5463.graph fusedMap5160swap=true := by decide +kernel
theorem certified5160swap : Certified (graph core5160) (root 8) 4 2 :=
  of_native_maps core5160 DegreeTwoThreeSpectrum6566.graph DegreeTwoThreeSpectrum5463.graph
    sourceMap5160swap fusedMap5160swap sourceMap5160swap_checked fusedMap5160swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5160
#print axioms sourceMap5160swap_checked
#print axioms fusedMap5160swap_checked
#print axioms certified5160swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
