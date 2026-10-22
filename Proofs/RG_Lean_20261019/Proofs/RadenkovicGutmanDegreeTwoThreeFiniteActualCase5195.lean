/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons103
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5195 : Family 8 := level8.get ⟨219,by decide⟩
def sourceMap5195 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,12,7,8,9,0,13,14,15,16] (sourceLabel 8 2 4 v)
def fusedMap5195 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 2 4 v)
theorem sourceMap5195_checked : acceptsGraphIso
    (source (graph core5195) (root 8) 2 4) DegreeTwoThreeSpectrum7235.graph sourceMap5195=true := by decide +kernel
theorem fusedMap5195_checked : acceptsGraphIso
    (fused (graph core5195) (root 8) 2 4) DegreeTwoThreeSpectrum5265.graph fusedMap5195=true := by decide +kernel
theorem certified5195 : Certified (graph core5195) (root 8) 2 4 :=
  of_native_maps core5195 DegreeTwoThreeSpectrum7235.graph DegreeTwoThreeSpectrum5265.graph
    sourceMap5195 fusedMap5195 sourceMap5195_checked fusedMap5195_checked
    DegreeTwoThreeFiniteComparisons.comparison5195
#print axioms sourceMap5195_checked
#print axioms fusedMap5195_checked
#print axioms certified5195
def sourceMap5195swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,10,11,12,0,13,14,15,16,7,8,9] (sourceLabel 8 4 2 v)
def fusedMap5195swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 4 2 v)
theorem sourceMap5195swap_checked : acceptsGraphIso
    (source (graph core5195) (root 8) 4 2) DegreeTwoThreeSpectrum7235.graph sourceMap5195swap=true := by decide +kernel
theorem fusedMap5195swap_checked : acceptsGraphIso
    (fused (graph core5195) (root 8) 4 2) DegreeTwoThreeSpectrum5265.graph fusedMap5195swap=true := by decide +kernel
theorem certified5195swap : Certified (graph core5195) (root 8) 4 2 :=
  of_native_maps core5195 DegreeTwoThreeSpectrum7235.graph DegreeTwoThreeSpectrum5265.graph
    sourceMap5195swap fusedMap5195swap sourceMap5195swap_checked fusedMap5195swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5195
#print axioms sourceMap5195swap_checked
#print axioms fusedMap5195swap_checked
#print axioms certified5195swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
