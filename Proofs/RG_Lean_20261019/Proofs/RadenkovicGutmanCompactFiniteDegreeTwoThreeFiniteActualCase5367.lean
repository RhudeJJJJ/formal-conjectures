/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5367 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap5367 : (Vertices 4 ⊕ Fin 4 ⊕ Fin 7) → Fin 16 :=
  fun v => ![1,6,7,8,9,2,3,4,5,0,10,11,12,13,14,15] (sourceLabel 4 3 6 v)
def fusedMap5367 : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 3 6 v)
theorem sourceMap5367_checked : acceptsGraphIso
    (source (graph core5367) (root 4) 3 6) DegreeTwoThreeSpectrum4125.graph sourceMap5367=true := by decide +kernel
theorem fusedMap5367_checked : acceptsGraphIso
    (fused (graph core5367) (root 4) 3 6) DegreeTwoThreeSpectrum3862.graph fusedMap5367=true := by decide +kernel
theorem certified5367 : Certified (graph core5367) (root 4) 3 6 :=
  of_native_maps core5367 DegreeTwoThreeSpectrum4125.graph DegreeTwoThreeSpectrum3862.graph
    sourceMap5367 fusedMap5367 sourceMap5367_checked fusedMap5367_checked
    DegreeTwoThreeFiniteComparisons.comparison5367
#print axioms sourceMap5367_checked
#print axioms fusedMap5367_checked
#print axioms certified5367
def sourceMap5367swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 4) → Fin 16 :=
  fun v => ![1,6,7,8,9,0,10,11,12,13,14,15,2,3,4,5] (sourceLabel 4 6 3 v)
def fusedMap5367swap : (Vertices 4 ⊕ Fin 11) → Fin 16 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14,15] (fusedLabel 4 6 3 v)
theorem sourceMap5367swap_checked : acceptsGraphIso
    (source (graph core5367) (root 4) 6 3) DegreeTwoThreeSpectrum4125.graph sourceMap5367swap=true := by decide +kernel
theorem fusedMap5367swap_checked : acceptsGraphIso
    (fused (graph core5367) (root 4) 6 3) DegreeTwoThreeSpectrum3862.graph fusedMap5367swap=true := by decide +kernel
theorem certified5367swap : Certified (graph core5367) (root 4) 6 3 :=
  of_native_maps core5367 DegreeTwoThreeSpectrum4125.graph DegreeTwoThreeSpectrum3862.graph
    sourceMap5367swap fusedMap5367swap sourceMap5367swap_checked fusedMap5367swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5367
#print axioms sourceMap5367swap_checked
#print axioms fusedMap5367swap_checked
#print axioms certified5367swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
