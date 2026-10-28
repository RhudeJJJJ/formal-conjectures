/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons107
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5356 : Family 4 := level4.get ⟨6,by decide⟩
def sourceMap5356 : (Vertices 4 ⊕ Fin 4 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,6,7,8,9,2,3,4,5,0,10,11,12,13,14] (sourceLabel 4 3 5 v)
def fusedMap5356 : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 3 5 v)
theorem sourceMap5356_checked : acceptsGraphIso
    (source (graph core5356) (root 4) 3 5) DegreeTwoThreeSpectrum2973.graph sourceMap5356=true := by decide +kernel
theorem fusedMap5356_checked : acceptsGraphIso
    (fused (graph core5356) (root 4) 3 5) DegreeTwoThreeSpectrum2354.graph fusedMap5356=true := by decide +kernel
theorem certified5356 : Certified (graph core5356) (root 4) 3 5 :=
  of_native_maps core5356 DegreeTwoThreeSpectrum2973.graph DegreeTwoThreeSpectrum2354.graph
    sourceMap5356 fusedMap5356 sourceMap5356_checked fusedMap5356_checked
    DegreeTwoThreeFiniteComparisons.comparison5356
#print axioms sourceMap5356_checked
#print axioms fusedMap5356_checked
#print axioms certified5356
def sourceMap5356swap : (Vertices 4 ⊕ Fin 6 ⊕ Fin 4) → Fin 15 :=
  fun v => ![1,6,7,8,9,0,10,11,12,13,14,2,3,4,5] (sourceLabel 4 5 3 v)
def fusedMap5356swap : (Vertices 4 ⊕ Fin 10) → Fin 15 :=
  fun v => ![4,5,6,7,8,3,2,1,0,9,10,11,12,13,14] (fusedLabel 4 5 3 v)
theorem sourceMap5356swap_checked : acceptsGraphIso
    (source (graph core5356) (root 4) 5 3) DegreeTwoThreeSpectrum2973.graph sourceMap5356swap=true := by decide +kernel
theorem fusedMap5356swap_checked : acceptsGraphIso
    (fused (graph core5356) (root 4) 5 3) DegreeTwoThreeSpectrum2354.graph fusedMap5356swap=true := by decide +kernel
theorem certified5356swap : Certified (graph core5356) (root 4) 5 3 :=
  of_native_maps core5356 DegreeTwoThreeSpectrum2973.graph DegreeTwoThreeSpectrum2354.graph
    sourceMap5356swap fusedMap5356swap sourceMap5356swap_checked fusedMap5356swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5356
#print axioms sourceMap5356swap_checked
#print axioms fusedMap5356swap_checked
#print axioms certified5356swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
