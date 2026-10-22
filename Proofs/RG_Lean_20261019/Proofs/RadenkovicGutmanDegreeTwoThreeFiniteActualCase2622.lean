/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2622 : Family 10 := level10.get ⟨601,by decide⟩
def sourceMap2622 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2622 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2622_checked : acceptsGraphIso
    (source (graph core2622) (root 10) 0 4) DegreeTwoThreeSpectrum6314.graph sourceMap2622=true := by decide +kernel
theorem fusedMap2622_checked : acceptsGraphIso
    (fused (graph core2622) (root 10) 0 4) DegreeTwoThreeSpectrum5277.graph fusedMap2622=true := by decide +kernel
theorem certified2622 : Certified (graph core2622) (root 10) 0 4 :=
  of_native_maps core2622 DegreeTwoThreeSpectrum6314.graph DegreeTwoThreeSpectrum5277.graph
    sourceMap2622 fusedMap2622 sourceMap2622_checked fusedMap2622_checked
    DegreeTwoThreeFiniteComparisons.comparison2622
#print axioms sourceMap2622_checked
#print axioms fusedMap2622_checked
#print axioms certified2622
def sourceMap2622swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2622swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2622swap_checked : acceptsGraphIso
    (source (graph core2622) (root 10) 4 0) DegreeTwoThreeSpectrum6314.graph sourceMap2622swap=true := by decide +kernel
theorem fusedMap2622swap_checked : acceptsGraphIso
    (fused (graph core2622) (root 10) 4 0) DegreeTwoThreeSpectrum5277.graph fusedMap2622swap=true := by decide +kernel
theorem certified2622swap : Certified (graph core2622) (root 10) 4 0 :=
  of_native_maps core2622 DegreeTwoThreeSpectrum6314.graph DegreeTwoThreeSpectrum5277.graph
    sourceMap2622swap fusedMap2622swap sourceMap2622swap_checked fusedMap2622swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2622
#print axioms sourceMap2622swap_checked
#print axioms fusedMap2622swap_checked
#print axioms certified2622swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
