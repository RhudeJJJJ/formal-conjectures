/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2324 : Family 9 := level9.get ⟨360,by decide⟩
def sourceMap2324 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2324 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2324_checked : acceptsGraphIso
    (source (graph core2324) (root 9) 0 4) DegreeTwoThreeSpectrum4273.graph sourceMap2324=true := by decide +kernel
theorem fusedMap2324_checked : acceptsGraphIso
    (fused (graph core2324) (root 9) 0 4) DegreeTwoThreeSpectrum4274.graph fusedMap2324=true := by decide +kernel
theorem certified2324 : Certified (graph core2324) (root 9) 0 4 :=
  of_native_maps core2324 DegreeTwoThreeSpectrum4273.graph DegreeTwoThreeSpectrum4274.graph
    sourceMap2324 fusedMap2324 sourceMap2324_checked fusedMap2324_checked
    DegreeTwoThreeFiniteComparisons.comparison2324
#print axioms sourceMap2324_checked
#print axioms fusedMap2324_checked
#print axioms certified2324
def sourceMap2324swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2324swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2324swap_checked : acceptsGraphIso
    (source (graph core2324) (root 9) 4 0) DegreeTwoThreeSpectrum4273.graph sourceMap2324swap=true := by decide +kernel
theorem fusedMap2324swap_checked : acceptsGraphIso
    (fused (graph core2324) (root 9) 4 0) DegreeTwoThreeSpectrum4274.graph fusedMap2324swap=true := by decide +kernel
theorem certified2324swap : Certified (graph core2324) (root 9) 4 0 :=
  of_native_maps core2324 DegreeTwoThreeSpectrum4273.graph DegreeTwoThreeSpectrum4274.graph
    sourceMap2324swap fusedMap2324swap sourceMap2324swap_checked fusedMap2324swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2324
#print axioms sourceMap2324swap_checked
#print axioms fusedMap2324swap_checked
#print axioms certified2324swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
