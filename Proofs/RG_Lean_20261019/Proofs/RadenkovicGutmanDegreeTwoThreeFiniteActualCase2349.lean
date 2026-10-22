/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2349 : Family 9 := level9.get ⟨423,by decide⟩
def sourceMap2349 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (sourceLabel 9 0 4 v)
def fusedMap2349 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2349_checked : acceptsGraphIso
    (source (graph core2349) (root 9) 0 4) DegreeTwoThreeSpectrum4408.graph sourceMap2349=true := by decide +kernel
theorem fusedMap2349_checked : acceptsGraphIso
    (fused (graph core2349) (root 9) 0 4) DegreeTwoThreeSpectrum4409.graph fusedMap2349=true := by decide +kernel
theorem certified2349 : Certified (graph core2349) (root 9) 0 4 :=
  of_native_maps core2349 DegreeTwoThreeSpectrum4408.graph DegreeTwoThreeSpectrum4409.graph
    sourceMap2349 fusedMap2349 sourceMap2349_checked fusedMap2349_checked
    DegreeTwoThreeFiniteComparisons.comparison2349
#print axioms sourceMap2349_checked
#print axioms fusedMap2349_checked
#print axioms certified2349
def sourceMap2349swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,10] (sourceLabel 9 4 0 v)
def fusedMap2349swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2349swap_checked : acceptsGraphIso
    (source (graph core2349) (root 9) 4 0) DegreeTwoThreeSpectrum4408.graph sourceMap2349swap=true := by decide +kernel
theorem fusedMap2349swap_checked : acceptsGraphIso
    (fused (graph core2349) (root 9) 4 0) DegreeTwoThreeSpectrum4409.graph fusedMap2349swap=true := by decide +kernel
theorem certified2349swap : Certified (graph core2349) (root 9) 4 0 :=
  of_native_maps core2349 DegreeTwoThreeSpectrum4408.graph DegreeTwoThreeSpectrum4409.graph
    sourceMap2349swap fusedMap2349swap sourceMap2349swap_checked fusedMap2349swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2349
#print axioms sourceMap2349swap_checked
#print axioms fusedMap2349swap_checked
#print axioms certified2349swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
