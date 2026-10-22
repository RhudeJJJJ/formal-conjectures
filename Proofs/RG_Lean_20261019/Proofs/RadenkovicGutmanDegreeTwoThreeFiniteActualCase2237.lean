/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2237 : Family 9 := level9.get ⟨106,by decide⟩
def sourceMap2237 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2237 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2237_checked : acceptsGraphIso
    (source (graph core2237) (root 9) 0 4) DegreeTwoThreeSpectrum4102.graph sourceMap2237=true := by decide +kernel
theorem fusedMap2237_checked : acceptsGraphIso
    (fused (graph core2237) (root 9) 0 4) DegreeTwoThreeSpectrum4103.graph fusedMap2237=true := by decide +kernel
theorem certified2237 : Certified (graph core2237) (root 9) 0 4 :=
  of_native_maps core2237 DegreeTwoThreeSpectrum4102.graph DegreeTwoThreeSpectrum4103.graph
    sourceMap2237 fusedMap2237 sourceMap2237_checked fusedMap2237_checked
    DegreeTwoThreeFiniteComparisons.comparison2237
#print axioms sourceMap2237_checked
#print axioms fusedMap2237_checked
#print axioms certified2237
def sourceMap2237swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2237swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2237swap_checked : acceptsGraphIso
    (source (graph core2237) (root 9) 4 0) DegreeTwoThreeSpectrum4102.graph sourceMap2237swap=true := by decide +kernel
theorem fusedMap2237swap_checked : acceptsGraphIso
    (fused (graph core2237) (root 9) 4 0) DegreeTwoThreeSpectrum4103.graph fusedMap2237swap=true := by decide +kernel
theorem certified2237swap : Certified (graph core2237) (root 9) 4 0 :=
  of_native_maps core2237 DegreeTwoThreeSpectrum4102.graph DegreeTwoThreeSpectrum4103.graph
    sourceMap2237swap fusedMap2237swap sourceMap2237swap_checked fusedMap2237swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2237
#print axioms sourceMap2237swap_checked
#print axioms fusedMap2237swap_checked
#print axioms certified2237swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
