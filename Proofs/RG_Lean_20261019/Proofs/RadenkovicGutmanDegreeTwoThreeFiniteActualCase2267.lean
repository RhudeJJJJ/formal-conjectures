/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2267 : Family 9 := level9.get ⟨196,by decide⟩
def sourceMap2267 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,15,7,8,9,10,11] (sourceLabel 9 0 4 v)
def fusedMap2267 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2267_checked : acceptsGraphIso
    (source (graph core2267) (root 9) 0 4) DegreeTwoThreeSpectrum4389.graph sourceMap2267=true := by decide +kernel
theorem fusedMap2267_checked : acceptsGraphIso
    (fused (graph core2267) (root 9) 0 4) DegreeTwoThreeSpectrum3972.graph fusedMap2267=true := by decide +kernel
theorem certified2267 : Certified (graph core2267) (root 9) 0 4 :=
  of_native_maps core2267 DegreeTwoThreeSpectrum4389.graph DegreeTwoThreeSpectrum3972.graph
    sourceMap2267 fusedMap2267 sourceMap2267_checked fusedMap2267_checked
    DegreeTwoThreeFiniteComparisons.comparison2267
#print axioms sourceMap2267_checked
#print axioms fusedMap2267_checked
#print axioms certified2267
def sourceMap2267swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,12,13,14,7,8,9,10,11,15] (sourceLabel 9 4 0 v)
def fusedMap2267swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2267swap_checked : acceptsGraphIso
    (source (graph core2267) (root 9) 4 0) DegreeTwoThreeSpectrum4389.graph sourceMap2267swap=true := by decide +kernel
theorem fusedMap2267swap_checked : acceptsGraphIso
    (fused (graph core2267) (root 9) 4 0) DegreeTwoThreeSpectrum3972.graph fusedMap2267swap=true := by decide +kernel
theorem certified2267swap : Certified (graph core2267) (root 9) 4 0 :=
  of_native_maps core2267 DegreeTwoThreeSpectrum4389.graph DegreeTwoThreeSpectrum3972.graph
    sourceMap2267swap fusedMap2267swap sourceMap2267swap_checked fusedMap2267swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2267
#print axioms sourceMap2267swap_checked
#print axioms fusedMap2267swap_checked
#print axioms certified2267swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
