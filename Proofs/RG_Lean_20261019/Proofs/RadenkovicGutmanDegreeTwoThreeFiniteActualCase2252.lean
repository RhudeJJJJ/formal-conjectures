/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2252 : Family 9 := level9.get ⟨153,by decide⟩
def sourceMap2252 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2252 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2252_checked : acceptsGraphIso
    (source (graph core2252) (root 9) 0 4) DegreeTwoThreeSpectrum4256.graph sourceMap2252=true := by decide +kernel
theorem fusedMap2252_checked : acceptsGraphIso
    (fused (graph core2252) (root 9) 0 4) DegreeTwoThreeSpectrum3910.graph fusedMap2252=true := by decide +kernel
theorem certified2252 : Certified (graph core2252) (root 9) 0 4 :=
  of_native_maps core2252 DegreeTwoThreeSpectrum4256.graph DegreeTwoThreeSpectrum3910.graph
    sourceMap2252 fusedMap2252 sourceMap2252_checked fusedMap2252_checked
    DegreeTwoThreeFiniteComparisons.comparison2252
#print axioms sourceMap2252_checked
#print axioms fusedMap2252_checked
#print axioms certified2252
def sourceMap2252swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2252swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2252swap_checked : acceptsGraphIso
    (source (graph core2252) (root 9) 4 0) DegreeTwoThreeSpectrum4256.graph sourceMap2252swap=true := by decide +kernel
theorem fusedMap2252swap_checked : acceptsGraphIso
    (fused (graph core2252) (root 9) 4 0) DegreeTwoThreeSpectrum3910.graph fusedMap2252swap=true := by decide +kernel
theorem certified2252swap : Certified (graph core2252) (root 9) 4 0 :=
  of_native_maps core2252 DegreeTwoThreeSpectrum4256.graph DegreeTwoThreeSpectrum3910.graph
    sourceMap2252swap fusedMap2252swap sourceMap2252swap_checked fusedMap2252swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2252
#print axioms sourceMap2252swap_checked
#print axioms fusedMap2252swap_checked
#print axioms certified2252swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
