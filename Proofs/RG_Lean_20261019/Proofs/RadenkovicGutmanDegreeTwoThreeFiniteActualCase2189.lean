/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2189 : Family 8 := level8.get ⟨208,by decide⟩
def sourceMap2189 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2189 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2189_checked : acceptsGraphIso
    (source (graph core2189) (root 8) 0 4) DegreeTwoThreeSpectrum3165.graph sourceMap2189=true := by decide +kernel
theorem fusedMap2189_checked : acceptsGraphIso
    (fused (graph core2189) (root 8) 0 4) DegreeTwoThreeSpectrum2503.graph fusedMap2189=true := by decide +kernel
theorem certified2189 : Certified (graph core2189) (root 8) 0 4 :=
  of_native_maps core2189 DegreeTwoThreeSpectrum3165.graph DegreeTwoThreeSpectrum2503.graph
    sourceMap2189 fusedMap2189 sourceMap2189_checked fusedMap2189_checked
    DegreeTwoThreeFiniteComparisons.comparison2189
#print axioms sourceMap2189_checked
#print axioms fusedMap2189_checked
#print axioms certified2189
def sourceMap2189swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,10] (sourceLabel 8 4 0 v)
def fusedMap2189swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2189swap_checked : acceptsGraphIso
    (source (graph core2189) (root 8) 4 0) DegreeTwoThreeSpectrum3165.graph sourceMap2189swap=true := by decide +kernel
theorem fusedMap2189swap_checked : acceptsGraphIso
    (fused (graph core2189) (root 8) 4 0) DegreeTwoThreeSpectrum2503.graph fusedMap2189swap=true := by decide +kernel
theorem certified2189swap : Certified (graph core2189) (root 8) 4 0 :=
  of_native_maps core2189 DegreeTwoThreeSpectrum3165.graph DegreeTwoThreeSpectrum2503.graph
    sourceMap2189swap fusedMap2189swap sourceMap2189swap_checked fusedMap2189swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2189
#print axioms sourceMap2189swap_checked
#print axioms fusedMap2189swap_checked
#print axioms certified2189swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
