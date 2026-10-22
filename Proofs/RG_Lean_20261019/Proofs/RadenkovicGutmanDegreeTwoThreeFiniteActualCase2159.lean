/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2159 : Family 8 := level8.get ⟨138,by decide⟩
def sourceMap2159 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2159 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2159_checked : acceptsGraphIso
    (source (graph core2159) (root 8) 0 4) DegreeTwoThreeSpectrum2668.graph sourceMap2159=true := by decide +kernel
theorem fusedMap2159_checked : acceptsGraphIso
    (fused (graph core2159) (root 8) 0 4) DegreeTwoThreeSpectrum2670.graph fusedMap2159=true := by decide +kernel
theorem certified2159 : Certified (graph core2159) (root 8) 0 4 :=
  of_native_maps core2159 DegreeTwoThreeSpectrum2668.graph DegreeTwoThreeSpectrum2670.graph
    sourceMap2159 fusedMap2159 sourceMap2159_checked fusedMap2159_checked
    DegreeTwoThreeFiniteComparisons.comparison2159
#print axioms sourceMap2159_checked
#print axioms fusedMap2159_checked
#print axioms certified2159
def sourceMap2159swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2159swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2159swap_checked : acceptsGraphIso
    (source (graph core2159) (root 8) 4 0) DegreeTwoThreeSpectrum2668.graph sourceMap2159swap=true := by decide +kernel
theorem fusedMap2159swap_checked : acceptsGraphIso
    (fused (graph core2159) (root 8) 4 0) DegreeTwoThreeSpectrum2670.graph fusedMap2159swap=true := by decide +kernel
theorem certified2159swap : Certified (graph core2159) (root 8) 4 0 :=
  of_native_maps core2159 DegreeTwoThreeSpectrum2668.graph DegreeTwoThreeSpectrum2670.graph
    sourceMap2159swap fusedMap2159swap sourceMap2159swap_checked fusedMap2159swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2159
#print axioms sourceMap2159swap_checked
#print axioms fusedMap2159swap_checked
#print axioms certified2159swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
