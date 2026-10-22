/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2173 : Family 8 := level8.get ⟨172,by decide⟩
def sourceMap2173 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2173 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2173_checked : acceptsGraphIso
    (source (graph core2173) (root 8) 0 4) DegreeTwoThreeSpectrum2873.graph sourceMap2173=true := by decide +kernel
theorem fusedMap2173_checked : acceptsGraphIso
    (fused (graph core2173) (root 8) 0 4) DegreeTwoThreeSpectrum2875.graph fusedMap2173=true := by decide +kernel
theorem certified2173 : Certified (graph core2173) (root 8) 0 4 :=
  of_native_maps core2173 DegreeTwoThreeSpectrum2873.graph DegreeTwoThreeSpectrum2875.graph
    sourceMap2173 fusedMap2173 sourceMap2173_checked fusedMap2173_checked
    DegreeTwoThreeFiniteComparisons.comparison2173
#print axioms sourceMap2173_checked
#print axioms fusedMap2173_checked
#print axioms certified2173
def sourceMap2173swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2173swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2173swap_checked : acceptsGraphIso
    (source (graph core2173) (root 8) 4 0) DegreeTwoThreeSpectrum2873.graph sourceMap2173swap=true := by decide +kernel
theorem fusedMap2173swap_checked : acceptsGraphIso
    (fused (graph core2173) (root 8) 4 0) DegreeTwoThreeSpectrum2875.graph fusedMap2173swap=true := by decide +kernel
theorem certified2173swap : Certified (graph core2173) (root 8) 4 0 :=
  of_native_maps core2173 DegreeTwoThreeSpectrum2873.graph DegreeTwoThreeSpectrum2875.graph
    sourceMap2173swap fusedMap2173swap sourceMap2173swap_checked fusedMap2173swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2173
#print axioms sourceMap2173swap_checked
#print axioms fusedMap2173swap_checked
#print axioms certified2173swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
