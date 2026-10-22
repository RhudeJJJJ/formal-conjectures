/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2164 : Family 8 := level8.get ⟨152,by decide⟩
def sourceMap2164 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2164 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2164_checked : acceptsGraphIso
    (source (graph core2164) (root 8) 0 4) DegreeTwoThreeSpectrum2742.graph sourceMap2164=true := by decide +kernel
theorem fusedMap2164_checked : acceptsGraphIso
    (fused (graph core2164) (root 8) 0 4) DegreeTwoThreeSpectrum2744.graph fusedMap2164=true := by decide +kernel
theorem certified2164 : Certified (graph core2164) (root 8) 0 4 :=
  of_native_maps core2164 DegreeTwoThreeSpectrum2742.graph DegreeTwoThreeSpectrum2744.graph
    sourceMap2164 fusedMap2164 sourceMap2164_checked fusedMap2164_checked
    DegreeTwoThreeFiniteComparisons.comparison2164
#print axioms sourceMap2164_checked
#print axioms fusedMap2164_checked
#print axioms certified2164
def sourceMap2164swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2164swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2164swap_checked : acceptsGraphIso
    (source (graph core2164) (root 8) 4 0) DegreeTwoThreeSpectrum2742.graph sourceMap2164swap=true := by decide +kernel
theorem fusedMap2164swap_checked : acceptsGraphIso
    (fused (graph core2164) (root 8) 4 0) DegreeTwoThreeSpectrum2744.graph fusedMap2164swap=true := by decide +kernel
theorem certified2164swap : Certified (graph core2164) (root 8) 4 0 :=
  of_native_maps core2164 DegreeTwoThreeSpectrum2742.graph DegreeTwoThreeSpectrum2744.graph
    sourceMap2164swap fusedMap2164swap sourceMap2164swap_checked fusedMap2164swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2164
#print axioms sourceMap2164swap_checked
#print axioms fusedMap2164swap_checked
#print axioms certified2164swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
