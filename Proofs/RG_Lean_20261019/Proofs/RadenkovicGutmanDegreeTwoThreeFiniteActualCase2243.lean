/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2243 : Family 9 := level9.get ⟨123,by decide⟩
def sourceMap2243 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2243 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 0 4 v)
theorem sourceMap2243_checked : acceptsGraphIso
    (source (graph core2243) (root 9) 0 4) DegreeTwoThreeSpectrum4146.graph sourceMap2243=true := by decide +kernel
theorem fusedMap2243_checked : acceptsGraphIso
    (fused (graph core2243) (root 9) 0 4) DegreeTwoThreeSpectrum4148.graph fusedMap2243=true := by decide +kernel
theorem certified2243 : Certified (graph core2243) (root 9) 0 4 :=
  of_native_maps core2243 DegreeTwoThreeSpectrum4146.graph DegreeTwoThreeSpectrum4148.graph
    sourceMap2243 fusedMap2243 sourceMap2243_checked fusedMap2243_checked
    DegreeTwoThreeFiniteComparisons.comparison2243
#print axioms sourceMap2243_checked
#print axioms fusedMap2243_checked
#print axioms certified2243
def sourceMap2243swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![7,0,1,2,3,4,5,6,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2243swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (fusedLabel 9 4 0 v)
theorem sourceMap2243swap_checked : acceptsGraphIso
    (source (graph core2243) (root 9) 4 0) DegreeTwoThreeSpectrum4146.graph sourceMap2243swap=true := by decide +kernel
theorem fusedMap2243swap_checked : acceptsGraphIso
    (fused (graph core2243) (root 9) 4 0) DegreeTwoThreeSpectrum4148.graph fusedMap2243swap=true := by decide +kernel
theorem certified2243swap : Certified (graph core2243) (root 9) 4 0 :=
  of_native_maps core2243 DegreeTwoThreeSpectrum4146.graph DegreeTwoThreeSpectrum4148.graph
    sourceMap2243swap fusedMap2243swap sourceMap2243swap_checked fusedMap2243swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2243
#print axioms sourceMap2243swap_checked
#print axioms fusedMap2243swap_checked
#print axioms certified2243swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
