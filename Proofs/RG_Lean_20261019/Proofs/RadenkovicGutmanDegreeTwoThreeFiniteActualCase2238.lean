/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2238 : Family 9 := level9.get ⟨109,by decide⟩
def sourceMap2238 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13] (sourceLabel 9 0 4 v)
def fusedMap2238 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 0 4 v)
theorem sourceMap2238_checked : acceptsGraphIso
    (source (graph core2238) (root 9) 0 4) DegreeTwoThreeSpectrum4109.graph sourceMap2238=true := by decide +kernel
theorem fusedMap2238_checked : acceptsGraphIso
    (fused (graph core2238) (root 9) 0 4) DegreeTwoThreeSpectrum4110.graph fusedMap2238=true := by decide +kernel
theorem certified2238 : Certified (graph core2238) (root 9) 0 4 :=
  of_native_maps core2238 DegreeTwoThreeSpectrum4109.graph DegreeTwoThreeSpectrum4110.graph
    sourceMap2238 fusedMap2238 sourceMap2238_checked fusedMap2238_checked
    DegreeTwoThreeFiniteComparisons.comparison2238
#print axioms sourceMap2238_checked
#print axioms fusedMap2238_checked
#print axioms certified2238
def sourceMap2238swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,9,10,11,12,13,15] (sourceLabel 9 4 0 v)
def fusedMap2238swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (fusedLabel 9 4 0 v)
theorem sourceMap2238swap_checked : acceptsGraphIso
    (source (graph core2238) (root 9) 4 0) DegreeTwoThreeSpectrum4109.graph sourceMap2238swap=true := by decide +kernel
theorem fusedMap2238swap_checked : acceptsGraphIso
    (fused (graph core2238) (root 9) 4 0) DegreeTwoThreeSpectrum4110.graph fusedMap2238swap=true := by decide +kernel
theorem certified2238swap : Certified (graph core2238) (root 9) 4 0 :=
  of_native_maps core2238 DegreeTwoThreeSpectrum4109.graph DegreeTwoThreeSpectrum4110.graph
    sourceMap2238swap fusedMap2238swap sourceMap2238swap_checked fusedMap2238swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2238
#print axioms sourceMap2238swap_checked
#print axioms fusedMap2238swap_checked
#print axioms certified2238swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
