/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2247 : Family 9 := level9.get ⟨133,by decide⟩
def sourceMap2247 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,10,11,12,13,14,15,6,7,8,9,1,2,3,4,5] (sourceLabel 9 0 4 v)
def fusedMap2247 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12] (fusedLabel 9 0 4 v)
theorem sourceMap2247_checked : acceptsGraphIso
    (source (graph core2247) (root 9) 0 4) DegreeTwoThreeSpectrum4153.graph sourceMap2247=true := by decide +kernel
theorem fusedMap2247_checked : acceptsGraphIso
    (fused (graph core2247) (root 9) 0 4) DegreeTwoThreeSpectrum4168.graph fusedMap2247=true := by decide +kernel
theorem certified2247 : Certified (graph core2247) (root 9) 0 4 :=
  of_native_maps core2247 DegreeTwoThreeSpectrum4153.graph DegreeTwoThreeSpectrum4168.graph
    sourceMap2247 fusedMap2247 sourceMap2247_checked fusedMap2247_checked
    DegreeTwoThreeFiniteComparisons.comparison2247
#print axioms sourceMap2247_checked
#print axioms fusedMap2247_checked
#print axioms certified2247
def sourceMap2247swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,10,11,12,13,14,15,6,7,8,1,2,3,4,5,9] (sourceLabel 9 4 0 v)
def fusedMap2247swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,13,14,15,7,8,9,10,11,12] (fusedLabel 9 4 0 v)
theorem sourceMap2247swap_checked : acceptsGraphIso
    (source (graph core2247) (root 9) 4 0) DegreeTwoThreeSpectrum4153.graph sourceMap2247swap=true := by decide +kernel
theorem fusedMap2247swap_checked : acceptsGraphIso
    (fused (graph core2247) (root 9) 4 0) DegreeTwoThreeSpectrum4168.graph fusedMap2247swap=true := by decide +kernel
theorem certified2247swap : Certified (graph core2247) (root 9) 4 0 :=
  of_native_maps core2247 DegreeTwoThreeSpectrum4153.graph DegreeTwoThreeSpectrum4168.graph
    sourceMap2247swap fusedMap2247swap sourceMap2247swap_checked fusedMap2247swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2247
#print axioms sourceMap2247swap_checked
#print axioms fusedMap2247swap_checked
#print axioms certified2247swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
