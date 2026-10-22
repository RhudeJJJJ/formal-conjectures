/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2177 : Family 8 := level8.get ⟨179,by decide⟩
def sourceMap2177 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2177 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2177_checked : acceptsGraphIso
    (source (graph core2177) (root 8) 0 4) DegreeTwoThreeSpectrum2941.graph sourceMap2177=true := by decide +kernel
theorem fusedMap2177_checked : acceptsGraphIso
    (fused (graph core2177) (root 8) 0 4) DegreeTwoThreeSpectrum2943.graph fusedMap2177=true := by decide +kernel
theorem certified2177 : Certified (graph core2177) (root 8) 0 4 :=
  of_native_maps core2177 DegreeTwoThreeSpectrum2941.graph DegreeTwoThreeSpectrum2943.graph
    sourceMap2177 fusedMap2177 sourceMap2177_checked fusedMap2177_checked
    DegreeTwoThreeFiniteComparisons.comparison2177
#print axioms sourceMap2177_checked
#print axioms fusedMap2177_checked
#print axioms certified2177
def sourceMap2177swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2177swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2177swap_checked : acceptsGraphIso
    (source (graph core2177) (root 8) 4 0) DegreeTwoThreeSpectrum2941.graph sourceMap2177swap=true := by decide +kernel
theorem fusedMap2177swap_checked : acceptsGraphIso
    (fused (graph core2177) (root 8) 4 0) DegreeTwoThreeSpectrum2943.graph fusedMap2177swap=true := by decide +kernel
theorem certified2177swap : Certified (graph core2177) (root 8) 4 0 :=
  of_native_maps core2177 DegreeTwoThreeSpectrum2941.graph DegreeTwoThreeSpectrum2943.graph
    sourceMap2177swap fusedMap2177swap sourceMap2177swap_checked fusedMap2177swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2177
#print axioms sourceMap2177swap_checked
#print axioms fusedMap2177swap_checked
#print axioms certified2177swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
