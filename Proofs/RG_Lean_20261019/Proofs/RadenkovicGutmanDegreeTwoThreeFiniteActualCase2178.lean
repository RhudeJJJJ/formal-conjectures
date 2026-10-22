/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2178 : Family 8 := level8.get ⟨180,by decide⟩
def sourceMap2178 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 5) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 8 0 4 v)
def fusedMap2178 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 0 4 v)
theorem sourceMap2178_checked : acceptsGraphIso
    (source (graph core2178) (root 8) 0 4) DegreeTwoThreeSpectrum2946.graph sourceMap2178=true := by decide +kernel
theorem fusedMap2178_checked : acceptsGraphIso
    (fused (graph core2178) (root 8) 0 4) DegreeTwoThreeSpectrum2948.graph fusedMap2178=true := by decide +kernel
theorem certified2178 : Certified (graph core2178) (root 8) 0 4 :=
  of_native_maps core2178 DegreeTwoThreeSpectrum2946.graph DegreeTwoThreeSpectrum2948.graph
    sourceMap2178 fusedMap2178 sourceMap2178_checked fusedMap2178_checked
    DegreeTwoThreeFiniteComparisons.comparison2178
#print axioms sourceMap2178_checked
#print axioms fusedMap2178_checked
#print axioms certified2178
def sourceMap2178swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,9] (sourceLabel 8 4 0 v)
def fusedMap2178swap : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 4 0 v)
theorem sourceMap2178swap_checked : acceptsGraphIso
    (source (graph core2178) (root 8) 4 0) DegreeTwoThreeSpectrum2946.graph sourceMap2178swap=true := by decide +kernel
theorem fusedMap2178swap_checked : acceptsGraphIso
    (fused (graph core2178) (root 8) 4 0) DegreeTwoThreeSpectrum2948.graph fusedMap2178swap=true := by decide +kernel
theorem certified2178swap : Certified (graph core2178) (root 8) 4 0 :=
  of_native_maps core2178 DegreeTwoThreeSpectrum2946.graph DegreeTwoThreeSpectrum2948.graph
    sourceMap2178swap fusedMap2178swap sourceMap2178swap_checked fusedMap2178swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2178
#print axioms sourceMap2178swap_checked
#print axioms fusedMap2178swap_checked
#print axioms certified2178swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
