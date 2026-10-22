/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2292 : Family 9 := level9.get ⟨273,by decide⟩
def sourceMap2292 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 5) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12] (sourceLabel 9 0 4 v)
def fusedMap2292 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 0 4 v)
theorem sourceMap2292_checked : acceptsGraphIso
    (source (graph core2292) (root 9) 0 4) DegreeTwoThreeSpectrum4606.graph sourceMap2292=true := by decide +kernel
theorem fusedMap2292_checked : acceptsGraphIso
    (fused (graph core2292) (root 9) 0 4) DegreeTwoThreeSpectrum4087.graph fusedMap2292=true := by decide +kernel
theorem certified2292 : Certified (graph core2292) (root 9) 0 4 :=
  of_native_maps core2292 DegreeTwoThreeSpectrum4606.graph DegreeTwoThreeSpectrum4087.graph
    sourceMap2292 fusedMap2292 sourceMap2292_checked fusedMap2292_checked
    DegreeTwoThreeFiniteComparisons.comparison2292
#print axioms sourceMap2292_checked
#print axioms fusedMap2292_checked
#print axioms certified2292
def sourceMap2292swap : (Vertices 9 ⊕ Fin 5 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,8,9,10,11,12,15] (sourceLabel 9 4 0 v)
def fusedMap2292swap : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 4 0 v)
theorem sourceMap2292swap_checked : acceptsGraphIso
    (source (graph core2292) (root 9) 4 0) DegreeTwoThreeSpectrum4606.graph sourceMap2292swap=true := by decide +kernel
theorem fusedMap2292swap_checked : acceptsGraphIso
    (fused (graph core2292) (root 9) 4 0) DegreeTwoThreeSpectrum4087.graph fusedMap2292swap=true := by decide +kernel
theorem certified2292swap : Certified (graph core2292) (root 9) 4 0 :=
  of_native_maps core2292 DegreeTwoThreeSpectrum4606.graph DegreeTwoThreeSpectrum4087.graph
    sourceMap2292swap fusedMap2292swap sourceMap2292swap_checked fusedMap2292swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2292
#print axioms sourceMap2292swap_checked
#print axioms fusedMap2292swap_checked
#print axioms certified2292swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
