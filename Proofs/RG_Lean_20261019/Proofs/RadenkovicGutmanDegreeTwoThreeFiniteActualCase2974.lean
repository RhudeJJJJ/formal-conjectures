/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons59
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2974 : Family 10 := level10.get ⟨1494,by decide⟩
def sourceMap2974 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2974 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2974_checked : acceptsGraphIso
    (source (graph core2974) (root 10) 0 4) DegreeTwoThreeSpectrum6995.graph sourceMap2974=true := by decide +kernel
theorem fusedMap2974_checked : acceptsGraphIso
    (fused (graph core2974) (root 10) 0 4) DegreeTwoThreeSpectrum6996.graph fusedMap2974=true := by decide +kernel
theorem certified2974 : Certified (graph core2974) (root 10) 0 4 :=
  of_native_maps core2974 DegreeTwoThreeSpectrum6995.graph DegreeTwoThreeSpectrum6996.graph
    sourceMap2974 fusedMap2974 sourceMap2974_checked fusedMap2974_checked
    DegreeTwoThreeFiniteComparisons.comparison2974
#print axioms sourceMap2974_checked
#print axioms fusedMap2974_checked
#print axioms certified2974
def sourceMap2974swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2974swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2974swap_checked : acceptsGraphIso
    (source (graph core2974) (root 10) 4 0) DegreeTwoThreeSpectrum6995.graph sourceMap2974swap=true := by decide +kernel
theorem fusedMap2974swap_checked : acceptsGraphIso
    (fused (graph core2974) (root 10) 4 0) DegreeTwoThreeSpectrum6996.graph fusedMap2974swap=true := by decide +kernel
theorem certified2974swap : Certified (graph core2974) (root 10) 4 0 :=
  of_native_maps core2974 DegreeTwoThreeSpectrum6995.graph DegreeTwoThreeSpectrum6996.graph
    sourceMap2974swap fusedMap2974swap sourceMap2974swap_checked fusedMap2974swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2974
#print axioms sourceMap2974swap_checked
#print axioms fusedMap2974swap_checked
#print axioms certified2974swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
