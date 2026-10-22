/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2042 : Family 10 := level10.get ⟨1744,by decide⟩
def sourceMap2042 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap2042 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap2042_checked : acceptsGraphIso
    (source (graph core2042) (root 10) 0 2) DegreeTwoThreeSpectrum3839.graph sourceMap2042=true := by decide +kernel
theorem fusedMap2042_checked : acceptsGraphIso
    (fused (graph core2042) (root 10) 0 2) DegreeTwoThreeSpectrum3471.graph fusedMap2042=true := by decide +kernel
theorem certified2042 : Certified (graph core2042) (root 10) 0 2 :=
  of_native_maps core2042 DegreeTwoThreeSpectrum3839.graph DegreeTwoThreeSpectrum3471.graph
    sourceMap2042 fusedMap2042 sourceMap2042_checked fusedMap2042_checked
    DegreeTwoThreeFiniteComparisons.comparison2042
#print axioms sourceMap2042_checked
#print axioms fusedMap2042_checked
#print axioms certified2042
def sourceMap2042swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap2042swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap2042swap_checked : acceptsGraphIso
    (source (graph core2042) (root 10) 2 0) DegreeTwoThreeSpectrum3839.graph sourceMap2042swap=true := by decide +kernel
theorem fusedMap2042swap_checked : acceptsGraphIso
    (fused (graph core2042) (root 10) 2 0) DegreeTwoThreeSpectrum3471.graph fusedMap2042swap=true := by decide +kernel
theorem certified2042swap : Certified (graph core2042) (root 10) 2 0 :=
  of_native_maps core2042 DegreeTwoThreeSpectrum3839.graph DegreeTwoThreeSpectrum3471.graph
    sourceMap2042swap fusedMap2042swap sourceMap2042swap_checked fusedMap2042swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2042
#print axioms sourceMap2042swap_checked
#print axioms fusedMap2042swap_checked
#print axioms certified2042swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
