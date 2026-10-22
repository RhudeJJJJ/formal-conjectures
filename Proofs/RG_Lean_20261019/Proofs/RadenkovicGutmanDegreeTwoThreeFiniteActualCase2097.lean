/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2097 : Family 7 := level7.get ⟨55,by decide⟩
def sourceMap2097 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 5) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13] (sourceLabel 7 0 4 v)
def fusedMap2097 : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 0 4 v)
theorem sourceMap2097_checked : acceptsGraphIso
    (source (graph core2097) (root 7) 0 4) DegreeTwoThreeSpectrum1879.graph sourceMap2097=true := by decide +kernel
theorem fusedMap2097_checked : acceptsGraphIso
    (fused (graph core2097) (root 7) 0 4) DegreeTwoThreeSpectrum1882.graph fusedMap2097=true := by decide +kernel
theorem certified2097 : Certified (graph core2097) (root 7) 0 4 :=
  of_native_maps core2097 DegreeTwoThreeSpectrum1879.graph DegreeTwoThreeSpectrum1882.graph
    sourceMap2097 fusedMap2097 sourceMap2097_checked fusedMap2097_checked
    DegreeTwoThreeFiniteComparisons.comparison2097
#print axioms sourceMap2097_checked
#print axioms fusedMap2097_checked
#print axioms certified2097
def sourceMap2097swap : (Vertices 7 ⊕ Fin 5 ⊕ Fin 1) → Fin 14 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,8] (sourceLabel 7 4 0 v)
def fusedMap2097swap : (Vertices 7 ⊕ Fin 6) → Fin 14 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13] (fusedLabel 7 4 0 v)
theorem sourceMap2097swap_checked : acceptsGraphIso
    (source (graph core2097) (root 7) 4 0) DegreeTwoThreeSpectrum1879.graph sourceMap2097swap=true := by decide +kernel
theorem fusedMap2097swap_checked : acceptsGraphIso
    (fused (graph core2097) (root 7) 4 0) DegreeTwoThreeSpectrum1882.graph fusedMap2097swap=true := by decide +kernel
theorem certified2097swap : Certified (graph core2097) (root 7) 4 0 :=
  of_native_maps core2097 DegreeTwoThreeSpectrum1879.graph DegreeTwoThreeSpectrum1882.graph
    sourceMap2097swap fusedMap2097swap sourceMap2097swap_checked fusedMap2097swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2097
#print axioms sourceMap2097swap_checked
#print axioms fusedMap2097swap_checked
#print axioms certified2097swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
