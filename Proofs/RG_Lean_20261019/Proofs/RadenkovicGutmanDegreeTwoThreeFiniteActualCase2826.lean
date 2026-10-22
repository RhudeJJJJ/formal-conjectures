/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons56
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2826 : Family 10 := level10.get ⟨1142,by decide⟩
def sourceMap2826 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2826 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2826_checked : acceptsGraphIso
    (source (graph core2826) (root 10) 0 4) DegreeTwoThreeSpectrum6270.graph sourceMap2826=true := by decide +kernel
theorem fusedMap2826_checked : acceptsGraphIso
    (fused (graph core2826) (root 10) 0 4) DegreeTwoThreeSpectrum6271.graph fusedMap2826=true := by decide +kernel
theorem certified2826 : Certified (graph core2826) (root 10) 0 4 :=
  of_native_maps core2826 DegreeTwoThreeSpectrum6270.graph DegreeTwoThreeSpectrum6271.graph
    sourceMap2826 fusedMap2826 sourceMap2826_checked fusedMap2826_checked
    DegreeTwoThreeFiniteComparisons.comparison2826
#print axioms sourceMap2826_checked
#print axioms fusedMap2826_checked
#print axioms certified2826
def sourceMap2826swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2826swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2826swap_checked : acceptsGraphIso
    (source (graph core2826) (root 10) 4 0) DegreeTwoThreeSpectrum6270.graph sourceMap2826swap=true := by decide +kernel
theorem fusedMap2826swap_checked : acceptsGraphIso
    (fused (graph core2826) (root 10) 4 0) DegreeTwoThreeSpectrum6271.graph fusedMap2826swap=true := by decide +kernel
theorem certified2826swap : Certified (graph core2826) (root 10) 4 0 :=
  of_native_maps core2826 DegreeTwoThreeSpectrum6270.graph DegreeTwoThreeSpectrum6271.graph
    sourceMap2826swap fusedMap2826swap sourceMap2826swap_checked fusedMap2826swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2826
#print axioms sourceMap2826swap_checked
#print axioms fusedMap2826swap_checked
#print axioms certified2826swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
