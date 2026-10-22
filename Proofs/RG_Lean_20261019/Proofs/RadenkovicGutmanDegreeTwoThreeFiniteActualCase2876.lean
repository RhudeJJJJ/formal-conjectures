/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2876 : Family 10 := level10.get ⟨1263,by decide⟩
def sourceMap2876 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2876 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2876_checked : acceptsGraphIso
    (source (graph core2876) (root 10) 0 4) DegreeTwoThreeSpectrum6514.graph sourceMap2876=true := by decide +kernel
theorem fusedMap2876_checked : acceptsGraphIso
    (fused (graph core2876) (root 10) 0 4) DegreeTwoThreeSpectrum6515.graph fusedMap2876=true := by decide +kernel
theorem certified2876 : Certified (graph core2876) (root 10) 0 4 :=
  of_native_maps core2876 DegreeTwoThreeSpectrum6514.graph DegreeTwoThreeSpectrum6515.graph
    sourceMap2876 fusedMap2876 sourceMap2876_checked fusedMap2876_checked
    DegreeTwoThreeFiniteComparisons.comparison2876
#print axioms sourceMap2876_checked
#print axioms fusedMap2876_checked
#print axioms certified2876
def sourceMap2876swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2876swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2876swap_checked : acceptsGraphIso
    (source (graph core2876) (root 10) 4 0) DegreeTwoThreeSpectrum6514.graph sourceMap2876swap=true := by decide +kernel
theorem fusedMap2876swap_checked : acceptsGraphIso
    (fused (graph core2876) (root 10) 4 0) DegreeTwoThreeSpectrum6515.graph fusedMap2876swap=true := by decide +kernel
theorem certified2876swap : Certified (graph core2876) (root 10) 4 0 :=
  of_native_maps core2876 DegreeTwoThreeSpectrum6514.graph DegreeTwoThreeSpectrum6515.graph
    sourceMap2876swap fusedMap2876swap sourceMap2876swap_checked fusedMap2876swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2876
#print axioms sourceMap2876swap_checked
#print axioms fusedMap2876swap_checked
#print axioms certified2876swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
