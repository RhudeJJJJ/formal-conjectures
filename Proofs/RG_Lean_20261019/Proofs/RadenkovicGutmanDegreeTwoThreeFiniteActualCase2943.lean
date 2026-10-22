/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2943 : Family 10 := level10.get ⟨1422,by decide⟩
def sourceMap2943 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2943 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2943_checked : acceptsGraphIso
    (source (graph core2943) (root 10) 0 4) DegreeTwoThreeSpectrum6874.graph sourceMap2943=true := by decide +kernel
theorem fusedMap2943_checked : acceptsGraphIso
    (fused (graph core2943) (root 10) 0 4) DegreeTwoThreeSpectrum6875.graph fusedMap2943=true := by decide +kernel
theorem certified2943 : Certified (graph core2943) (root 10) 0 4 :=
  of_native_maps core2943 DegreeTwoThreeSpectrum6874.graph DegreeTwoThreeSpectrum6875.graph
    sourceMap2943 fusedMap2943 sourceMap2943_checked fusedMap2943_checked
    DegreeTwoThreeFiniteComparisons.comparison2943
#print axioms sourceMap2943_checked
#print axioms fusedMap2943_checked
#print axioms certified2943
def sourceMap2943swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2943swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2943swap_checked : acceptsGraphIso
    (source (graph core2943) (root 10) 4 0) DegreeTwoThreeSpectrum6874.graph sourceMap2943swap=true := by decide +kernel
theorem fusedMap2943swap_checked : acceptsGraphIso
    (fused (graph core2943) (root 10) 4 0) DegreeTwoThreeSpectrum6875.graph fusedMap2943swap=true := by decide +kernel
theorem certified2943swap : Certified (graph core2943) (root 10) 4 0 :=
  of_native_maps core2943 DegreeTwoThreeSpectrum6874.graph DegreeTwoThreeSpectrum6875.graph
    sourceMap2943swap fusedMap2943swap sourceMap2943swap_checked fusedMap2943swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2943
#print axioms sourceMap2943swap_checked
#print axioms fusedMap2943swap_checked
#print axioms certified2943swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
