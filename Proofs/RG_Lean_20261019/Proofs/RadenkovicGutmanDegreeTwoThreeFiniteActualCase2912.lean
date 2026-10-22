/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2912 : Family 10 := level10.get ⟨1349,by decide⟩
def sourceMap2912 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2912 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2912_checked : acceptsGraphIso
    (source (graph core2912) (root 10) 0 4) DegreeTwoThreeSpectrum6679.graph sourceMap2912=true := by decide +kernel
theorem fusedMap2912_checked : acceptsGraphIso
    (fused (graph core2912) (root 10) 0 4) DegreeTwoThreeSpectrum6680.graph fusedMap2912=true := by decide +kernel
theorem certified2912 : Certified (graph core2912) (root 10) 0 4 :=
  of_native_maps core2912 DegreeTwoThreeSpectrum6679.graph DegreeTwoThreeSpectrum6680.graph
    sourceMap2912 fusedMap2912 sourceMap2912_checked fusedMap2912_checked
    DegreeTwoThreeFiniteComparisons.comparison2912
#print axioms sourceMap2912_checked
#print axioms fusedMap2912_checked
#print axioms certified2912
def sourceMap2912swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2912swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2912swap_checked : acceptsGraphIso
    (source (graph core2912) (root 10) 4 0) DegreeTwoThreeSpectrum6679.graph sourceMap2912swap=true := by decide +kernel
theorem fusedMap2912swap_checked : acceptsGraphIso
    (fused (graph core2912) (root 10) 4 0) DegreeTwoThreeSpectrum6680.graph fusedMap2912swap=true := by decide +kernel
theorem certified2912swap : Certified (graph core2912) (root 10) 4 0 :=
  of_native_maps core2912 DegreeTwoThreeSpectrum6679.graph DegreeTwoThreeSpectrum6680.graph
    sourceMap2912swap fusedMap2912swap sourceMap2912swap_checked fusedMap2912swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2912
#print axioms sourceMap2912swap_checked
#print axioms fusedMap2912swap_checked
#print axioms certified2912swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
