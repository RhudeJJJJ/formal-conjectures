/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons50
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2537 : Family 10 := level10.get ⟨340,by decide⟩
def sourceMap2537 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,16,9,10,11,12,13] (sourceLabel 10 0 4 v)
def fusedMap2537 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 0 4 v)
theorem sourceMap2537_checked : acceptsGraphIso
    (source (graph core2537) (root 10) 0 4) DegreeTwoThreeSpectrum5592.graph sourceMap2537=true := by decide +kernel
theorem fusedMap2537_checked : acceptsGraphIso
    (fused (graph core2537) (root 10) 0 4) DegreeTwoThreeSpectrum5594.graph fusedMap2537=true := by decide +kernel
theorem certified2537 : Certified (graph core2537) (root 10) 0 4 :=
  of_native_maps core2537 DegreeTwoThreeSpectrum5592.graph DegreeTwoThreeSpectrum5594.graph
    sourceMap2537 fusedMap2537 sourceMap2537_checked fusedMap2537_checked
    DegreeTwoThreeFiniteComparisons.comparison2537
#print axioms sourceMap2537_checked
#print axioms fusedMap2537_checked
#print axioms certified2537
def sourceMap2537swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,14,15,9,10,11,12,13,16] (sourceLabel 10 4 0 v)
def fusedMap2537swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 4 0 v)
theorem sourceMap2537swap_checked : acceptsGraphIso
    (source (graph core2537) (root 10) 4 0) DegreeTwoThreeSpectrum5592.graph sourceMap2537swap=true := by decide +kernel
theorem fusedMap2537swap_checked : acceptsGraphIso
    (fused (graph core2537) (root 10) 4 0) DegreeTwoThreeSpectrum5594.graph fusedMap2537swap=true := by decide +kernel
theorem certified2537swap : Certified (graph core2537) (root 10) 4 0 :=
  of_native_maps core2537 DegreeTwoThreeSpectrum5592.graph DegreeTwoThreeSpectrum5594.graph
    sourceMap2537swap fusedMap2537swap sourceMap2537swap_checked fusedMap2537swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2537
#print axioms sourceMap2537swap_checked
#print axioms fusedMap2537swap_checked
#print axioms certified2537swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
