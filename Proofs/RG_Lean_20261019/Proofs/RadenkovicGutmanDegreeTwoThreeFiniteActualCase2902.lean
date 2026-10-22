/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2902 : Family 10 := level10.get ⟨1326,by decide⟩
def sourceMap2902 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2902 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2902_checked : acceptsGraphIso
    (source (graph core2902) (root 10) 0 4) DegreeTwoThreeSpectrum6635.graph sourceMap2902=true := by decide +kernel
theorem fusedMap2902_checked : acceptsGraphIso
    (fused (graph core2902) (root 10) 0 4) DegreeTwoThreeSpectrum6636.graph fusedMap2902=true := by decide +kernel
theorem certified2902 : Certified (graph core2902) (root 10) 0 4 :=
  of_native_maps core2902 DegreeTwoThreeSpectrum6635.graph DegreeTwoThreeSpectrum6636.graph
    sourceMap2902 fusedMap2902 sourceMap2902_checked fusedMap2902_checked
    DegreeTwoThreeFiniteComparisons.comparison2902
#print axioms sourceMap2902_checked
#print axioms fusedMap2902_checked
#print axioms certified2902
def sourceMap2902swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2902swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2902swap_checked : acceptsGraphIso
    (source (graph core2902) (root 10) 4 0) DegreeTwoThreeSpectrum6635.graph sourceMap2902swap=true := by decide +kernel
theorem fusedMap2902swap_checked : acceptsGraphIso
    (fused (graph core2902) (root 10) 4 0) DegreeTwoThreeSpectrum6636.graph fusedMap2902swap=true := by decide +kernel
theorem certified2902swap : Certified (graph core2902) (root 10) 4 0 :=
  of_native_maps core2902 DegreeTwoThreeSpectrum6635.graph DegreeTwoThreeSpectrum6636.graph
    sourceMap2902swap fusedMap2902swap sourceMap2902swap_checked fusedMap2902swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2902
#print axioms sourceMap2902swap_checked
#print axioms fusedMap2902swap_checked
#print axioms certified2902swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
