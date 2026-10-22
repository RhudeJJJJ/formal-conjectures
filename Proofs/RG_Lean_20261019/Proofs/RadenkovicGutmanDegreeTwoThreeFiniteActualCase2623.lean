/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2623 : Family 10 := level10.get ⟨606,by decide⟩
def sourceMap2623 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2623 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2623_checked : acceptsGraphIso
    (source (graph core2623) (root 10) 0 4) DegreeTwoThreeSpectrum6326.graph sourceMap2623=true := by decide +kernel
theorem fusedMap2623_checked : acceptsGraphIso
    (fused (graph core2623) (root 10) 0 4) DegreeTwoThreeSpectrum5285.graph fusedMap2623=true := by decide +kernel
theorem certified2623 : Certified (graph core2623) (root 10) 0 4 :=
  of_native_maps core2623 DegreeTwoThreeSpectrum6326.graph DegreeTwoThreeSpectrum5285.graph
    sourceMap2623 fusedMap2623 sourceMap2623_checked fusedMap2623_checked
    DegreeTwoThreeFiniteComparisons.comparison2623
#print axioms sourceMap2623_checked
#print axioms fusedMap2623_checked
#print axioms certified2623
def sourceMap2623swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2623swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2623swap_checked : acceptsGraphIso
    (source (graph core2623) (root 10) 4 0) DegreeTwoThreeSpectrum6326.graph sourceMap2623swap=true := by decide +kernel
theorem fusedMap2623swap_checked : acceptsGraphIso
    (fused (graph core2623) (root 10) 4 0) DegreeTwoThreeSpectrum5285.graph fusedMap2623swap=true := by decide +kernel
theorem certified2623swap : Certified (graph core2623) (root 10) 4 0 :=
  of_native_maps core2623 DegreeTwoThreeSpectrum6326.graph DegreeTwoThreeSpectrum5285.graph
    sourceMap2623swap fusedMap2623swap sourceMap2623swap_checked fusedMap2623swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2623
#print axioms sourceMap2623swap_checked
#print axioms fusedMap2623swap_checked
#print axioms certified2623swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
