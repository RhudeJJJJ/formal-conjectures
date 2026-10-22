/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2891 : Family 10 := level10.get ⟨1299,by decide⟩
def sourceMap2891 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2891 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2891_checked : acceptsGraphIso
    (source (graph core2891) (root 10) 0 4) DegreeTwoThreeSpectrum6584.graph sourceMap2891=true := by decide +kernel
theorem fusedMap2891_checked : acceptsGraphIso
    (fused (graph core2891) (root 10) 0 4) DegreeTwoThreeSpectrum6585.graph fusedMap2891=true := by decide +kernel
theorem certified2891 : Certified (graph core2891) (root 10) 0 4 :=
  of_native_maps core2891 DegreeTwoThreeSpectrum6584.graph DegreeTwoThreeSpectrum6585.graph
    sourceMap2891 fusedMap2891 sourceMap2891_checked fusedMap2891_checked
    DegreeTwoThreeFiniteComparisons.comparison2891
#print axioms sourceMap2891_checked
#print axioms fusedMap2891_checked
#print axioms certified2891
def sourceMap2891swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2891swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2891swap_checked : acceptsGraphIso
    (source (graph core2891) (root 10) 4 0) DegreeTwoThreeSpectrum6584.graph sourceMap2891swap=true := by decide +kernel
theorem fusedMap2891swap_checked : acceptsGraphIso
    (fused (graph core2891) (root 10) 4 0) DegreeTwoThreeSpectrum6585.graph fusedMap2891swap=true := by decide +kernel
theorem certified2891swap : Certified (graph core2891) (root 10) 4 0 :=
  of_native_maps core2891 DegreeTwoThreeSpectrum6584.graph DegreeTwoThreeSpectrum6585.graph
    sourceMap2891swap fusedMap2891swap sourceMap2891swap_checked fusedMap2891swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2891
#print axioms sourceMap2891swap_checked
#print axioms fusedMap2891swap_checked
#print axioms certified2891swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
