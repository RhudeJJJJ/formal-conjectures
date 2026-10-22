/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons57
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2861 : Family 10 := level10.get ⟨1222,by decide⟩
def sourceMap2861 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2861 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2861_checked : acceptsGraphIso
    (source (graph core2861) (root 10) 0 4) DegreeTwoThreeSpectrum6420.graph sourceMap2861=true := by decide +kernel
theorem fusedMap2861_checked : acceptsGraphIso
    (fused (graph core2861) (root 10) 0 4) DegreeTwoThreeSpectrum6421.graph fusedMap2861=true := by decide +kernel
theorem certified2861 : Certified (graph core2861) (root 10) 0 4 :=
  of_native_maps core2861 DegreeTwoThreeSpectrum6420.graph DegreeTwoThreeSpectrum6421.graph
    sourceMap2861 fusedMap2861 sourceMap2861_checked fusedMap2861_checked
    DegreeTwoThreeFiniteComparisons.comparison2861
#print axioms sourceMap2861_checked
#print axioms fusedMap2861_checked
#print axioms certified2861
def sourceMap2861swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2861swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2861swap_checked : acceptsGraphIso
    (source (graph core2861) (root 10) 4 0) DegreeTwoThreeSpectrum6420.graph sourceMap2861swap=true := by decide +kernel
theorem fusedMap2861swap_checked : acceptsGraphIso
    (fused (graph core2861) (root 10) 4 0) DegreeTwoThreeSpectrum6421.graph fusedMap2861swap=true := by decide +kernel
theorem certified2861swap : Certified (graph core2861) (root 10) 4 0 :=
  of_native_maps core2861 DegreeTwoThreeSpectrum6420.graph DegreeTwoThreeSpectrum6421.graph
    sourceMap2861swap fusedMap2861swap sourceMap2861swap_checked fusedMap2861swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2861
#print axioms sourceMap2861swap_checked
#print axioms fusedMap2861swap_checked
#print axioms certified2861swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
