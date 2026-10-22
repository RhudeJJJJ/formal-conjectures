/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons58
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2907 : Family 10 := level10.get ⟨1336,by decide⟩
def sourceMap2907 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap2907 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2907_checked : acceptsGraphIso
    (source (graph core2907) (root 10) 0 4) DegreeTwoThreeSpectrum6653.graph sourceMap2907=true := by decide +kernel
theorem fusedMap2907_checked : acceptsGraphIso
    (fused (graph core2907) (root 10) 0 4) DegreeTwoThreeSpectrum6654.graph fusedMap2907=true := by decide +kernel
theorem certified2907 : Certified (graph core2907) (root 10) 0 4 :=
  of_native_maps core2907 DegreeTwoThreeSpectrum6653.graph DegreeTwoThreeSpectrum6654.graph
    sourceMap2907 fusedMap2907 sourceMap2907_checked fusedMap2907_checked
    DegreeTwoThreeFiniteComparisons.comparison2907
#print axioms sourceMap2907_checked
#print axioms fusedMap2907_checked
#print axioms certified2907
def sourceMap2907swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,16,11] (sourceLabel 10 4 0 v)
def fusedMap2907swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2907swap_checked : acceptsGraphIso
    (source (graph core2907) (root 10) 4 0) DegreeTwoThreeSpectrum6653.graph sourceMap2907swap=true := by decide +kernel
theorem fusedMap2907swap_checked : acceptsGraphIso
    (fused (graph core2907) (root 10) 4 0) DegreeTwoThreeSpectrum6654.graph fusedMap2907swap=true := by decide +kernel
theorem certified2907swap : Certified (graph core2907) (root 10) 4 0 :=
  of_native_maps core2907 DegreeTwoThreeSpectrum6653.graph DegreeTwoThreeSpectrum6654.graph
    sourceMap2907swap fusedMap2907swap sourceMap2907swap_checked fusedMap2907swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2907
#print axioms sourceMap2907swap_checked
#print axioms fusedMap2907swap_checked
#print axioms certified2907swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
