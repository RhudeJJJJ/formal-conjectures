/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3044 : Family 10 := level10.get ⟨1678,by decide⟩
def sourceMap3044 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3044 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3044_checked : acceptsGraphIso
    (source (graph core3044) (root 10) 0 4) DegreeTwoThreeSpectrum7260.graph sourceMap3044=true := by decide +kernel
theorem fusedMap3044_checked : acceptsGraphIso
    (fused (graph core3044) (root 10) 0 4) DegreeTwoThreeSpectrum6338.graph fusedMap3044=true := by decide +kernel
theorem certified3044 : Certified (graph core3044) (root 10) 0 4 :=
  of_native_maps core3044 DegreeTwoThreeSpectrum7260.graph DegreeTwoThreeSpectrum6338.graph
    sourceMap3044 fusedMap3044 sourceMap3044_checked fusedMap3044_checked
    DegreeTwoThreeFiniteComparisons.comparison3044
#print axioms sourceMap3044_checked
#print axioms fusedMap3044_checked
#print axioms certified3044
def sourceMap3044swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3044swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3044swap_checked : acceptsGraphIso
    (source (graph core3044) (root 10) 4 0) DegreeTwoThreeSpectrum7260.graph sourceMap3044swap=true := by decide +kernel
theorem fusedMap3044swap_checked : acceptsGraphIso
    (fused (graph core3044) (root 10) 4 0) DegreeTwoThreeSpectrum6338.graph fusedMap3044swap=true := by decide +kernel
theorem certified3044swap : Certified (graph core3044) (root 10) 4 0 :=
  of_native_maps core3044 DegreeTwoThreeSpectrum7260.graph DegreeTwoThreeSpectrum6338.graph
    sourceMap3044swap fusedMap3044swap sourceMap3044swap_checked fusedMap3044swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3044
#print axioms sourceMap3044swap_checked
#print axioms fusedMap3044swap_checked
#print axioms certified3044swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
