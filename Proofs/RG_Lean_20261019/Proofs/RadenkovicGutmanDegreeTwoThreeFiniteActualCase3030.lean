/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3030 : Family 10 := level10.get ⟨1638,by decide⟩
def sourceMap3030 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3030 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3030_checked : acceptsGraphIso
    (source (graph core3030) (root 10) 0 4) DegreeTwoThreeSpectrum7194.graph sourceMap3030=true := by decide +kernel
theorem fusedMap3030_checked : acceptsGraphIso
    (fused (graph core3030) (root 10) 0 4) DegreeTwoThreeSpectrum6213.graph fusedMap3030=true := by decide +kernel
theorem certified3030 : Certified (graph core3030) (root 10) 0 4 :=
  of_native_maps core3030 DegreeTwoThreeSpectrum7194.graph DegreeTwoThreeSpectrum6213.graph
    sourceMap3030 fusedMap3030 sourceMap3030_checked fusedMap3030_checked
    DegreeTwoThreeFiniteComparisons.comparison3030
#print axioms sourceMap3030_checked
#print axioms fusedMap3030_checked
#print axioms certified3030
def sourceMap3030swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3030swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3030swap_checked : acceptsGraphIso
    (source (graph core3030) (root 10) 4 0) DegreeTwoThreeSpectrum7194.graph sourceMap3030swap=true := by decide +kernel
theorem fusedMap3030swap_checked : acceptsGraphIso
    (fused (graph core3030) (root 10) 4 0) DegreeTwoThreeSpectrum6213.graph fusedMap3030swap=true := by decide +kernel
theorem certified3030swap : Certified (graph core3030) (root 10) 4 0 :=
  of_native_maps core3030 DegreeTwoThreeSpectrum7194.graph DegreeTwoThreeSpectrum6213.graph
    sourceMap3030swap fusedMap3030swap sourceMap3030swap_checked fusedMap3030swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3030
#print axioms sourceMap3030swap_checked
#print axioms fusedMap3030swap_checked
#print axioms certified3030swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
