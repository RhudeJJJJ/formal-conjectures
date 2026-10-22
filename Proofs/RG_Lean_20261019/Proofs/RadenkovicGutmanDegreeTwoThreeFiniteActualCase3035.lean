/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3035 : Family 10 := level10.get ⟨1650,by decide⟩
def sourceMap3035 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3035 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3035_checked : acceptsGraphIso
    (source (graph core3035) (root 10) 0 4) DegreeTwoThreeSpectrum7210.graph sourceMap3035=true := by decide +kernel
theorem fusedMap3035_checked : acceptsGraphIso
    (fused (graph core3035) (root 10) 0 4) DegreeTwoThreeSpectrum6243.graph fusedMap3035=true := by decide +kernel
theorem certified3035 : Certified (graph core3035) (root 10) 0 4 :=
  of_native_maps core3035 DegreeTwoThreeSpectrum7210.graph DegreeTwoThreeSpectrum6243.graph
    sourceMap3035 fusedMap3035 sourceMap3035_checked fusedMap3035_checked
    DegreeTwoThreeFiniteComparisons.comparison3035
#print axioms sourceMap3035_checked
#print axioms fusedMap3035_checked
#print axioms certified3035
def sourceMap3035swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3035swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3035swap_checked : acceptsGraphIso
    (source (graph core3035) (root 10) 4 0) DegreeTwoThreeSpectrum7210.graph sourceMap3035swap=true := by decide +kernel
theorem fusedMap3035swap_checked : acceptsGraphIso
    (fused (graph core3035) (root 10) 4 0) DegreeTwoThreeSpectrum6243.graph fusedMap3035swap=true := by decide +kernel
theorem certified3035swap : Certified (graph core3035) (root 10) 4 0 :=
  of_native_maps core3035 DegreeTwoThreeSpectrum7210.graph DegreeTwoThreeSpectrum6243.graph
    sourceMap3035swap fusedMap3035swap sourceMap3035swap_checked fusedMap3035swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3035
#print axioms sourceMap3035swap_checked
#print axioms fusedMap3035swap_checked
#print axioms certified3035swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
