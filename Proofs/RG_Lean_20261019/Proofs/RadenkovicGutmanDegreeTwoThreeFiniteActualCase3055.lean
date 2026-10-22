/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3055 : Family 10 := level10.get ⟨1714,by decide⟩
def sourceMap3055 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3055 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3055_checked : acceptsGraphIso
    (source (graph core3055) (root 10) 0 4) DegreeTwoThreeSpectrum7335.graph sourceMap3055=true := by decide +kernel
theorem fusedMap3055_checked : acceptsGraphIso
    (fused (graph core3055) (root 10) 0 4) DegreeTwoThreeSpectrum6493.graph fusedMap3055=true := by decide +kernel
theorem certified3055 : Certified (graph core3055) (root 10) 0 4 :=
  of_native_maps core3055 DegreeTwoThreeSpectrum7335.graph DegreeTwoThreeSpectrum6493.graph
    sourceMap3055 fusedMap3055 sourceMap3055_checked fusedMap3055_checked
    DegreeTwoThreeFiniteComparisons.comparison3055
#print axioms sourceMap3055_checked
#print axioms fusedMap3055_checked
#print axioms certified3055
def sourceMap3055swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3055swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3055swap_checked : acceptsGraphIso
    (source (graph core3055) (root 10) 4 0) DegreeTwoThreeSpectrum7335.graph sourceMap3055swap=true := by decide +kernel
theorem fusedMap3055swap_checked : acceptsGraphIso
    (fused (graph core3055) (root 10) 4 0) DegreeTwoThreeSpectrum6493.graph fusedMap3055swap=true := by decide +kernel
theorem certified3055swap : Certified (graph core3055) (root 10) 4 0 :=
  of_native_maps core3055 DegreeTwoThreeSpectrum7335.graph DegreeTwoThreeSpectrum6493.graph
    sourceMap3055swap fusedMap3055swap sourceMap3055swap_checked fusedMap3055swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3055
#print axioms sourceMap3055swap_checked
#print axioms fusedMap3055swap_checked
#print axioms certified3055swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
