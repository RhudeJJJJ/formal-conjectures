/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3038 : Family 10 := level10.get ⟨1655,by decide⟩
def sourceMap3038 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3038 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3038_checked : acceptsGraphIso
    (source (graph core3038) (root 10) 0 4) DegreeTwoThreeSpectrum7216.graph sourceMap3038=true := by decide +kernel
theorem fusedMap3038_checked : acceptsGraphIso
    (fused (graph core3038) (root 10) 0 4) DegreeTwoThreeSpectrum6255.graph fusedMap3038=true := by decide +kernel
theorem certified3038 : Certified (graph core3038) (root 10) 0 4 :=
  of_native_maps core3038 DegreeTwoThreeSpectrum7216.graph DegreeTwoThreeSpectrum6255.graph
    sourceMap3038 fusedMap3038 sourceMap3038_checked fusedMap3038_checked
    DegreeTwoThreeFiniteComparisons.comparison3038
#print axioms sourceMap3038_checked
#print axioms fusedMap3038_checked
#print axioms certified3038
def sourceMap3038swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3038swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3038swap_checked : acceptsGraphIso
    (source (graph core3038) (root 10) 4 0) DegreeTwoThreeSpectrum7216.graph sourceMap3038swap=true := by decide +kernel
theorem fusedMap3038swap_checked : acceptsGraphIso
    (fused (graph core3038) (root 10) 4 0) DegreeTwoThreeSpectrum6255.graph fusedMap3038swap=true := by decide +kernel
theorem certified3038swap : Certified (graph core3038) (root 10) 4 0 :=
  of_native_maps core3038 DegreeTwoThreeSpectrum7216.graph DegreeTwoThreeSpectrum6255.graph
    sourceMap3038swap fusedMap3038swap sourceMap3038swap_checked fusedMap3038swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3038
#print axioms sourceMap3038swap_checked
#print axioms fusedMap3038swap_checked
#print axioms certified3038swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
