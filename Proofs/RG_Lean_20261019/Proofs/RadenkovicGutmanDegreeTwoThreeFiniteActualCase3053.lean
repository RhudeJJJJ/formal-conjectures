/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3053 : Family 10 := level10.get ⟨1711,by decide⟩
def sourceMap3053 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3053 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3053_checked : acceptsGraphIso
    (source (graph core3053) (root 10) 0 4) DegreeTwoThreeSpectrum7332.graph sourceMap3053=true := by decide +kernel
theorem fusedMap3053_checked : acceptsGraphIso
    (fused (graph core3053) (root 10) 0 4) DegreeTwoThreeSpectrum6487.graph fusedMap3053=true := by decide +kernel
theorem certified3053 : Certified (graph core3053) (root 10) 0 4 :=
  of_native_maps core3053 DegreeTwoThreeSpectrum7332.graph DegreeTwoThreeSpectrum6487.graph
    sourceMap3053 fusedMap3053 sourceMap3053_checked fusedMap3053_checked
    DegreeTwoThreeFiniteComparisons.comparison3053
#print axioms sourceMap3053_checked
#print axioms fusedMap3053_checked
#print axioms certified3053
def sourceMap3053swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3053swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3053swap_checked : acceptsGraphIso
    (source (graph core3053) (root 10) 4 0) DegreeTwoThreeSpectrum7332.graph sourceMap3053swap=true := by decide +kernel
theorem fusedMap3053swap_checked : acceptsGraphIso
    (fused (graph core3053) (root 10) 4 0) DegreeTwoThreeSpectrum6487.graph fusedMap3053swap=true := by decide +kernel
theorem certified3053swap : Certified (graph core3053) (root 10) 4 0 :=
  of_native_maps core3053 DegreeTwoThreeSpectrum7332.graph DegreeTwoThreeSpectrum6487.graph
    sourceMap3053swap fusedMap3053swap sourceMap3053swap_checked fusedMap3053swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3053
#print axioms sourceMap3053swap_checked
#print axioms fusedMap3053swap_checked
#print axioms certified3053swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
