/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3052 : Family 10 := level10.get ⟨1710,by decide⟩
def sourceMap3052 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3052 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3052_checked : acceptsGraphIso
    (source (graph core3052) (root 10) 0 4) DegreeTwoThreeSpectrum7331.graph sourceMap3052=true := by decide +kernel
theorem fusedMap3052_checked : acceptsGraphIso
    (fused (graph core3052) (root 10) 0 4) DegreeTwoThreeSpectrum6486.graph fusedMap3052=true := by decide +kernel
theorem certified3052 : Certified (graph core3052) (root 10) 0 4 :=
  of_native_maps core3052 DegreeTwoThreeSpectrum7331.graph DegreeTwoThreeSpectrum6486.graph
    sourceMap3052 fusedMap3052 sourceMap3052_checked fusedMap3052_checked
    DegreeTwoThreeFiniteComparisons.comparison3052
#print axioms sourceMap3052_checked
#print axioms fusedMap3052_checked
#print axioms certified3052
def sourceMap3052swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3052swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3052swap_checked : acceptsGraphIso
    (source (graph core3052) (root 10) 4 0) DegreeTwoThreeSpectrum7331.graph sourceMap3052swap=true := by decide +kernel
theorem fusedMap3052swap_checked : acceptsGraphIso
    (fused (graph core3052) (root 10) 4 0) DegreeTwoThreeSpectrum6486.graph fusedMap3052swap=true := by decide +kernel
theorem certified3052swap : Certified (graph core3052) (root 10) 4 0 :=
  of_native_maps core3052 DegreeTwoThreeSpectrum7331.graph DegreeTwoThreeSpectrum6486.graph
    sourceMap3052swap fusedMap3052swap sourceMap3052swap_checked fusedMap3052swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3052
#print axioms sourceMap3052swap_checked
#print axioms fusedMap3052swap_checked
#print axioms certified3052swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
