/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3051 : Family 10 := level10.get ⟨1706,by decide⟩
def sourceMap3051 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3051 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3051_checked : acceptsGraphIso
    (source (graph core3051) (root 10) 0 4) DegreeTwoThreeSpectrum7327.graph sourceMap3051=true := by decide +kernel
theorem fusedMap3051_checked : acceptsGraphIso
    (fused (graph core3051) (root 10) 0 4) DegreeTwoThreeSpectrum6476.graph fusedMap3051=true := by decide +kernel
theorem certified3051 : Certified (graph core3051) (root 10) 0 4 :=
  of_native_maps core3051 DegreeTwoThreeSpectrum7327.graph DegreeTwoThreeSpectrum6476.graph
    sourceMap3051 fusedMap3051 sourceMap3051_checked fusedMap3051_checked
    DegreeTwoThreeFiniteComparisons.comparison3051
#print axioms sourceMap3051_checked
#print axioms fusedMap3051_checked
#print axioms certified3051
def sourceMap3051swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3051swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3051swap_checked : acceptsGraphIso
    (source (graph core3051) (root 10) 4 0) DegreeTwoThreeSpectrum7327.graph sourceMap3051swap=true := by decide +kernel
theorem fusedMap3051swap_checked : acceptsGraphIso
    (fused (graph core3051) (root 10) 4 0) DegreeTwoThreeSpectrum6476.graph fusedMap3051swap=true := by decide +kernel
theorem certified3051swap : Certified (graph core3051) (root 10) 4 0 :=
  of_native_maps core3051 DegreeTwoThreeSpectrum7327.graph DegreeTwoThreeSpectrum6476.graph
    sourceMap3051swap fusedMap3051swap sourceMap3051swap_checked fusedMap3051swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3051
#print axioms sourceMap3051swap_checked
#print axioms fusedMap3051swap_checked
#print axioms certified3051swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
