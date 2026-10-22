/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons60
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3016 : Family 10 := level10.get ⟨1602,by decide⟩
def sourceMap3016 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3016 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3016_checked : acceptsGraphIso
    (source (graph core3016) (root 10) 0 4) DegreeTwoThreeSpectrum7145.graph sourceMap3016=true := by decide +kernel
theorem fusedMap3016_checked : acceptsGraphIso
    (fused (graph core3016) (root 10) 0 4) DegreeTwoThreeSpectrum6118.graph fusedMap3016=true := by decide +kernel
theorem certified3016 : Certified (graph core3016) (root 10) 0 4 :=
  of_native_maps core3016 DegreeTwoThreeSpectrum7145.graph DegreeTwoThreeSpectrum6118.graph
    sourceMap3016 fusedMap3016 sourceMap3016_checked fusedMap3016_checked
    DegreeTwoThreeFiniteComparisons.comparison3016
#print axioms sourceMap3016_checked
#print axioms fusedMap3016_checked
#print axioms certified3016
def sourceMap3016swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3016swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3016swap_checked : acceptsGraphIso
    (source (graph core3016) (root 10) 4 0) DegreeTwoThreeSpectrum7145.graph sourceMap3016swap=true := by decide +kernel
theorem fusedMap3016swap_checked : acceptsGraphIso
    (fused (graph core3016) (root 10) 4 0) DegreeTwoThreeSpectrum6118.graph fusedMap3016swap=true := by decide +kernel
theorem certified3016swap : Certified (graph core3016) (root 10) 4 0 :=
  of_native_maps core3016 DegreeTwoThreeSpectrum7145.graph DegreeTwoThreeSpectrum6118.graph
    sourceMap3016swap fusedMap3016swap sourceMap3016swap_checked fusedMap3016swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3016
#print axioms sourceMap3016swap_checked
#print axioms fusedMap3016swap_checked
#print axioms certified3016swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
