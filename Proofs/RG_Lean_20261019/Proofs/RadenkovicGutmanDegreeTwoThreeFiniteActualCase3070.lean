/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3070 : Family 10 := level10.get ⟨1785,by decide⟩
def sourceMap3070 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3070 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3070_checked : acceptsGraphIso
    (source (graph core3070) (root 10) 0 4) DegreeTwoThreeSpectrum7553.graph sourceMap3070=true := by decide +kernel
theorem fusedMap3070_checked : acceptsGraphIso
    (fused (graph core3070) (root 10) 0 4) DegreeTwoThreeSpectrum6865.graph fusedMap3070=true := by decide +kernel
theorem certified3070 : Certified (graph core3070) (root 10) 0 4 :=
  of_native_maps core3070 DegreeTwoThreeSpectrum7553.graph DegreeTwoThreeSpectrum6865.graph
    sourceMap3070 fusedMap3070 sourceMap3070_checked fusedMap3070_checked
    DegreeTwoThreeFiniteComparisons.comparison3070
#print axioms sourceMap3070_checked
#print axioms fusedMap3070_checked
#print axioms certified3070
def sourceMap3070swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3070swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3070swap_checked : acceptsGraphIso
    (source (graph core3070) (root 10) 4 0) DegreeTwoThreeSpectrum7553.graph sourceMap3070swap=true := by decide +kernel
theorem fusedMap3070swap_checked : acceptsGraphIso
    (fused (graph core3070) (root 10) 4 0) DegreeTwoThreeSpectrum6865.graph fusedMap3070swap=true := by decide +kernel
theorem certified3070swap : Certified (graph core3070) (root 10) 4 0 :=
  of_native_maps core3070 DegreeTwoThreeSpectrum7553.graph DegreeTwoThreeSpectrum6865.graph
    sourceMap3070swap fusedMap3070swap sourceMap3070swap_checked fusedMap3070swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3070
#print axioms sourceMap3070swap_checked
#print axioms fusedMap3070swap_checked
#print axioms certified3070swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
