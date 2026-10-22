/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3388 : Family 9 := level9.get ⟨467,by decide⟩
def sourceMap3388 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3388 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3388_checked : acceptsGraphIso
    (source (graph core3388) (root 9) 0 5) DegreeTwoThreeSpectrum6709.graph sourceMap3388=true := by decide +kernel
theorem fusedMap3388_checked : acceptsGraphIso
    (fused (graph core3388) (root 9) 0 5) DegreeTwoThreeSpectrum5553.graph fusedMap3388=true := by decide +kernel
theorem certified3388 : Certified (graph core3388) (root 9) 0 5 :=
  of_native_maps core3388 DegreeTwoThreeSpectrum6709.graph DegreeTwoThreeSpectrum5553.graph
    sourceMap3388 fusedMap3388 sourceMap3388_checked fusedMap3388_checked
    DegreeTwoThreeFiniteComparisons.comparison3388
#print axioms sourceMap3388_checked
#print axioms fusedMap3388_checked
#print axioms certified3388
def sourceMap3388swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3388swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3388swap_checked : acceptsGraphIso
    (source (graph core3388) (root 9) 5 0) DegreeTwoThreeSpectrum6709.graph sourceMap3388swap=true := by decide +kernel
theorem fusedMap3388swap_checked : acceptsGraphIso
    (fused (graph core3388) (root 9) 5 0) DegreeTwoThreeSpectrum5553.graph fusedMap3388swap=true := by decide +kernel
theorem certified3388swap : Certified (graph core3388) (root 9) 5 0 :=
  of_native_maps core3388 DegreeTwoThreeSpectrum6709.graph DegreeTwoThreeSpectrum5553.graph
    sourceMap3388swap fusedMap3388swap sourceMap3388swap_checked fusedMap3388swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3388
#print axioms sourceMap3388swap_checked
#print axioms fusedMap3388swap_checked
#print axioms certified3388swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
