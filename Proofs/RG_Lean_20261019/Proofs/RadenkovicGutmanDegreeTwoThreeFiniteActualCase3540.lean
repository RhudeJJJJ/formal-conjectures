/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3540 : Family 8 := level8.get ⟨13,by decide⟩
def sourceMap3540 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3540 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3540_checked : acceptsGraphIso
    (source (graph core3540) (root 8) 0 6) DegreeTwoThreeSpectrum5000.graph sourceMap3540=true := by decide +kernel
theorem fusedMap3540_checked : acceptsGraphIso
    (fused (graph core3540) (root 8) 0 6) DegreeTwoThreeSpectrum5002.graph fusedMap3540=true := by decide +kernel
theorem certified3540 : Certified (graph core3540) (root 8) 0 6 :=
  of_native_maps core3540 DegreeTwoThreeSpectrum5000.graph DegreeTwoThreeSpectrum5002.graph
    sourceMap3540 fusedMap3540 sourceMap3540_checked fusedMap3540_checked
    DegreeTwoThreeFiniteComparisons.comparison3540
#print axioms sourceMap3540_checked
#print axioms fusedMap3540_checked
#print axioms certified3540
def sourceMap3540swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,10,11,12,13,14,15,16,9] (sourceLabel 8 6 0 v)
def fusedMap3540swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3540swap_checked : acceptsGraphIso
    (source (graph core3540) (root 8) 6 0) DegreeTwoThreeSpectrum5000.graph sourceMap3540swap=true := by decide +kernel
theorem fusedMap3540swap_checked : acceptsGraphIso
    (fused (graph core3540) (root 8) 6 0) DegreeTwoThreeSpectrum5002.graph fusedMap3540swap=true := by decide +kernel
theorem certified3540swap : Certified (graph core3540) (root 8) 6 0 :=
  of_native_maps core3540 DegreeTwoThreeSpectrum5000.graph DegreeTwoThreeSpectrum5002.graph
    sourceMap3540swap fusedMap3540swap sourceMap3540swap_checked fusedMap3540swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3540
#print axioms sourceMap3540swap_checked
#print axioms fusedMap3540swap_checked
#print axioms certified3540swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
