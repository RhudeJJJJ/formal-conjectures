/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3709 : Family 5 := level5.get ⟨15,by decide⟩
def sourceMap3709 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (sourceLabel 5 0 8 v)
def fusedMap3709 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 0 8 v)
theorem sourceMap3709_checked : acceptsGraphIso
    (source (graph core3709) (root 5) 0 8) DegreeTwoThreeSpectrum3918.graph sourceMap3709=true := by decide +kernel
theorem fusedMap3709_checked : acceptsGraphIso
    (fused (graph core3709) (root 5) 0 8) DegreeTwoThreeSpectrum3922.graph fusedMap3709=true := by decide +kernel
theorem certified3709 : Certified (graph core3709) (root 5) 0 8 :=
  of_native_maps core3709 DegreeTwoThreeSpectrum3918.graph DegreeTwoThreeSpectrum3922.graph
    sourceMap3709 fusedMap3709 sourceMap3709_checked fusedMap3709_checked
    DegreeTwoThreeFiniteComparisons.comparison3709
#print axioms sourceMap3709_checked
#print axioms fusedMap3709_checked
#print axioms certified3709
def sourceMap3709swap : (Vertices 5 ⊕ Fin 9 ⊕ Fin 1) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,10,11,12,13,14,15,9] (sourceLabel 5 8 0 v)
def fusedMap3709swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 8 0 v)
theorem sourceMap3709swap_checked : acceptsGraphIso
    (source (graph core3709) (root 5) 8 0) DegreeTwoThreeSpectrum3918.graph sourceMap3709swap=true := by decide +kernel
theorem fusedMap3709swap_checked : acceptsGraphIso
    (fused (graph core3709) (root 5) 8 0) DegreeTwoThreeSpectrum3922.graph fusedMap3709swap=true := by decide +kernel
theorem certified3709swap : Certified (graph core3709) (root 5) 8 0 :=
  of_native_maps core3709 DegreeTwoThreeSpectrum3918.graph DegreeTwoThreeSpectrum3922.graph
    sourceMap3709swap fusedMap3709swap sourceMap3709swap_checked fusedMap3709swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3709
#print axioms sourceMap3709swap_checked
#print axioms fusedMap3709swap_checked
#print axioms certified3709swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
