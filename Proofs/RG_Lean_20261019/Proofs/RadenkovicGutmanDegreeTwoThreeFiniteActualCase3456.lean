/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3456 : Family 9 := level9.get ⟨632,by decide⟩
def sourceMap3456 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3456 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3456_checked : acceptsGraphIso
    (source (graph core3456) (root 9) 0 5) DegreeTwoThreeSpectrum6477.graph sourceMap3456=true := by decide +kernel
theorem fusedMap3456_checked : acceptsGraphIso
    (fused (graph core3456) (root 9) 0 5) DegreeTwoThreeSpectrum6478.graph fusedMap3456=true := by decide +kernel
theorem certified3456 : Certified (graph core3456) (root 9) 0 5 :=
  of_native_maps core3456 DegreeTwoThreeSpectrum6477.graph DegreeTwoThreeSpectrum6478.graph
    sourceMap3456 fusedMap3456 sourceMap3456_checked fusedMap3456_checked
    DegreeTwoThreeFiniteComparisons.comparison3456
#print axioms sourceMap3456_checked
#print axioms fusedMap3456_checked
#print axioms certified3456
def sourceMap3456swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3456swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3456swap_checked : acceptsGraphIso
    (source (graph core3456) (root 9) 5 0) DegreeTwoThreeSpectrum6477.graph sourceMap3456swap=true := by decide +kernel
theorem fusedMap3456swap_checked : acceptsGraphIso
    (fused (graph core3456) (root 9) 5 0) DegreeTwoThreeSpectrum6478.graph fusedMap3456swap=true := by decide +kernel
theorem certified3456swap : Certified (graph core3456) (root 9) 5 0 :=
  of_native_maps core3456 DegreeTwoThreeSpectrum6477.graph DegreeTwoThreeSpectrum6478.graph
    sourceMap3456swap fusedMap3456swap sourceMap3456swap_checked fusedMap3456swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3456
#print axioms sourceMap3456swap_checked
#print axioms fusedMap3456swap_checked
#print axioms certified3456swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
