/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3453 : Family 9 := level9.get ⟨618,by decide⟩
def sourceMap3453 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3453 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3453_checked : acceptsGraphIso
    (source (graph core3453) (root 9) 0 5) DegreeTwoThreeSpectrum6342.graph sourceMap3453=true := by decide +kernel
theorem fusedMap3453_checked : acceptsGraphIso
    (fused (graph core3453) (root 9) 0 5) DegreeTwoThreeSpectrum6343.graph fusedMap3453=true := by decide +kernel
theorem certified3453 : Certified (graph core3453) (root 9) 0 5 :=
  of_native_maps core3453 DegreeTwoThreeSpectrum6342.graph DegreeTwoThreeSpectrum6343.graph
    sourceMap3453 fusedMap3453 sourceMap3453_checked fusedMap3453_checked
    DegreeTwoThreeFiniteComparisons.comparison3453
#print axioms sourceMap3453_checked
#print axioms fusedMap3453_checked
#print axioms certified3453
def sourceMap3453swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3453swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3453swap_checked : acceptsGraphIso
    (source (graph core3453) (root 9) 5 0) DegreeTwoThreeSpectrum6342.graph sourceMap3453swap=true := by decide +kernel
theorem fusedMap3453swap_checked : acceptsGraphIso
    (fused (graph core3453) (root 9) 5 0) DegreeTwoThreeSpectrum6343.graph fusedMap3453swap=true := by decide +kernel
theorem certified3453swap : Certified (graph core3453) (root 9) 5 0 :=
  of_native_maps core3453 DegreeTwoThreeSpectrum6342.graph DegreeTwoThreeSpectrum6343.graph
    sourceMap3453swap fusedMap3453swap sourceMap3453swap_checked fusedMap3453swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3453
#print axioms sourceMap3453swap_checked
#print axioms fusedMap3453swap_checked
#print axioms certified3453swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
