/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3712 : Family 6 := level6.get ⟨13,by decide⟩
def sourceMap3712 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3712 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3712_checked : acceptsGraphIso
    (source (graph core3712) (root 6) 0 8) DegreeTwoThreeSpectrum5029.graph sourceMap3712=true := by decide +kernel
theorem fusedMap3712_checked : acceptsGraphIso
    (fused (graph core3712) (root 6) 0 8) DegreeTwoThreeSpectrum5033.graph fusedMap3712=true := by decide +kernel
theorem certified3712 : Certified (graph core3712) (root 6) 0 8 :=
  of_native_maps core3712 DegreeTwoThreeSpectrum5029.graph DegreeTwoThreeSpectrum5033.graph
    sourceMap3712 fusedMap3712 sourceMap3712_checked fusedMap3712_checked
    DegreeTwoThreeFiniteComparisons.comparison3712
#print axioms sourceMap3712_checked
#print axioms fusedMap3712_checked
#print axioms certified3712
def sourceMap3712swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,16,9] (sourceLabel 6 8 0 v)
def fusedMap3712swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3712swap_checked : acceptsGraphIso
    (source (graph core3712) (root 6) 8 0) DegreeTwoThreeSpectrum5029.graph sourceMap3712swap=true := by decide +kernel
theorem fusedMap3712swap_checked : acceptsGraphIso
    (fused (graph core3712) (root 6) 8 0) DegreeTwoThreeSpectrum5033.graph fusedMap3712swap=true := by decide +kernel
theorem certified3712swap : Certified (graph core3712) (root 6) 8 0 :=
  of_native_maps core3712 DegreeTwoThreeSpectrum5029.graph DegreeTwoThreeSpectrum5033.graph
    sourceMap3712swap fusedMap3712swap sourceMap3712swap_checked fusedMap3712swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3712
#print axioms sourceMap3712swap_checked
#print axioms fusedMap3712swap_checked
#print axioms certified3712swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
