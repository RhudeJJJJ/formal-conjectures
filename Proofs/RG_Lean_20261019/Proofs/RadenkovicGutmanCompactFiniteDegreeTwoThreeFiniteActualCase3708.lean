/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3708 : Family 5 := level5.get ⟨14,by decide⟩
def sourceMap3708 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 9) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14,15] (sourceLabel 5 0 8 v)
def fusedMap3708 : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 0 8 v)
theorem sourceMap3708_checked : acceptsGraphIso
    (source (graph core3708) (root 5) 0 8) DegreeTwoThreeSpectrum3898.graph sourceMap3708=true := by decide +kernel
theorem fusedMap3708_checked : acceptsGraphIso
    (fused (graph core3708) (root 5) 0 8) DegreeTwoThreeSpectrum3902.graph fusedMap3708=true := by decide +kernel
theorem certified3708 : Certified (graph core3708) (root 5) 0 8 :=
  of_native_maps core3708 DegreeTwoThreeSpectrum3898.graph DegreeTwoThreeSpectrum3902.graph
    sourceMap3708 fusedMap3708 sourceMap3708_checked fusedMap3708_checked
    DegreeTwoThreeFiniteComparisons.comparison3708
#print axioms sourceMap3708_checked
#print axioms fusedMap3708_checked
#print axioms certified3708
def sourceMap3708swap : (Vertices 5 ⊕ Fin 9 ⊕ Fin 1) → Fin 16 :=
  fun v => ![3,4,5,6,7,8,2,1,0,10,11,12,13,14,15,9] (sourceLabel 5 8 0 v)
def fusedMap3708swap : (Vertices 5 ⊕ Fin 10) → Fin 16 :=
  fun v => ![4,5,6,7,8,9,3,2,1,0,10,11,12,13,14,15] (fusedLabel 5 8 0 v)
theorem sourceMap3708swap_checked : acceptsGraphIso
    (source (graph core3708) (root 5) 8 0) DegreeTwoThreeSpectrum3898.graph sourceMap3708swap=true := by decide +kernel
theorem fusedMap3708swap_checked : acceptsGraphIso
    (fused (graph core3708) (root 5) 8 0) DegreeTwoThreeSpectrum3902.graph fusedMap3708swap=true := by decide +kernel
theorem certified3708swap : Certified (graph core3708) (root 5) 8 0 :=
  of_native_maps core3708 DegreeTwoThreeSpectrum3898.graph DegreeTwoThreeSpectrum3902.graph
    sourceMap3708swap fusedMap3708swap sourceMap3708swap_checked fusedMap3708swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3708
#print axioms sourceMap3708swap_checked
#print axioms fusedMap3708swap_checked
#print axioms certified3708swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
