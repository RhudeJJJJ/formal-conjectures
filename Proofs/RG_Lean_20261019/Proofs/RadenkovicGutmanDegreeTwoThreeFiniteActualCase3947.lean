/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3947 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap3947 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,10,8,9,1,0,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3947 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3947_checked : acceptsGraphIso
    (source (graph core3947) (root 6) 1 5) DegreeTwoThreeSpectrum3025.graph sourceMap3947=true := by decide +kernel
theorem fusedMap3947_checked : acceptsGraphIso
    (fused (graph core3947) (root 6) 1 5) DegreeTwoThreeSpectrum2444.graph fusedMap3947=true := by decide +kernel
theorem certified3947 : Certified (graph core3947) (root 6) 1 5 :=
  of_native_maps core3947 DegreeTwoThreeSpectrum3025.graph DegreeTwoThreeSpectrum2444.graph
    sourceMap3947 fusedMap3947 sourceMap3947_checked fusedMap3947_checked
    DegreeTwoThreeFiniteComparisons.comparison3947
#print axioms sourceMap3947_checked
#print axioms fusedMap3947_checked
#print axioms certified3947
def sourceMap3947swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,10,1,0,11,12,13,14,8,9] (sourceLabel 6 5 1 v)
def fusedMap3947swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![3,4,5,6,7,8,9,2,1,0,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3947swap_checked : acceptsGraphIso
    (source (graph core3947) (root 6) 5 1) DegreeTwoThreeSpectrum3025.graph sourceMap3947swap=true := by decide +kernel
theorem fusedMap3947swap_checked : acceptsGraphIso
    (fused (graph core3947) (root 6) 5 1) DegreeTwoThreeSpectrum2444.graph fusedMap3947swap=true := by decide +kernel
theorem certified3947swap : Certified (graph core3947) (root 6) 5 1 :=
  of_native_maps core3947 DegreeTwoThreeSpectrum3025.graph DegreeTwoThreeSpectrum2444.graph
    sourceMap3947swap fusedMap3947swap sourceMap3947swap_checked fusedMap3947swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3947
#print axioms sourceMap3947swap_checked
#print axioms fusedMap3947swap_checked
#print axioms certified3947swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
