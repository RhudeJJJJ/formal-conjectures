/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3493 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap3493 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3493 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3493_checked : acceptsGraphIso
    (source (graph core3493) (root 6) 0 6) DegreeTwoThreeSpectrum2572.graph sourceMap3493=true := by decide +kernel
theorem fusedMap3493_checked : acceptsGraphIso
    (fused (graph core3493) (root 6) 0 6) DegreeTwoThreeSpectrum2328.graph fusedMap3493=true := by decide +kernel
theorem certified3493 : Certified (graph core3493) (root 6) 0 6 :=
  of_native_maps core3493 DegreeTwoThreeSpectrum2572.graph DegreeTwoThreeSpectrum2328.graph
    sourceMap3493 fusedMap3493 sourceMap3493_checked fusedMap3493_checked
    DegreeTwoThreeFiniteComparisons.comparison3493
#print axioms sourceMap3493_checked
#print axioms fusedMap3493_checked
#print axioms certified3493
def sourceMap3493swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,9] (sourceLabel 6 6 0 v)
def fusedMap3493swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3493swap_checked : acceptsGraphIso
    (source (graph core3493) (root 6) 6 0) DegreeTwoThreeSpectrum2572.graph sourceMap3493swap=true := by decide +kernel
theorem fusedMap3493swap_checked : acceptsGraphIso
    (fused (graph core3493) (root 6) 6 0) DegreeTwoThreeSpectrum2328.graph fusedMap3493swap=true := by decide +kernel
theorem certified3493swap : Certified (graph core3493) (root 6) 6 0 :=
  of_native_maps core3493 DegreeTwoThreeSpectrum2572.graph DegreeTwoThreeSpectrum2328.graph
    sourceMap3493swap fusedMap3493swap sourceMap3493swap_checked fusedMap3493swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3493
#print axioms sourceMap3493swap_checked
#print axioms fusedMap3493swap_checked
#print axioms certified3493swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
