/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3473 : Family 9 := level9.get ⟨693,by decide⟩
def sourceMap3473 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,12,1,0,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3473 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3473_checked : acceptsGraphIso
    (source (graph core3473) (root 9) 0 5) DegreeTwoThreeSpectrum7071.graph sourceMap3473=true := by decide +kernel
theorem fusedMap3473_checked : acceptsGraphIso
    (fused (graph core3473) (root 9) 0 5) DegreeTwoThreeSpectrum5971.graph fusedMap3473=true := by decide +kernel
theorem certified3473 : Certified (graph core3473) (root 9) 0 5 :=
  of_native_maps core3473 DegreeTwoThreeSpectrum7071.graph DegreeTwoThreeSpectrum5971.graph
    sourceMap3473 fusedMap3473 sourceMap3473_checked fusedMap3473_checked
    DegreeTwoThreeFiniteComparisons.comparison3473
#print axioms sourceMap3473_checked
#print axioms fusedMap3473_checked
#print axioms certified3473
def sourceMap3473swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,13,14,15,16,12] (sourceLabel 9 5 0 v)
def fusedMap3473swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3473swap_checked : acceptsGraphIso
    (source (graph core3473) (root 9) 5 0) DegreeTwoThreeSpectrum7071.graph sourceMap3473swap=true := by decide +kernel
theorem fusedMap3473swap_checked : acceptsGraphIso
    (fused (graph core3473) (root 9) 5 0) DegreeTwoThreeSpectrum5971.graph fusedMap3473swap=true := by decide +kernel
theorem certified3473swap : Certified (graph core3473) (root 9) 5 0 :=
  of_native_maps core3473 DegreeTwoThreeSpectrum7071.graph DegreeTwoThreeSpectrum5971.graph
    sourceMap3473swap fusedMap3473swap sourceMap3473swap_checked fusedMap3473swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3473
#print axioms sourceMap3473swap_checked
#print axioms fusedMap3473swap_checked
#print axioms certified3473swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
