/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3135 : Family 7 := level7.get ⟨91,by decide⟩
def sourceMap3135 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3135 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3135_checked : acceptsGraphIso
    (source (graph core3135) (root 7) 0 5) DegreeTwoThreeSpectrum2736.graph sourceMap3135=true := by decide +kernel
theorem fusedMap3135_checked : acceptsGraphIso
    (fused (graph core3135) (root 7) 0 5) DegreeTwoThreeSpectrum2738.graph fusedMap3135=true := by decide +kernel
theorem certified3135 : Certified (graph core3135) (root 7) 0 5 :=
  of_native_maps core3135 DegreeTwoThreeSpectrum2736.graph DegreeTwoThreeSpectrum2738.graph
    sourceMap3135 fusedMap3135 sourceMap3135_checked fusedMap3135_checked
    DegreeTwoThreeFiniteComparisons.comparison3135
#print axioms sourceMap3135_checked
#print axioms fusedMap3135_checked
#print axioms certified3135
def sourceMap3135swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3135swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3135swap_checked : acceptsGraphIso
    (source (graph core3135) (root 7) 5 0) DegreeTwoThreeSpectrum2736.graph sourceMap3135swap=true := by decide +kernel
theorem fusedMap3135swap_checked : acceptsGraphIso
    (fused (graph core3135) (root 7) 5 0) DegreeTwoThreeSpectrum2738.graph fusedMap3135swap=true := by decide +kernel
theorem certified3135swap : Certified (graph core3135) (root 7) 5 0 :=
  of_native_maps core3135 DegreeTwoThreeSpectrum2736.graph DegreeTwoThreeSpectrum2738.graph
    sourceMap3135swap fusedMap3135swap sourceMap3135swap_checked fusedMap3135swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3135
#print axioms sourceMap3135swap_checked
#print axioms fusedMap3135swap_checked
#print axioms certified3135swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
