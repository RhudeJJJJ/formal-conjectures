/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3105 : Family 7 := level7.get ⟨16,by decide⟩
def sourceMap3105 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3105 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3105_checked : acceptsGraphIso
    (source (graph core3105) (root 7) 0 5) DegreeTwoThreeSpectrum2372.graph sourceMap3105=true := by decide +kernel
theorem fusedMap3105_checked : acceptsGraphIso
    (fused (graph core3105) (root 7) 0 5) DegreeTwoThreeSpectrum2374.graph fusedMap3105=true := by decide +kernel
theorem certified3105 : Certified (graph core3105) (root 7) 0 5 :=
  of_native_maps core3105 DegreeTwoThreeSpectrum2372.graph DegreeTwoThreeSpectrum2374.graph
    sourceMap3105 fusedMap3105 sourceMap3105_checked fusedMap3105_checked
    DegreeTwoThreeFiniteComparisons.comparison3105
#print axioms sourceMap3105_checked
#print axioms fusedMap3105_checked
#print axioms certified3105
def sourceMap3105swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,9,10,11,12,13,14,8] (sourceLabel 7 5 0 v)
def fusedMap3105swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3105swap_checked : acceptsGraphIso
    (source (graph core3105) (root 7) 5 0) DegreeTwoThreeSpectrum2372.graph sourceMap3105swap=true := by decide +kernel
theorem fusedMap3105swap_checked : acceptsGraphIso
    (fused (graph core3105) (root 7) 5 0) DegreeTwoThreeSpectrum2374.graph fusedMap3105swap=true := by decide +kernel
theorem certified3105swap : Certified (graph core3105) (root 7) 5 0 :=
  of_native_maps core3105 DegreeTwoThreeSpectrum2372.graph DegreeTwoThreeSpectrum2374.graph
    sourceMap3105swap fusedMap3105swap sourceMap3105swap_checked fusedMap3105swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3105
#print axioms sourceMap3105swap_checked
#print axioms fusedMap3105swap_checked
#print axioms certified3105swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
