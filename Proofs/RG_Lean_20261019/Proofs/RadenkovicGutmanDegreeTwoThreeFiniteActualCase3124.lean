/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3124 : Family 7 := level7.get ⟨68,by decide⟩
def sourceMap3124 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3124 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3124_checked : acceptsGraphIso
    (source (graph core3124) (root 7) 0 5) DegreeTwoThreeSpectrum2475.graph sourceMap3124=true := by decide +kernel
theorem fusedMap3124_checked : acceptsGraphIso
    (fused (graph core3124) (root 7) 0 5) DegreeTwoThreeSpectrum2477.graph fusedMap3124=true := by decide +kernel
theorem certified3124 : Certified (graph core3124) (root 7) 0 5 :=
  of_native_maps core3124 DegreeTwoThreeSpectrum2475.graph DegreeTwoThreeSpectrum2477.graph
    sourceMap3124 fusedMap3124 sourceMap3124_checked fusedMap3124_checked
    DegreeTwoThreeFiniteComparisons.comparison3124
#print axioms sourceMap3124_checked
#print axioms fusedMap3124_checked
#print axioms certified3124
def sourceMap3124swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3124swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3124swap_checked : acceptsGraphIso
    (source (graph core3124) (root 7) 5 0) DegreeTwoThreeSpectrum2475.graph sourceMap3124swap=true := by decide +kernel
theorem fusedMap3124swap_checked : acceptsGraphIso
    (fused (graph core3124) (root 7) 5 0) DegreeTwoThreeSpectrum2477.graph fusedMap3124swap=true := by decide +kernel
theorem certified3124swap : Certified (graph core3124) (root 7) 5 0 :=
  of_native_maps core3124 DegreeTwoThreeSpectrum2475.graph DegreeTwoThreeSpectrum2477.graph
    sourceMap3124swap fusedMap3124swap sourceMap3124swap_checked fusedMap3124swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3124
#print axioms sourceMap3124swap_checked
#print axioms fusedMap3124swap_checked
#print axioms certified3124swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
