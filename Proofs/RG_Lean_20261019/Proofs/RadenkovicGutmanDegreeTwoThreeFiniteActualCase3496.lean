/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3496 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap3496 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3496 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3496_checked : acceptsGraphIso
    (source (graph core3496) (root 6) 0 6) DegreeTwoThreeSpectrum2741.graph sourceMap3496=true := by decide +kernel
theorem fusedMap3496_checked : acceptsGraphIso
    (fused (graph core3496) (root 6) 0 6) DegreeTwoThreeSpectrum2360.graph fusedMap3496=true := by decide +kernel
theorem certified3496 : Certified (graph core3496) (root 6) 0 6 :=
  of_native_maps core3496 DegreeTwoThreeSpectrum2741.graph DegreeTwoThreeSpectrum2360.graph
    sourceMap3496 fusedMap3496 sourceMap3496_checked fusedMap3496_checked
    DegreeTwoThreeFiniteComparisons.comparison3496
#print axioms sourceMap3496_checked
#print axioms fusedMap3496_checked
#print axioms certified3496
def sourceMap3496swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,9] (sourceLabel 6 6 0 v)
def fusedMap3496swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3496swap_checked : acceptsGraphIso
    (source (graph core3496) (root 6) 6 0) DegreeTwoThreeSpectrum2741.graph sourceMap3496swap=true := by decide +kernel
theorem fusedMap3496swap_checked : acceptsGraphIso
    (fused (graph core3496) (root 6) 6 0) DegreeTwoThreeSpectrum2360.graph fusedMap3496swap=true := by decide +kernel
theorem certified3496swap : Certified (graph core3496) (root 6) 6 0 :=
  of_native_maps core3496 DegreeTwoThreeSpectrum2741.graph DegreeTwoThreeSpectrum2360.graph
    sourceMap3496swap fusedMap3496swap sourceMap3496swap_checked fusedMap3496swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3496
#print axioms sourceMap3496swap_checked
#print axioms fusedMap3496swap_checked
#print axioms certified3496swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
