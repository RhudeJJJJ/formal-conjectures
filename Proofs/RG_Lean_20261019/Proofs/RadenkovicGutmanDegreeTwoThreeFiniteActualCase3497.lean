/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3497 : Family 6 := level6.get ⟨33,by decide⟩
def sourceMap3497 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3497 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3497_checked : acceptsGraphIso
    (source (graph core3497) (root 6) 0 6) DegreeTwoThreeSpectrum2819.graph sourceMap3497=true := by decide +kernel
theorem fusedMap3497_checked : acceptsGraphIso
    (fused (graph core3497) (root 6) 0 6) DegreeTwoThreeSpectrum2381.graph fusedMap3497=true := by decide +kernel
theorem certified3497 : Certified (graph core3497) (root 6) 0 6 :=
  of_native_maps core3497 DegreeTwoThreeSpectrum2819.graph DegreeTwoThreeSpectrum2381.graph
    sourceMap3497 fusedMap3497 sourceMap3497_checked fusedMap3497_checked
    DegreeTwoThreeFiniteComparisons.comparison3497
#print axioms sourceMap3497_checked
#print axioms fusedMap3497_checked
#print axioms certified3497
def sourceMap3497swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,9] (sourceLabel 6 6 0 v)
def fusedMap3497swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3497swap_checked : acceptsGraphIso
    (source (graph core3497) (root 6) 6 0) DegreeTwoThreeSpectrum2819.graph sourceMap3497swap=true := by decide +kernel
theorem fusedMap3497swap_checked : acceptsGraphIso
    (fused (graph core3497) (root 6) 6 0) DegreeTwoThreeSpectrum2381.graph fusedMap3497swap=true := by decide +kernel
theorem certified3497swap : Certified (graph core3497) (root 6) 6 0 :=
  of_native_maps core3497 DegreeTwoThreeSpectrum2819.graph DegreeTwoThreeSpectrum2381.graph
    sourceMap3497swap fusedMap3497swap sourceMap3497swap_checked fusedMap3497swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3497
#print axioms sourceMap3497swap_checked
#print axioms fusedMap3497swap_checked
#print axioms certified3497swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
