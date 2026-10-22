/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons69
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3487 : Family 6 := level6.get ⟨9,by decide⟩
def sourceMap3487 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 7) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14] (sourceLabel 6 0 6 v)
def fusedMap3487 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 0 6 v)
theorem sourceMap3487_checked : acceptsGraphIso
    (source (graph core3487) (root 6) 0 6) DegreeTwoThreeSpectrum2335.graph sourceMap3487=true := by decide +kernel
theorem fusedMap3487_checked : acceptsGraphIso
    (fused (graph core3487) (root 6) 0 6) DegreeTwoThreeSpectrum2338.graph fusedMap3487=true := by decide +kernel
theorem certified3487 : Certified (graph core3487) (root 6) 0 6 :=
  of_native_maps core3487 DegreeTwoThreeSpectrum2335.graph DegreeTwoThreeSpectrum2338.graph
    sourceMap3487 fusedMap3487 sourceMap3487_checked fusedMap3487_checked
    DegreeTwoThreeFiniteComparisons.comparison3487
#print axioms sourceMap3487_checked
#print axioms fusedMap3487_checked
#print axioms certified3487
def sourceMap3487swap : (Vertices 6 ⊕ Fin 7 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,0,9,10,11,12,13,14,8] (sourceLabel 6 6 0 v)
def fusedMap3487swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 6 0 v)
theorem sourceMap3487swap_checked : acceptsGraphIso
    (source (graph core3487) (root 6) 6 0) DegreeTwoThreeSpectrum2335.graph sourceMap3487swap=true := by decide +kernel
theorem fusedMap3487swap_checked : acceptsGraphIso
    (fused (graph core3487) (root 6) 6 0) DegreeTwoThreeSpectrum2338.graph fusedMap3487swap=true := by decide +kernel
theorem certified3487swap : Certified (graph core3487) (root 6) 6 0 :=
  of_native_maps core3487 DegreeTwoThreeSpectrum2335.graph DegreeTwoThreeSpectrum2338.graph
    sourceMap3487swap fusedMap3487swap sourceMap3487swap_checked fusedMap3487swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3487
#print axioms sourceMap3487swap_checked
#print axioms fusedMap3487swap_checked
#print axioms certified3487swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
