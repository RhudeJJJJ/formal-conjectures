/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3125 : Family 7 := level7.get ⟨72,by decide⟩
def sourceMap3125 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3125 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3125_checked : acceptsGraphIso
    (source (graph core3125) (root 7) 0 5) DegreeTwoThreeSpectrum2511.graph sourceMap3125=true := by decide +kernel
theorem fusedMap3125_checked : acceptsGraphIso
    (fused (graph core3125) (root 7) 0 5) DegreeTwoThreeSpectrum2513.graph fusedMap3125=true := by decide +kernel
theorem certified3125 : Certified (graph core3125) (root 7) 0 5 :=
  of_native_maps core3125 DegreeTwoThreeSpectrum2511.graph DegreeTwoThreeSpectrum2513.graph
    sourceMap3125 fusedMap3125 sourceMap3125_checked fusedMap3125_checked
    DegreeTwoThreeFiniteComparisons.comparison3125
#print axioms sourceMap3125_checked
#print axioms fusedMap3125_checked
#print axioms certified3125
def sourceMap3125swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3125swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3125swap_checked : acceptsGraphIso
    (source (graph core3125) (root 7) 5 0) DegreeTwoThreeSpectrum2511.graph sourceMap3125swap=true := by decide +kernel
theorem fusedMap3125swap_checked : acceptsGraphIso
    (fused (graph core3125) (root 7) 5 0) DegreeTwoThreeSpectrum2513.graph fusedMap3125swap=true := by decide +kernel
theorem certified3125swap : Certified (graph core3125) (root 7) 5 0 :=
  of_native_maps core3125 DegreeTwoThreeSpectrum2511.graph DegreeTwoThreeSpectrum2513.graph
    sourceMap3125swap fusedMap3125swap sourceMap3125swap_checked fusedMap3125swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3125
#print axioms sourceMap3125swap_checked
#print axioms fusedMap3125swap_checked
#print axioms certified3125swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
