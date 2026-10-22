/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3131 : Family 7 := level7.get ⟨84,by decide⟩
def sourceMap3131 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (sourceLabel 7 0 5 v)
def fusedMap3131 : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 0 5 v)
theorem sourceMap3131_checked : acceptsGraphIso
    (source (graph core3131) (root 7) 0 5) DegreeTwoThreeSpectrum2663.graph sourceMap3131=true := by decide +kernel
theorem fusedMap3131_checked : acceptsGraphIso
    (fused (graph core3131) (root 7) 0 5) DegreeTwoThreeSpectrum2665.graph fusedMap3131=true := by decide +kernel
theorem certified3131 : Certified (graph core3131) (root 7) 0 5 :=
  of_native_maps core3131 DegreeTwoThreeSpectrum2663.graph DegreeTwoThreeSpectrum2665.graph
    sourceMap3131 fusedMap3131 sourceMap3131_checked fusedMap3131_checked
    DegreeTwoThreeFiniteComparisons.comparison3131
#print axioms sourceMap3131_checked
#print axioms fusedMap3131_checked
#print axioms certified3131
def sourceMap3131swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,9] (sourceLabel 7 5 0 v)
def fusedMap3131swap : (Vertices 7 ⊕ Fin 7) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14] (fusedLabel 7 5 0 v)
theorem sourceMap3131swap_checked : acceptsGraphIso
    (source (graph core3131) (root 7) 5 0) DegreeTwoThreeSpectrum2663.graph sourceMap3131swap=true := by decide +kernel
theorem fusedMap3131swap_checked : acceptsGraphIso
    (fused (graph core3131) (root 7) 5 0) DegreeTwoThreeSpectrum2665.graph fusedMap3131swap=true := by decide +kernel
theorem certified3131swap : Certified (graph core3131) (root 7) 5 0 :=
  of_native_maps core3131 DegreeTwoThreeSpectrum2663.graph DegreeTwoThreeSpectrum2665.graph
    sourceMap3131swap fusedMap3131swap sourceMap3131swap_checked fusedMap3131swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3131
#print axioms sourceMap3131swap_checked
#print axioms fusedMap3131swap_checked
#print axioms certified3131swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
