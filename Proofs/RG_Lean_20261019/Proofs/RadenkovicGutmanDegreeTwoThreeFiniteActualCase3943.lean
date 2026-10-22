/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3943 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap3943 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,7,8,0,10,11,12,13,14] (sourceLabel 6 1 5 v)
def fusedMap3943 : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 1 5 v)
theorem sourceMap3943_checked : acceptsGraphIso
    (source (graph core3943) (root 6) 1 5) DegreeTwoThreeSpectrum2704.graph sourceMap3943=true := by decide +kernel
theorem fusedMap3943_checked : acceptsGraphIso
    (fused (graph core3943) (root 6) 1 5) DegreeTwoThreeSpectrum2355.graph fusedMap3943=true := by decide +kernel
theorem certified3943 : Certified (graph core3943) (root 6) 1 5 :=
  of_native_maps core3943 DegreeTwoThreeSpectrum2704.graph DegreeTwoThreeSpectrum2355.graph
    sourceMap3943 fusedMap3943 sourceMap3943_checked fusedMap3943_checked
    DegreeTwoThreeFiniteComparisons.comparison3943
#print axioms sourceMap3943_checked
#print axioms fusedMap3943_checked
#print axioms certified3943
def sourceMap3943swap : (Vertices 6 ⊕ Fin 6 ⊕ Fin 2) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,9,0,10,11,12,13,14,7,8] (sourceLabel 6 5 1 v)
def fusedMap3943swap : (Vertices 6 ⊕ Fin 8) → Fin 15 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14] (fusedLabel 6 5 1 v)
theorem sourceMap3943swap_checked : acceptsGraphIso
    (source (graph core3943) (root 6) 5 1) DegreeTwoThreeSpectrum2704.graph sourceMap3943swap=true := by decide +kernel
theorem fusedMap3943swap_checked : acceptsGraphIso
    (fused (graph core3943) (root 6) 5 1) DegreeTwoThreeSpectrum2355.graph fusedMap3943swap=true := by decide +kernel
theorem certified3943swap : Certified (graph core3943) (root 6) 5 1 :=
  of_native_maps core3943 DegreeTwoThreeSpectrum2704.graph DegreeTwoThreeSpectrum2355.graph
    sourceMap3943swap fusedMap3943swap sourceMap3943swap_checked fusedMap3943swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3943
#print axioms sourceMap3943swap_checked
#print axioms fusedMap3943swap_checked
#print axioms certified3943swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
