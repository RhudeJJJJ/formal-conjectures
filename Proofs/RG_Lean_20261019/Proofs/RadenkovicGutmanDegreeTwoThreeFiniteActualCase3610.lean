/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3610 : Family 8 := level8.get ⟨211,by decide⟩
def sourceMap3610 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3610 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3610_checked : acceptsGraphIso
    (source (graph core3610) (root 8) 0 6) DegreeTwoThreeSpectrum6206.graph sourceMap3610=true := by decide +kernel
theorem fusedMap3610_checked : acceptsGraphIso
    (fused (graph core3610) (root 8) 0 6) DegreeTwoThreeSpectrum5229.graph fusedMap3610=true := by decide +kernel
theorem certified3610 : Certified (graph core3610) (root 8) 0 6 :=
  of_native_maps core3610 DegreeTwoThreeSpectrum6206.graph DegreeTwoThreeSpectrum5229.graph
    sourceMap3610 fusedMap3610 sourceMap3610_checked fusedMap3610_checked
    DegreeTwoThreeFiniteComparisons.comparison3610
#print axioms sourceMap3610_checked
#print axioms fusedMap3610_checked
#print axioms certified3610
def sourceMap3610swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3610swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3610swap_checked : acceptsGraphIso
    (source (graph core3610) (root 8) 6 0) DegreeTwoThreeSpectrum6206.graph sourceMap3610swap=true := by decide +kernel
theorem fusedMap3610swap_checked : acceptsGraphIso
    (fused (graph core3610) (root 8) 6 0) DegreeTwoThreeSpectrum5229.graph fusedMap3610swap=true := by decide +kernel
theorem certified3610swap : Certified (graph core3610) (root 8) 6 0 :=
  of_native_maps core3610 DegreeTwoThreeSpectrum6206.graph DegreeTwoThreeSpectrum5229.graph
    sourceMap3610swap fusedMap3610swap sourceMap3610swap_checked fusedMap3610swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3610
#print axioms sourceMap3610swap_checked
#print axioms fusedMap3610swap_checked
#print axioms certified3610swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
