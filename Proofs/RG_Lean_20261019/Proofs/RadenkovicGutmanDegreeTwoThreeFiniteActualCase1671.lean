/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1671 : Family 10 := level10.get ⟨807,by decide⟩
def sourceMap1671 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,11,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1671 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1671_checked : acceptsGraphIso
    (source (graph core1671) (root 10) 0 2) DegreeTwoThreeSpectrum3600.graph sourceMap1671=true := by decide +kernel
theorem fusedMap1671_checked : acceptsGraphIso
    (fused (graph core1671) (root 10) 0 2) DegreeTwoThreeSpectrum2776.graph fusedMap1671=true := by decide +kernel
theorem certified1671 : Certified (graph core1671) (root 10) 0 2 :=
  of_native_maps core1671 DegreeTwoThreeSpectrum3600.graph DegreeTwoThreeSpectrum2776.graph
    sourceMap1671 fusedMap1671 sourceMap1671_checked fusedMap1671_checked
    DegreeTwoThreeFiniteComparisons.comparison1671
#print axioms sourceMap1671_checked
#print axioms fusedMap1671_checked
#print axioms certified1671
def sourceMap1671swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,12,13,14,10,7,8,9,11] (sourceLabel 10 2 0 v)
def fusedMap1671swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1671swap_checked : acceptsGraphIso
    (source (graph core1671) (root 10) 2 0) DegreeTwoThreeSpectrum3600.graph sourceMap1671swap=true := by decide +kernel
theorem fusedMap1671swap_checked : acceptsGraphIso
    (fused (graph core1671) (root 10) 2 0) DegreeTwoThreeSpectrum2776.graph fusedMap1671swap=true := by decide +kernel
theorem certified1671swap : Certified (graph core1671) (root 10) 2 0 :=
  of_native_maps core1671 DegreeTwoThreeSpectrum3600.graph DegreeTwoThreeSpectrum2776.graph
    sourceMap1671swap fusedMap1671swap sourceMap1671swap_checked fusedMap1671swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1671
#print axioms sourceMap1671swap_checked
#print axioms fusedMap1671swap_checked
#print axioms certified1671swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
