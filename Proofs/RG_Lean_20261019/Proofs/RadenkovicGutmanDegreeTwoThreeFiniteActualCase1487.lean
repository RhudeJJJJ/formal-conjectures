/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1487 : Family 10 := level10.get ⟨249,by decide⟩
def sourceMap1487 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1487 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1487_checked : acceptsGraphIso
    (source (graph core1487) (root 10) 0 2) DegreeTwoThreeSpectrum2583.graph sourceMap1487=true := by decide +kernel
theorem fusedMap1487_checked : acceptsGraphIso
    (fused (graph core1487) (root 10) 0 2) DegreeTwoThreeSpectrum2585.graph fusedMap1487=true := by decide +kernel
theorem certified1487 : Certified (graph core1487) (root 10) 0 2 :=
  of_native_maps core1487 DegreeTwoThreeSpectrum2583.graph DegreeTwoThreeSpectrum2585.graph
    sourceMap1487 fusedMap1487 sourceMap1487_checked fusedMap1487_checked
    DegreeTwoThreeFiniteComparisons.comparison1487
#print axioms sourceMap1487_checked
#print axioms fusedMap1487_checked
#print axioms certified1487
def sourceMap1487swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1487swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1487swap_checked : acceptsGraphIso
    (source (graph core1487) (root 10) 2 0) DegreeTwoThreeSpectrum2583.graph sourceMap1487swap=true := by decide +kernel
theorem fusedMap1487swap_checked : acceptsGraphIso
    (fused (graph core1487) (root 10) 2 0) DegreeTwoThreeSpectrum2585.graph fusedMap1487swap=true := by decide +kernel
theorem certified1487swap : Certified (graph core1487) (root 10) 2 0 :=
  of_native_maps core1487 DegreeTwoThreeSpectrum2583.graph DegreeTwoThreeSpectrum2585.graph
    sourceMap1487swap fusedMap1487swap sourceMap1487swap_checked fusedMap1487swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1487
#print axioms sourceMap1487swap_checked
#print axioms fusedMap1487swap_checked
#print axioms certified1487swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
