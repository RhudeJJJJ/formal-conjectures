/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1743 : Family 10 := level10.get ⟨980,by decide⟩
def sourceMap1743 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![1,0,11,12,13,14,2,3,4,5,6,10,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1743 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,5,6,7,8,9,1,2,3,4] (fusedLabel 10 0 2 v)
theorem sourceMap1743_checked : acceptsGraphIso
    (source (graph core1743) (root 10) 0 2) DegreeTwoThreeSpectrum3119.graph sourceMap1743=true := by decide +kernel
theorem fusedMap1743_checked : acceptsGraphIso
    (fused (graph core1743) (root 10) 0 2) DegreeTwoThreeSpectrum2944.graph fusedMap1743=true := by decide +kernel
theorem certified1743 : Certified (graph core1743) (root 10) 0 2 :=
  of_native_maps core1743 DegreeTwoThreeSpectrum3119.graph DegreeTwoThreeSpectrum2944.graph
    sourceMap1743 fusedMap1743 sourceMap1743_checked fusedMap1743_checked
    DegreeTwoThreeFiniteComparisons.comparison1743
#print axioms sourceMap1743_checked
#print axioms fusedMap1743_checked
#print axioms certified1743
def sourceMap1743swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![1,0,11,12,13,14,2,3,4,5,6,7,8,9,10] (sourceLabel 10 2 0 v)
def fusedMap1743swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,5,6,7,8,9,1,2,3,4] (fusedLabel 10 2 0 v)
theorem sourceMap1743swap_checked : acceptsGraphIso
    (source (graph core1743) (root 10) 2 0) DegreeTwoThreeSpectrum3119.graph sourceMap1743swap=true := by decide +kernel
theorem fusedMap1743swap_checked : acceptsGraphIso
    (fused (graph core1743) (root 10) 2 0) DegreeTwoThreeSpectrum2944.graph fusedMap1743swap=true := by decide +kernel
theorem certified1743swap : Certified (graph core1743) (root 10) 2 0 :=
  of_native_maps core1743 DegreeTwoThreeSpectrum3119.graph DegreeTwoThreeSpectrum2944.graph
    sourceMap1743swap fusedMap1743swap sourceMap1743swap_checked fusedMap1743swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1743
#print axioms sourceMap1743swap_checked
#print axioms fusedMap1743swap_checked
#print axioms certified1743swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
