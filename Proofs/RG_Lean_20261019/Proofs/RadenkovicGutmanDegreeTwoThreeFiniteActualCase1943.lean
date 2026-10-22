/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1943 : Family 10 := level10.get ⟨1468,by decide⟩
def sourceMap1943 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1943 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1943_checked : acceptsGraphIso
    (source (graph core1943) (root 10) 0 2) DegreeTwoThreeSpectrum3536.graph sourceMap1943=true := by decide +kernel
theorem fusedMap1943_checked : acceptsGraphIso
    (fused (graph core1943) (root 10) 0 2) DegreeTwoThreeSpectrum3709.graph fusedMap1943=true := by decide +kernel
theorem certified1943 : Certified (graph core1943) (root 10) 0 2 :=
  of_native_maps core1943 DegreeTwoThreeSpectrum3536.graph DegreeTwoThreeSpectrum3709.graph
    sourceMap1943 fusedMap1943 sourceMap1943_checked fusedMap1943_checked
    DegreeTwoThreeFiniteComparisons.comparison1943
#print axioms sourceMap1943_checked
#print axioms fusedMap1943_checked
#print axioms certified1943
def sourceMap1943swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1943swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1943swap_checked : acceptsGraphIso
    (source (graph core1943) (root 10) 2 0) DegreeTwoThreeSpectrum3536.graph sourceMap1943swap=true := by decide +kernel
theorem fusedMap1943swap_checked : acceptsGraphIso
    (fused (graph core1943) (root 10) 2 0) DegreeTwoThreeSpectrum3709.graph fusedMap1943swap=true := by decide +kernel
theorem certified1943swap : Certified (graph core1943) (root 10) 2 0 :=
  of_native_maps core1943 DegreeTwoThreeSpectrum3536.graph DegreeTwoThreeSpectrum3709.graph
    sourceMap1943swap fusedMap1943swap sourceMap1943swap_checked fusedMap1943swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1943
#print axioms sourceMap1943swap_checked
#print axioms fusedMap1943swap_checked
#print axioms certified1943swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
