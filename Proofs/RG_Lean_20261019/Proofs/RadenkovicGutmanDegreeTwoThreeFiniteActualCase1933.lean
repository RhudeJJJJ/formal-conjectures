/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1933 : Family 10 := level10.get ⟨1449,by decide⟩
def sourceMap1933 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1933 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1933_checked : acceptsGraphIso
    (source (graph core1933) (root 10) 0 2) DegreeTwoThreeSpectrum3692.graph sourceMap1933=true := by decide +kernel
theorem fusedMap1933_checked : acceptsGraphIso
    (fused (graph core1933) (root 10) 0 2) DegreeTwoThreeSpectrum3689.graph fusedMap1933=true := by decide +kernel
theorem certified1933 : Certified (graph core1933) (root 10) 0 2 :=
  of_native_maps core1933 DegreeTwoThreeSpectrum3692.graph DegreeTwoThreeSpectrum3689.graph
    sourceMap1933 fusedMap1933 sourceMap1933_checked fusedMap1933_checked
    DegreeTwoThreeFiniteComparisons.comparison1933
#print axioms sourceMap1933_checked
#print axioms fusedMap1933_checked
#print axioms certified1933
def sourceMap1933swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1933swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1933swap_checked : acceptsGraphIso
    (source (graph core1933) (root 10) 2 0) DegreeTwoThreeSpectrum3692.graph sourceMap1933swap=true := by decide +kernel
theorem fusedMap1933swap_checked : acceptsGraphIso
    (fused (graph core1933) (root 10) 2 0) DegreeTwoThreeSpectrum3689.graph fusedMap1933swap=true := by decide +kernel
theorem certified1933swap : Certified (graph core1933) (root 10) 2 0 :=
  of_native_maps core1933 DegreeTwoThreeSpectrum3692.graph DegreeTwoThreeSpectrum3689.graph
    sourceMap1933swap fusedMap1933swap sourceMap1933swap_checked fusedMap1933swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1933
#print axioms sourceMap1933swap_checked
#print axioms fusedMap1933swap_checked
#print axioms certified1933swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
