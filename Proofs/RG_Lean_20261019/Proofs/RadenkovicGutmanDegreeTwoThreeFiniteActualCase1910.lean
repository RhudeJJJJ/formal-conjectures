/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1910 : Family 10 := level10.get ⟨1391,by decide⟩
def sourceMap1910 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1910 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1910_checked : acceptsGraphIso
    (source (graph core1910) (root 10) 0 2) DegreeTwoThreeSpectrum3239.graph sourceMap1910=true := by decide +kernel
theorem fusedMap1910_checked : acceptsGraphIso
    (fused (graph core1910) (root 10) 0 2) DegreeTwoThreeSpectrum3606.graph fusedMap1910=true := by decide +kernel
theorem certified1910 : Certified (graph core1910) (root 10) 0 2 :=
  of_native_maps core1910 DegreeTwoThreeSpectrum3239.graph DegreeTwoThreeSpectrum3606.graph
    sourceMap1910 fusedMap1910 sourceMap1910_checked fusedMap1910_checked
    DegreeTwoThreeFiniteComparisons.comparison1910
#print axioms sourceMap1910_checked
#print axioms fusedMap1910_checked
#print axioms certified1910
def sourceMap1910swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1910swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1910swap_checked : acceptsGraphIso
    (source (graph core1910) (root 10) 2 0) DegreeTwoThreeSpectrum3239.graph sourceMap1910swap=true := by decide +kernel
theorem fusedMap1910swap_checked : acceptsGraphIso
    (fused (graph core1910) (root 10) 2 0) DegreeTwoThreeSpectrum3606.graph fusedMap1910swap=true := by decide +kernel
theorem certified1910swap : Certified (graph core1910) (root 10) 2 0 :=
  of_native_maps core1910 DegreeTwoThreeSpectrum3239.graph DegreeTwoThreeSpectrum3606.graph
    sourceMap1910swap fusedMap1910swap sourceMap1910swap_checked fusedMap1910swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1910
#print axioms sourceMap1910swap_checked
#print axioms fusedMap1910swap_checked
#print axioms certified1910swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
