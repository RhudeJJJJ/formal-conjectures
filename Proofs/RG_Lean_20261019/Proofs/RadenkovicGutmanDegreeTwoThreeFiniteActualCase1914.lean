/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1914 : Family 10 := level10.get ⟨1408,by decide⟩
def sourceMap1914 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1914 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1914_checked : acceptsGraphIso
    (source (graph core1914) (root 10) 0 2) DegreeTwoThreeSpectrum3616.graph sourceMap1914=true := by decide +kernel
theorem fusedMap1914_checked : acceptsGraphIso
    (fused (graph core1914) (root 10) 0 2) DegreeTwoThreeSpectrum3618.graph fusedMap1914=true := by decide +kernel
theorem certified1914 : Certified (graph core1914) (root 10) 0 2 :=
  of_native_maps core1914 DegreeTwoThreeSpectrum3616.graph DegreeTwoThreeSpectrum3618.graph
    sourceMap1914 fusedMap1914 sourceMap1914_checked fusedMap1914_checked
    DegreeTwoThreeFiniteComparisons.comparison1914
#print axioms sourceMap1914_checked
#print axioms fusedMap1914_checked
#print axioms certified1914
def sourceMap1914swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1914swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1914swap_checked : acceptsGraphIso
    (source (graph core1914) (root 10) 2 0) DegreeTwoThreeSpectrum3616.graph sourceMap1914swap=true := by decide +kernel
theorem fusedMap1914swap_checked : acceptsGraphIso
    (fused (graph core1914) (root 10) 2 0) DegreeTwoThreeSpectrum3618.graph fusedMap1914swap=true := by decide +kernel
theorem certified1914swap : Certified (graph core1914) (root 10) 2 0 :=
  of_native_maps core1914 DegreeTwoThreeSpectrum3616.graph DegreeTwoThreeSpectrum3618.graph
    sourceMap1914swap fusedMap1914swap sourceMap1914swap_checked fusedMap1914swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1914
#print axioms sourceMap1914swap_checked
#print axioms fusedMap1914swap_checked
#print axioms certified1914swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
