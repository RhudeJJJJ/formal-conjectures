/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1848 : Family 10 := level10.get ⟨1251,by decide⟩
def sourceMap1848 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1848 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1848_checked : acceptsGraphIso
    (source (graph core1848) (root 10) 0 2) DegreeTwoThreeSpectrum3391.graph sourceMap1848=true := by decide +kernel
theorem fusedMap1848_checked : acceptsGraphIso
    (fused (graph core1848) (root 10) 0 2) DegreeTwoThreeSpectrum3392.graph fusedMap1848=true := by decide +kernel
theorem certified1848 : Certified (graph core1848) (root 10) 0 2 :=
  of_native_maps core1848 DegreeTwoThreeSpectrum3391.graph DegreeTwoThreeSpectrum3392.graph
    sourceMap1848 fusedMap1848 sourceMap1848_checked fusedMap1848_checked
    DegreeTwoThreeFiniteComparisons.comparison1848
#print axioms sourceMap1848_checked
#print axioms fusedMap1848_checked
#print axioms certified1848
def sourceMap1848swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1848swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1848swap_checked : acceptsGraphIso
    (source (graph core1848) (root 10) 2 0) DegreeTwoThreeSpectrum3391.graph sourceMap1848swap=true := by decide +kernel
theorem fusedMap1848swap_checked : acceptsGraphIso
    (fused (graph core1848) (root 10) 2 0) DegreeTwoThreeSpectrum3392.graph fusedMap1848swap=true := by decide +kernel
theorem certified1848swap : Certified (graph core1848) (root 10) 2 0 :=
  of_native_maps core1848 DegreeTwoThreeSpectrum3391.graph DegreeTwoThreeSpectrum3392.graph
    sourceMap1848swap fusedMap1848swap sourceMap1848swap_checked fusedMap1848swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1848
#print axioms sourceMap1848swap_checked
#print axioms fusedMap1848swap_checked
#print axioms certified1848swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
