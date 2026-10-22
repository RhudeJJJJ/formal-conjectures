/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1823 : Family 10 := level10.get ⟨1192,by decide⟩
def sourceMap1823 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1823 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1823_checked : acceptsGraphIso
    (source (graph core1823) (root 10) 0 2) DegreeTwoThreeSpectrum3309.graph sourceMap1823=true := by decide +kernel
theorem fusedMap1823_checked : acceptsGraphIso
    (fused (graph core1823) (root 10) 0 2) DegreeTwoThreeSpectrum3311.graph fusedMap1823=true := by decide +kernel
theorem certified1823 : Certified (graph core1823) (root 10) 0 2 :=
  of_native_maps core1823 DegreeTwoThreeSpectrum3309.graph DegreeTwoThreeSpectrum3311.graph
    sourceMap1823 fusedMap1823 sourceMap1823_checked fusedMap1823_checked
    DegreeTwoThreeFiniteComparisons.comparison1823
#print axioms sourceMap1823_checked
#print axioms fusedMap1823_checked
#print axioms certified1823
def sourceMap1823swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1823swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1823swap_checked : acceptsGraphIso
    (source (graph core1823) (root 10) 2 0) DegreeTwoThreeSpectrum3309.graph sourceMap1823swap=true := by decide +kernel
theorem fusedMap1823swap_checked : acceptsGraphIso
    (fused (graph core1823) (root 10) 2 0) DegreeTwoThreeSpectrum3311.graph fusedMap1823swap=true := by decide +kernel
theorem certified1823swap : Certified (graph core1823) (root 10) 2 0 :=
  of_native_maps core1823 DegreeTwoThreeSpectrum3309.graph DegreeTwoThreeSpectrum3311.graph
    sourceMap1823swap fusedMap1823swap sourceMap1823swap_checked fusedMap1823swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1823
#print axioms sourceMap1823swap_checked
#print axioms fusedMap1823swap_checked
#print axioms certified1823swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
