/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1814 : Family 10 := level10.get ⟨1167,by decide⟩
def sourceMap1814 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1814 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1814_checked : acceptsGraphIso
    (source (graph core1814) (root 10) 0 2) DegreeTwoThreeSpectrum3265.graph sourceMap1814=true := by decide +kernel
theorem fusedMap1814_checked : acceptsGraphIso
    (fused (graph core1814) (root 10) 0 2) DegreeTwoThreeSpectrum3275.graph fusedMap1814=true := by decide +kernel
theorem certified1814 : Certified (graph core1814) (root 10) 0 2 :=
  of_native_maps core1814 DegreeTwoThreeSpectrum3265.graph DegreeTwoThreeSpectrum3275.graph
    sourceMap1814 fusedMap1814 sourceMap1814_checked fusedMap1814_checked
    DegreeTwoThreeFiniteComparisons.comparison1814
#print axioms sourceMap1814_checked
#print axioms fusedMap1814_checked
#print axioms certified1814
def sourceMap1814swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1814swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1814swap_checked : acceptsGraphIso
    (source (graph core1814) (root 10) 2 0) DegreeTwoThreeSpectrum3265.graph sourceMap1814swap=true := by decide +kernel
theorem fusedMap1814swap_checked : acceptsGraphIso
    (fused (graph core1814) (root 10) 2 0) DegreeTwoThreeSpectrum3275.graph fusedMap1814swap=true := by decide +kernel
theorem certified1814swap : Certified (graph core1814) (root 10) 2 0 :=
  of_native_maps core1814 DegreeTwoThreeSpectrum3265.graph DegreeTwoThreeSpectrum3275.graph
    sourceMap1814swap fusedMap1814swap sourceMap1814swap_checked fusedMap1814swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1814
#print axioms sourceMap1814swap_checked
#print axioms fusedMap1814swap_checked
#print axioms certified1814swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
