/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1840 : Family 10 := level10.get ⟨1225,by decide⟩
def sourceMap1840 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1840 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1840_checked : acceptsGraphIso
    (source (graph core1840) (root 10) 0 2) DegreeTwoThreeSpectrum3116.graph sourceMap1840=true := by decide +kernel
theorem fusedMap1840_checked : acceptsGraphIso
    (fused (graph core1840) (root 10) 0 2) DegreeTwoThreeSpectrum3371.graph fusedMap1840=true := by decide +kernel
theorem certified1840 : Certified (graph core1840) (root 10) 0 2 :=
  of_native_maps core1840 DegreeTwoThreeSpectrum3116.graph DegreeTwoThreeSpectrum3371.graph
    sourceMap1840 fusedMap1840 sourceMap1840_checked fusedMap1840_checked
    DegreeTwoThreeFiniteComparisons.comparison1840
#print axioms sourceMap1840_checked
#print axioms fusedMap1840_checked
#print axioms certified1840
def sourceMap1840swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1840swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1840swap_checked : acceptsGraphIso
    (source (graph core1840) (root 10) 2 0) DegreeTwoThreeSpectrum3116.graph sourceMap1840swap=true := by decide +kernel
theorem fusedMap1840swap_checked : acceptsGraphIso
    (fused (graph core1840) (root 10) 2 0) DegreeTwoThreeSpectrum3371.graph fusedMap1840swap=true := by decide +kernel
theorem certified1840swap : Certified (graph core1840) (root 10) 2 0 :=
  of_native_maps core1840 DegreeTwoThreeSpectrum3116.graph DegreeTwoThreeSpectrum3371.graph
    sourceMap1840swap fusedMap1840swap sourceMap1840swap_checked fusedMap1840swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1840
#print axioms sourceMap1840swap_checked
#print axioms fusedMap1840swap_checked
#print axioms certified1840swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
