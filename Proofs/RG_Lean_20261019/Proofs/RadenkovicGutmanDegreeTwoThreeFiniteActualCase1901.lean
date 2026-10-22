/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1901 : Family 10 := level10.get ⟨1374,by decide⟩
def sourceMap1901 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1901 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1901_checked : acceptsGraphIso
    (source (graph core1901) (root 10) 0 2) DegreeTwoThreeSpectrum3570.graph sourceMap1901=true := by decide +kernel
theorem fusedMap1901_checked : acceptsGraphIso
    (fused (graph core1901) (root 10) 0 2) DegreeTwoThreeSpectrum3574.graph fusedMap1901=true := by decide +kernel
theorem certified1901 : Certified (graph core1901) (root 10) 0 2 :=
  of_native_maps core1901 DegreeTwoThreeSpectrum3570.graph DegreeTwoThreeSpectrum3574.graph
    sourceMap1901 fusedMap1901 sourceMap1901_checked fusedMap1901_checked
    DegreeTwoThreeFiniteComparisons.comparison1901
#print axioms sourceMap1901_checked
#print axioms fusedMap1901_checked
#print axioms certified1901
def sourceMap1901swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1901swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1901swap_checked : acceptsGraphIso
    (source (graph core1901) (root 10) 2 0) DegreeTwoThreeSpectrum3570.graph sourceMap1901swap=true := by decide +kernel
theorem fusedMap1901swap_checked : acceptsGraphIso
    (fused (graph core1901) (root 10) 2 0) DegreeTwoThreeSpectrum3574.graph fusedMap1901swap=true := by decide +kernel
theorem certified1901swap : Certified (graph core1901) (root 10) 2 0 :=
  of_native_maps core1901 DegreeTwoThreeSpectrum3570.graph DegreeTwoThreeSpectrum3574.graph
    sourceMap1901swap fusedMap1901swap sourceMap1901swap_checked fusedMap1901swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1901
#print axioms sourceMap1901swap_checked
#print axioms fusedMap1901swap_checked
#print axioms certified1901swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
