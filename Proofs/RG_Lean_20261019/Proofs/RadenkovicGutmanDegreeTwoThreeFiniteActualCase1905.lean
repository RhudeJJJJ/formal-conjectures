/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1905 : Family 10 := level10.get ⟨1380,by decide⟩
def sourceMap1905 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1905 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1905_checked : acceptsGraphIso
    (source (graph core1905) (root 10) 0 2) DegreeTwoThreeSpectrum3533.graph sourceMap1905=true := by decide +kernel
theorem fusedMap1905_checked : acceptsGraphIso
    (fused (graph core1905) (root 10) 0 2) DegreeTwoThreeSpectrum3585.graph fusedMap1905=true := by decide +kernel
theorem certified1905 : Certified (graph core1905) (root 10) 0 2 :=
  of_native_maps core1905 DegreeTwoThreeSpectrum3533.graph DegreeTwoThreeSpectrum3585.graph
    sourceMap1905 fusedMap1905 sourceMap1905_checked fusedMap1905_checked
    DegreeTwoThreeFiniteComparisons.comparison1905
#print axioms sourceMap1905_checked
#print axioms fusedMap1905_checked
#print axioms certified1905
def sourceMap1905swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1905swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1905swap_checked : acceptsGraphIso
    (source (graph core1905) (root 10) 2 0) DegreeTwoThreeSpectrum3533.graph sourceMap1905swap=true := by decide +kernel
theorem fusedMap1905swap_checked : acceptsGraphIso
    (fused (graph core1905) (root 10) 2 0) DegreeTwoThreeSpectrum3585.graph fusedMap1905swap=true := by decide +kernel
theorem certified1905swap : Certified (graph core1905) (root 10) 2 0 :=
  of_native_maps core1905 DegreeTwoThreeSpectrum3533.graph DegreeTwoThreeSpectrum3585.graph
    sourceMap1905swap fusedMap1905swap sourceMap1905swap_checked fusedMap1905swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1905
#print axioms sourceMap1905swap_checked
#print axioms fusedMap1905swap_checked
#print axioms certified1905swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
