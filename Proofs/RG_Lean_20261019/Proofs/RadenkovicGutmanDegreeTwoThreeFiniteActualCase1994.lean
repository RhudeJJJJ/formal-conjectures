/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1994 : Family 10 := level10.get ⟨1603,by decide⟩
def sourceMap1994 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1994 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1994_checked : acceptsGraphIso
    (source (graph core1994) (root 10) 0 2) DegreeTwoThreeSpectrum3779.graph sourceMap1994=true := by decide +kernel
theorem fusedMap1994_checked : acceptsGraphIso
    (fused (graph core1994) (root 10) 0 2) DegreeTwoThreeSpectrum3115.graph fusedMap1994=true := by decide +kernel
theorem certified1994 : Certified (graph core1994) (root 10) 0 2 :=
  of_native_maps core1994 DegreeTwoThreeSpectrum3779.graph DegreeTwoThreeSpectrum3115.graph
    sourceMap1994 fusedMap1994 sourceMap1994_checked fusedMap1994_checked
    DegreeTwoThreeFiniteComparisons.comparison1994
#print axioms sourceMap1994_checked
#print axioms fusedMap1994_checked
#print axioms certified1994
def sourceMap1994swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1994swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1994swap_checked : acceptsGraphIso
    (source (graph core1994) (root 10) 2 0) DegreeTwoThreeSpectrum3779.graph sourceMap1994swap=true := by decide +kernel
theorem fusedMap1994swap_checked : acceptsGraphIso
    (fused (graph core1994) (root 10) 2 0) DegreeTwoThreeSpectrum3115.graph fusedMap1994swap=true := by decide +kernel
theorem certified1994swap : Certified (graph core1994) (root 10) 2 0 :=
  of_native_maps core1994 DegreeTwoThreeSpectrum3779.graph DegreeTwoThreeSpectrum3115.graph
    sourceMap1994swap fusedMap1994swap sourceMap1994swap_checked fusedMap1994swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1994
#print axioms sourceMap1994swap_checked
#print axioms fusedMap1994swap_checked
#print axioms certified1994swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
