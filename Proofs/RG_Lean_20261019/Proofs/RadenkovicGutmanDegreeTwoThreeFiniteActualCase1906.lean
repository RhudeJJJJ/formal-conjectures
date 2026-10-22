/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1906 : Family 10 := level10.get ⟨1382,by decide⟩
def sourceMap1906 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,14,7,8,9] (sourceLabel 10 0 2 v)
def fusedMap1906 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1906_checked : acceptsGraphIso
    (source (graph core1906) (root 10) 0 2) DegreeTwoThreeSpectrum3578.graph sourceMap1906=true := by decide +kernel
theorem fusedMap1906_checked : acceptsGraphIso
    (fused (graph core1906) (root 10) 0 2) DegreeTwoThreeSpectrum3587.graph fusedMap1906=true := by decide +kernel
theorem certified1906 : Certified (graph core1906) (root 10) 0 2 :=
  of_native_maps core1906 DegreeTwoThreeSpectrum3578.graph DegreeTwoThreeSpectrum3587.graph
    sourceMap1906 fusedMap1906 sourceMap1906_checked fusedMap1906_checked
    DegreeTwoThreeFiniteComparisons.comparison1906
#print axioms sourceMap1906_checked
#print axioms fusedMap1906_checked
#print axioms certified1906
def sourceMap1906swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,13,7,8,9,14] (sourceLabel 10 2 0 v)
def fusedMap1906swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1906swap_checked : acceptsGraphIso
    (source (graph core1906) (root 10) 2 0) DegreeTwoThreeSpectrum3578.graph sourceMap1906swap=true := by decide +kernel
theorem fusedMap1906swap_checked : acceptsGraphIso
    (fused (graph core1906) (root 10) 2 0) DegreeTwoThreeSpectrum3587.graph fusedMap1906swap=true := by decide +kernel
theorem certified1906swap : Certified (graph core1906) (root 10) 2 0 :=
  of_native_maps core1906 DegreeTwoThreeSpectrum3578.graph DegreeTwoThreeSpectrum3587.graph
    sourceMap1906swap fusedMap1906swap sourceMap1906swap_checked fusedMap1906swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1906
#print axioms sourceMap1906swap_checked
#print axioms fusedMap1906swap_checked
#print axioms certified1906swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
