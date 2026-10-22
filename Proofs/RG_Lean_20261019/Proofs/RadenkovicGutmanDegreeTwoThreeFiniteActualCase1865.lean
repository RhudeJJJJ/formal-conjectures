/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1865 : Family 10 := level10.get ⟨1289,by decide⟩
def sourceMap1865 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,8,5,6,7] (sourceLabel 10 0 2 v)
def fusedMap1865 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 0 2 v)
theorem sourceMap1865_checked : acceptsGraphIso
    (source (graph core1865) (root 10) 0 2) DegreeTwoThreeSpectrum3291.graph sourceMap1865=true := by decide +kernel
theorem fusedMap1865_checked : acceptsGraphIso
    (fused (graph core1865) (root 10) 0 2) DegreeTwoThreeSpectrum3455.graph fusedMap1865=true := by decide +kernel
theorem certified1865 : Certified (graph core1865) (root 10) 0 2 :=
  of_native_maps core1865 DegreeTwoThreeSpectrum3291.graph DegreeTwoThreeSpectrum3455.graph
    sourceMap1865 fusedMap1865 sourceMap1865_checked fusedMap1865_checked
    DegreeTwoThreeFiniteComparisons.comparison1865
#print axioms sourceMap1865_checked
#print axioms fusedMap1865_checked
#print axioms certified1865
def sourceMap1865swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,9,10,11,12,13,14,1,2,3,4,5,6,7,8] (sourceLabel 10 2 0 v)
def fusedMap1865swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,11,12,13,14,7,8,9,10] (fusedLabel 10 2 0 v)
theorem sourceMap1865swap_checked : acceptsGraphIso
    (source (graph core1865) (root 10) 2 0) DegreeTwoThreeSpectrum3291.graph sourceMap1865swap=true := by decide +kernel
theorem fusedMap1865swap_checked : acceptsGraphIso
    (fused (graph core1865) (root 10) 2 0) DegreeTwoThreeSpectrum3455.graph fusedMap1865swap=true := by decide +kernel
theorem certified1865swap : Certified (graph core1865) (root 10) 2 0 :=
  of_native_maps core1865 DegreeTwoThreeSpectrum3291.graph DegreeTwoThreeSpectrum3455.graph
    sourceMap1865swap fusedMap1865swap sourceMap1865swap_checked fusedMap1865swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1865
#print axioms sourceMap1865swap_checked
#print axioms fusedMap1865swap_checked
#print axioms certified1865swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
