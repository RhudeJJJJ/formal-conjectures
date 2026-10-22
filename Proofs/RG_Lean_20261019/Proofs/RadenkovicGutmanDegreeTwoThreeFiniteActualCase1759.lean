/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1759 : Family 10 := level10.get ⟨1028,by decide⟩
def sourceMap1759 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1759 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1759_checked : acceptsGraphIso
    (source (graph core1759) (root 10) 0 2) DegreeTwoThreeSpectrum3053.graph sourceMap1759=true := by decide +kernel
theorem fusedMap1759_checked : acceptsGraphIso
    (fused (graph core1759) (root 10) 0 2) DegreeTwoThreeSpectrum3057.graph fusedMap1759=true := by decide +kernel
theorem certified1759 : Certified (graph core1759) (root 10) 0 2 :=
  of_native_maps core1759 DegreeTwoThreeSpectrum3053.graph DegreeTwoThreeSpectrum3057.graph
    sourceMap1759 fusedMap1759 sourceMap1759_checked fusedMap1759_checked
    DegreeTwoThreeFiniteComparisons.comparison1759
#print axioms sourceMap1759_checked
#print axioms fusedMap1759_checked
#print axioms certified1759
def sourceMap1759swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1759swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1759swap_checked : acceptsGraphIso
    (source (graph core1759) (root 10) 2 0) DegreeTwoThreeSpectrum3053.graph sourceMap1759swap=true := by decide +kernel
theorem fusedMap1759swap_checked : acceptsGraphIso
    (fused (graph core1759) (root 10) 2 0) DegreeTwoThreeSpectrum3057.graph fusedMap1759swap=true := by decide +kernel
theorem certified1759swap : Certified (graph core1759) (root 10) 2 0 :=
  of_native_maps core1759 DegreeTwoThreeSpectrum3053.graph DegreeTwoThreeSpectrum3057.graph
    sourceMap1759swap fusedMap1759swap sourceMap1759swap_checked fusedMap1759swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1759
#print axioms sourceMap1759swap_checked
#print axioms fusedMap1759swap_checked
#print axioms certified1759swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
