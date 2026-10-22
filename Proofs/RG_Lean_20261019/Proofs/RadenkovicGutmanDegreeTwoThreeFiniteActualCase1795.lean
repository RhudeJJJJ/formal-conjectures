/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1795 : Family 10 := level10.get ⟨1122,by decide⟩
def sourceMap1795 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1795 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1795_checked : acceptsGraphIso
    (source (graph core1795) (root 10) 0 2) DegreeTwoThreeSpectrum3199.graph sourceMap1795=true := by decide +kernel
theorem fusedMap1795_checked : acceptsGraphIso
    (fused (graph core1795) (root 10) 0 2) DegreeTwoThreeSpectrum3203.graph fusedMap1795=true := by decide +kernel
theorem certified1795 : Certified (graph core1795) (root 10) 0 2 :=
  of_native_maps core1795 DegreeTwoThreeSpectrum3199.graph DegreeTwoThreeSpectrum3203.graph
    sourceMap1795 fusedMap1795 sourceMap1795_checked fusedMap1795_checked
    DegreeTwoThreeFiniteComparisons.comparison1795
#print axioms sourceMap1795_checked
#print axioms fusedMap1795_checked
#print axioms certified1795
def sourceMap1795swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1795swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1795swap_checked : acceptsGraphIso
    (source (graph core1795) (root 10) 2 0) DegreeTwoThreeSpectrum3199.graph sourceMap1795swap=true := by decide +kernel
theorem fusedMap1795swap_checked : acceptsGraphIso
    (fused (graph core1795) (root 10) 2 0) DegreeTwoThreeSpectrum3203.graph fusedMap1795swap=true := by decide +kernel
theorem certified1795swap : Certified (graph core1795) (root 10) 2 0 :=
  of_native_maps core1795 DegreeTwoThreeSpectrum3199.graph DegreeTwoThreeSpectrum3203.graph
    sourceMap1795swap fusedMap1795swap sourceMap1795swap_checked fusedMap1795swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1795
#print axioms sourceMap1795swap_checked
#print axioms fusedMap1795swap_checked
#print axioms certified1795swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
