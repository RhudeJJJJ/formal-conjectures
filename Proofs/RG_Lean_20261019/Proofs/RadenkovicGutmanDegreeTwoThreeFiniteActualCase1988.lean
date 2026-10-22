/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1988 : Family 10 := level10.get ⟨1591,by decide⟩
def sourceMap1988 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1988 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1988_checked : acceptsGraphIso
    (source (graph core1988) (root 10) 0 2) DegreeTwoThreeSpectrum3772.graph sourceMap1988=true := by decide +kernel
theorem fusedMap1988_checked : acceptsGraphIso
    (fused (graph core1988) (root 10) 0 2) DegreeTwoThreeSpectrum3094.graph fusedMap1988=true := by decide +kernel
theorem certified1988 : Certified (graph core1988) (root 10) 0 2 :=
  of_native_maps core1988 DegreeTwoThreeSpectrum3772.graph DegreeTwoThreeSpectrum3094.graph
    sourceMap1988 fusedMap1988 sourceMap1988_checked fusedMap1988_checked
    DegreeTwoThreeFiniteComparisons.comparison1988
#print axioms sourceMap1988_checked
#print axioms fusedMap1988_checked
#print axioms certified1988
def sourceMap1988swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1988swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1988swap_checked : acceptsGraphIso
    (source (graph core1988) (root 10) 2 0) DegreeTwoThreeSpectrum3772.graph sourceMap1988swap=true := by decide +kernel
theorem fusedMap1988swap_checked : acceptsGraphIso
    (fused (graph core1988) (root 10) 2 0) DegreeTwoThreeSpectrum3094.graph fusedMap1988swap=true := by decide +kernel
theorem certified1988swap : Certified (graph core1988) (root 10) 2 0 :=
  of_native_maps core1988 DegreeTwoThreeSpectrum3772.graph DegreeTwoThreeSpectrum3094.graph
    sourceMap1988swap fusedMap1988swap sourceMap1988swap_checked fusedMap1988swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1988
#print axioms sourceMap1988swap_checked
#print axioms fusedMap1988swap_checked
#print axioms certified1988swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
