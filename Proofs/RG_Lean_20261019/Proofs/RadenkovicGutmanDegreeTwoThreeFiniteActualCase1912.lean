/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1912 : Family 10 := level10.get ⟨1394,by decide⟩
def sourceMap1912 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1912 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1912_checked : acceptsGraphIso
    (source (graph core1912) (root 10) 0 2) DegreeTwoThreeSpectrum3489.graph sourceMap1912=true := by decide +kernel
theorem fusedMap1912_checked : acceptsGraphIso
    (fused (graph core1912) (root 10) 0 2) DegreeTwoThreeSpectrum3608.graph fusedMap1912=true := by decide +kernel
theorem certified1912 : Certified (graph core1912) (root 10) 0 2 :=
  of_native_maps core1912 DegreeTwoThreeSpectrum3489.graph DegreeTwoThreeSpectrum3608.graph
    sourceMap1912 fusedMap1912 sourceMap1912_checked fusedMap1912_checked
    DegreeTwoThreeFiniteComparisons.comparison1912
#print axioms sourceMap1912_checked
#print axioms fusedMap1912_checked
#print axioms certified1912
def sourceMap1912swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1912swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1912swap_checked : acceptsGraphIso
    (source (graph core1912) (root 10) 2 0) DegreeTwoThreeSpectrum3489.graph sourceMap1912swap=true := by decide +kernel
theorem fusedMap1912swap_checked : acceptsGraphIso
    (fused (graph core1912) (root 10) 2 0) DegreeTwoThreeSpectrum3608.graph fusedMap1912swap=true := by decide +kernel
theorem certified1912swap : Certified (graph core1912) (root 10) 2 0 :=
  of_native_maps core1912 DegreeTwoThreeSpectrum3489.graph DegreeTwoThreeSpectrum3608.graph
    sourceMap1912swap fusedMap1912swap sourceMap1912swap_checked fusedMap1912swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1912
#print axioms sourceMap1912swap_checked
#print axioms fusedMap1912swap_checked
#print axioms certified1912swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
