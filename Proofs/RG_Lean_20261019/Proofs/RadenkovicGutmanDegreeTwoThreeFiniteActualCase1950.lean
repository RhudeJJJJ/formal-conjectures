/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1950 : Family 10 := level10.get ⟨1485,by decide⟩
def sourceMap1950 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,4,5,6,7,8,9,1,2,3] (sourceLabel 10 0 2 v)
def fusedMap1950 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1950_checked : acceptsGraphIso
    (source (graph core1950) (root 10) 0 2) DegreeTwoThreeSpectrum3637.graph sourceMap1950=true := by decide +kernel
theorem fusedMap1950_checked : acceptsGraphIso
    (fused (graph core1950) (root 10) 0 2) DegreeTwoThreeSpectrum3722.graph fusedMap1950=true := by decide +kernel
theorem certified1950 : Certified (graph core1950) (root 10) 0 2 :=
  of_native_maps core1950 DegreeTwoThreeSpectrum3637.graph DegreeTwoThreeSpectrum3722.graph
    sourceMap1950 fusedMap1950 sourceMap1950_checked fusedMap1950_checked
    DegreeTwoThreeFiniteComparisons.comparison1950
#print axioms sourceMap1950_checked
#print axioms fusedMap1950_checked
#print axioms certified1950
def sourceMap1950swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,4,5,6,7,8,1,2,3,9] (sourceLabel 10 2 0 v)
def fusedMap1950swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,10,11,12,13,14,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1950swap_checked : acceptsGraphIso
    (source (graph core1950) (root 10) 2 0) DegreeTwoThreeSpectrum3637.graph sourceMap1950swap=true := by decide +kernel
theorem fusedMap1950swap_checked : acceptsGraphIso
    (fused (graph core1950) (root 10) 2 0) DegreeTwoThreeSpectrum3722.graph fusedMap1950swap=true := by decide +kernel
theorem certified1950swap : Certified (graph core1950) (root 10) 2 0 :=
  of_native_maps core1950 DegreeTwoThreeSpectrum3637.graph DegreeTwoThreeSpectrum3722.graph
    sourceMap1950swap fusedMap1950swap sourceMap1950swap_checked fusedMap1950swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1950
#print axioms sourceMap1950swap_checked
#print axioms fusedMap1950swap_checked
#print axioms certified1950swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
