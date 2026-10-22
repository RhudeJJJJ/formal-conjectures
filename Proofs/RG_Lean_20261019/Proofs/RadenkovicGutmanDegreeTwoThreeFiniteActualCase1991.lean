/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1991 : Family 10 := level10.get ⟨1599,by decide⟩
def sourceMap1991 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1991 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1991_checked : acceptsGraphIso
    (source (graph core1991) (root 10) 0 2) DegreeTwoThreeSpectrum3776.graph sourceMap1991=true := by decide +kernel
theorem fusedMap1991_checked : acceptsGraphIso
    (fused (graph core1991) (root 10) 0 2) DegreeTwoThreeSpectrum3112.graph fusedMap1991=true := by decide +kernel
theorem certified1991 : Certified (graph core1991) (root 10) 0 2 :=
  of_native_maps core1991 DegreeTwoThreeSpectrum3776.graph DegreeTwoThreeSpectrum3112.graph
    sourceMap1991 fusedMap1991 sourceMap1991_checked fusedMap1991_checked
    DegreeTwoThreeFiniteComparisons.comparison1991
#print axioms sourceMap1991_checked
#print axioms fusedMap1991_checked
#print axioms certified1991
def sourceMap1991swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1991swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1991swap_checked : acceptsGraphIso
    (source (graph core1991) (root 10) 2 0) DegreeTwoThreeSpectrum3776.graph sourceMap1991swap=true := by decide +kernel
theorem fusedMap1991swap_checked : acceptsGraphIso
    (fused (graph core1991) (root 10) 2 0) DegreeTwoThreeSpectrum3112.graph fusedMap1991swap=true := by decide +kernel
theorem certified1991swap : Certified (graph core1991) (root 10) 2 0 :=
  of_native_maps core1991 DegreeTwoThreeSpectrum3776.graph DegreeTwoThreeSpectrum3112.graph
    sourceMap1991swap fusedMap1991swap sourceMap1991swap_checked fusedMap1991swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1991
#print axioms sourceMap1991swap_checked
#print axioms fusedMap1991swap_checked
#print axioms certified1991swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
