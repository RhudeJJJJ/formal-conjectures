/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1931 : Family 10 := level10.get ⟨1445,by decide⟩
def sourceMap1931 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,1,2,3,7,4,5,6] (sourceLabel 10 0 2 v)
def fusedMap1931 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1931_checked : acceptsGraphIso
    (source (graph core1931) (root 10) 0 2) DegreeTwoThreeSpectrum3623.graph sourceMap1931=true := by decide +kernel
theorem fusedMap1931_checked : acceptsGraphIso
    (fused (graph core1931) (root 10) 0 2) DegreeTwoThreeSpectrum3683.graph fusedMap1931=true := by decide +kernel
theorem certified1931 : Certified (graph core1931) (root 10) 0 2 :=
  of_native_maps core1931 DegreeTwoThreeSpectrum3623.graph DegreeTwoThreeSpectrum3683.graph
    sourceMap1931 fusedMap1931 sourceMap1931_checked fusedMap1931_checked
    DegreeTwoThreeFiniteComparisons.comparison1931
#print axioms sourceMap1931_checked
#print axioms fusedMap1931_checked
#print axioms certified1931
def sourceMap1931swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,1,2,3,4,5,6,7] (sourceLabel 10 2 0 v)
def fusedMap1931swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1931swap_checked : acceptsGraphIso
    (source (graph core1931) (root 10) 2 0) DegreeTwoThreeSpectrum3623.graph sourceMap1931swap=true := by decide +kernel
theorem fusedMap1931swap_checked : acceptsGraphIso
    (fused (graph core1931) (root 10) 2 0) DegreeTwoThreeSpectrum3683.graph fusedMap1931swap=true := by decide +kernel
theorem certified1931swap : Certified (graph core1931) (root 10) 2 0 :=
  of_native_maps core1931 DegreeTwoThreeSpectrum3623.graph DegreeTwoThreeSpectrum3683.graph
    sourceMap1931swap fusedMap1931swap sourceMap1931swap_checked fusedMap1931swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1931
#print axioms sourceMap1931swap_checked
#print axioms fusedMap1931swap_checked
#print axioms certified1931swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
