/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1894 : Family 10 := level10.get ⟨1361,by decide⟩
def sourceMap1894 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1894 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1894_checked : acceptsGraphIso
    (source (graph core1894) (root 10) 0 2) DegreeTwoThreeSpectrum3552.graph sourceMap1894=true := by decide +kernel
theorem fusedMap1894_checked : acceptsGraphIso
    (fused (graph core1894) (root 10) 0 2) DegreeTwoThreeSpectrum3553.graph fusedMap1894=true := by decide +kernel
theorem certified1894 : Certified (graph core1894) (root 10) 0 2 :=
  of_native_maps core1894 DegreeTwoThreeSpectrum3552.graph DegreeTwoThreeSpectrum3553.graph
    sourceMap1894 fusedMap1894 sourceMap1894_checked fusedMap1894_checked
    DegreeTwoThreeFiniteComparisons.comparison1894
#print axioms sourceMap1894_checked
#print axioms fusedMap1894_checked
#print axioms certified1894
def sourceMap1894swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1894swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1894swap_checked : acceptsGraphIso
    (source (graph core1894) (root 10) 2 0) DegreeTwoThreeSpectrum3552.graph sourceMap1894swap=true := by decide +kernel
theorem fusedMap1894swap_checked : acceptsGraphIso
    (fused (graph core1894) (root 10) 2 0) DegreeTwoThreeSpectrum3553.graph fusedMap1894swap=true := by decide +kernel
theorem certified1894swap : Certified (graph core1894) (root 10) 2 0 :=
  of_native_maps core1894 DegreeTwoThreeSpectrum3552.graph DegreeTwoThreeSpectrum3553.graph
    sourceMap1894swap fusedMap1894swap sourceMap1894swap_checked fusedMap1894swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1894
#print axioms sourceMap1894swap_checked
#print axioms fusedMap1894swap_checked
#print axioms certified1894swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
