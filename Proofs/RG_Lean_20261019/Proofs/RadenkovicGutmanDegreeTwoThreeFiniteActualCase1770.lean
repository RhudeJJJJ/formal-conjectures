/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1770 : Family 10 := level10.get ⟨1059,by decide⟩
def sourceMap1770 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1770 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1770_checked : acceptsGraphIso
    (source (graph core1770) (root 10) 0 2) DegreeTwoThreeSpectrum3103.graph sourceMap1770=true := by decide +kernel
theorem fusedMap1770_checked : acceptsGraphIso
    (fused (graph core1770) (root 10) 0 2) DegreeTwoThreeSpectrum3105.graph fusedMap1770=true := by decide +kernel
theorem certified1770 : Certified (graph core1770) (root 10) 0 2 :=
  of_native_maps core1770 DegreeTwoThreeSpectrum3103.graph DegreeTwoThreeSpectrum3105.graph
    sourceMap1770 fusedMap1770 sourceMap1770_checked fusedMap1770_checked
    DegreeTwoThreeFiniteComparisons.comparison1770
#print axioms sourceMap1770_checked
#print axioms fusedMap1770_checked
#print axioms certified1770
def sourceMap1770swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1770swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1770swap_checked : acceptsGraphIso
    (source (graph core1770) (root 10) 2 0) DegreeTwoThreeSpectrum3103.graph sourceMap1770swap=true := by decide +kernel
theorem fusedMap1770swap_checked : acceptsGraphIso
    (fused (graph core1770) (root 10) 2 0) DegreeTwoThreeSpectrum3105.graph fusedMap1770swap=true := by decide +kernel
theorem certified1770swap : Certified (graph core1770) (root 10) 2 0 :=
  of_native_maps core1770 DegreeTwoThreeSpectrum3103.graph DegreeTwoThreeSpectrum3105.graph
    sourceMap1770swap fusedMap1770swap sourceMap1770swap_checked fusedMap1770swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1770
#print axioms sourceMap1770swap_checked
#print axioms fusedMap1770swap_checked
#print axioms certified1770swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
