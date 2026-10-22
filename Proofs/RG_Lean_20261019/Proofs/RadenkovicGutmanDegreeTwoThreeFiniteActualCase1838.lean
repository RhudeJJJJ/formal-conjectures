/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1838 : Family 10 := level10.get ⟨1222,by decide⟩
def sourceMap1838 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1838 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1838_checked : acceptsGraphIso
    (source (graph core1838) (root 10) 0 2) DegreeTwoThreeSpectrum3355.graph sourceMap1838=true := by decide +kernel
theorem fusedMap1838_checked : acceptsGraphIso
    (fused (graph core1838) (root 10) 0 2) DegreeTwoThreeSpectrum3354.graph fusedMap1838=true := by decide +kernel
theorem certified1838 : Certified (graph core1838) (root 10) 0 2 :=
  of_native_maps core1838 DegreeTwoThreeSpectrum3355.graph DegreeTwoThreeSpectrum3354.graph
    sourceMap1838 fusedMap1838 sourceMap1838_checked fusedMap1838_checked
    DegreeTwoThreeFiniteComparisons.comparison1838
#print axioms sourceMap1838_checked
#print axioms fusedMap1838_checked
#print axioms certified1838
def sourceMap1838swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1838swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1838swap_checked : acceptsGraphIso
    (source (graph core1838) (root 10) 2 0) DegreeTwoThreeSpectrum3355.graph sourceMap1838swap=true := by decide +kernel
theorem fusedMap1838swap_checked : acceptsGraphIso
    (fused (graph core1838) (root 10) 2 0) DegreeTwoThreeSpectrum3354.graph fusedMap1838swap=true := by decide +kernel
theorem certified1838swap : Certified (graph core1838) (root 10) 2 0 :=
  of_native_maps core1838 DegreeTwoThreeSpectrum3355.graph DegreeTwoThreeSpectrum3354.graph
    sourceMap1838swap fusedMap1838swap sourceMap1838swap_checked fusedMap1838swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1838
#print axioms sourceMap1838swap_checked
#print axioms fusedMap1838swap_checked
#print axioms certified1838swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
