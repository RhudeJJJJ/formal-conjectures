/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons34
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1741 : Family 10 := level10.get ⟨977,by decide⟩
def sourceMap1741 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,9,6,7,8] (sourceLabel 10 0 2 v)
def fusedMap1741 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (fusedLabel 10 0 2 v)
theorem sourceMap1741_checked : acceptsGraphIso
    (source (graph core1741) (root 10) 0 2) DegreeTwoThreeSpectrum2772.graph sourceMap1741=true := by decide +kernel
theorem fusedMap1741_checked : acceptsGraphIso
    (fused (graph core1741) (root 10) 0 2) DegreeTwoThreeSpectrum2771.graph fusedMap1741=true := by decide +kernel
theorem certified1741 : Certified (graph core1741) (root 10) 0 2 :=
  of_native_maps core1741 DegreeTwoThreeSpectrum2772.graph DegreeTwoThreeSpectrum2771.graph
    sourceMap1741 fusedMap1741 sourceMap1741_checked fusedMap1741_checked
    DegreeTwoThreeFiniteComparisons.comparison1741
#print axioms sourceMap1741_checked
#print axioms fusedMap1741_checked
#print axioms certified1741
def sourceMap1741swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (sourceLabel 10 2 0 v)
def fusedMap1741swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,10,11,12,13,14,1,2,3,4,5,6,7,8,9] (fusedLabel 10 2 0 v)
theorem sourceMap1741swap_checked : acceptsGraphIso
    (source (graph core1741) (root 10) 2 0) DegreeTwoThreeSpectrum2772.graph sourceMap1741swap=true := by decide +kernel
theorem fusedMap1741swap_checked : acceptsGraphIso
    (fused (graph core1741) (root 10) 2 0) DegreeTwoThreeSpectrum2771.graph fusedMap1741swap=true := by decide +kernel
theorem certified1741swap : Certified (graph core1741) (root 10) 2 0 :=
  of_native_maps core1741 DegreeTwoThreeSpectrum2772.graph DegreeTwoThreeSpectrum2771.graph
    sourceMap1741swap fusedMap1741swap sourceMap1741swap_checked fusedMap1741swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1741
#print axioms sourceMap1741swap_checked
#print axioms fusedMap1741swap_checked
#print axioms certified1741swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
