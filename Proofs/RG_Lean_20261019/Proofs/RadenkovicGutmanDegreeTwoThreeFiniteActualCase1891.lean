/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1891 : Family 10 := level10.get ⟨1354,by decide⟩
def sourceMap1891 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1891 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1891_checked : acceptsGraphIso
    (source (graph core1891) (root 10) 0 2) DegreeTwoThreeSpectrum3544.graph sourceMap1891=true := by decide +kernel
theorem fusedMap1891_checked : acceptsGraphIso
    (fused (graph core1891) (root 10) 0 2) DegreeTwoThreeSpectrum3545.graph fusedMap1891=true := by decide +kernel
theorem certified1891 : Certified (graph core1891) (root 10) 0 2 :=
  of_native_maps core1891 DegreeTwoThreeSpectrum3544.graph DegreeTwoThreeSpectrum3545.graph
    sourceMap1891 fusedMap1891 sourceMap1891_checked fusedMap1891_checked
    DegreeTwoThreeFiniteComparisons.comparison1891
#print axioms sourceMap1891_checked
#print axioms fusedMap1891_checked
#print axioms certified1891
def sourceMap1891swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1891swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1891swap_checked : acceptsGraphIso
    (source (graph core1891) (root 10) 2 0) DegreeTwoThreeSpectrum3544.graph sourceMap1891swap=true := by decide +kernel
theorem fusedMap1891swap_checked : acceptsGraphIso
    (fused (graph core1891) (root 10) 2 0) DegreeTwoThreeSpectrum3545.graph fusedMap1891swap=true := by decide +kernel
theorem certified1891swap : Certified (graph core1891) (root 10) 2 0 :=
  of_native_maps core1891 DegreeTwoThreeSpectrum3544.graph DegreeTwoThreeSpectrum3545.graph
    sourceMap1891swap fusedMap1891swap sourceMap1891swap_checked fusedMap1891swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1891
#print axioms sourceMap1891swap_checked
#print axioms fusedMap1891swap_checked
#print axioms certified1891swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
