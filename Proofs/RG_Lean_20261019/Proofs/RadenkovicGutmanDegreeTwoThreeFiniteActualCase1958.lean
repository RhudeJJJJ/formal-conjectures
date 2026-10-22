/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1958 : Family 10 := level10.get ⟨1525,by decide⟩
def sourceMap1958 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1958 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1958_checked : acceptsGraphIso
    (source (graph core1958) (root 10) 0 2) DegreeTwoThreeSpectrum3735.graph sourceMap1958=true := by decide +kernel
theorem fusedMap1958_checked : acceptsGraphIso
    (fused (graph core1958) (root 10) 0 2) DegreeTwoThreeSpectrum2997.graph fusedMap1958=true := by decide +kernel
theorem certified1958 : Certified (graph core1958) (root 10) 0 2 :=
  of_native_maps core1958 DegreeTwoThreeSpectrum3735.graph DegreeTwoThreeSpectrum2997.graph
    sourceMap1958 fusedMap1958 sourceMap1958_checked fusedMap1958_checked
    DegreeTwoThreeFiniteComparisons.comparison1958
#print axioms sourceMap1958_checked
#print axioms fusedMap1958_checked
#print axioms certified1958
def sourceMap1958swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1958swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1958swap_checked : acceptsGraphIso
    (source (graph core1958) (root 10) 2 0) DegreeTwoThreeSpectrum3735.graph sourceMap1958swap=true := by decide +kernel
theorem fusedMap1958swap_checked : acceptsGraphIso
    (fused (graph core1958) (root 10) 2 0) DegreeTwoThreeSpectrum2997.graph fusedMap1958swap=true := by decide +kernel
theorem certified1958swap : Certified (graph core1958) (root 10) 2 0 :=
  of_native_maps core1958 DegreeTwoThreeSpectrum3735.graph DegreeTwoThreeSpectrum2997.graph
    sourceMap1958swap fusedMap1958swap sourceMap1958swap_checked fusedMap1958swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1958
#print axioms sourceMap1958swap_checked
#print axioms fusedMap1958swap_checked
#print axioms certified1958swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
