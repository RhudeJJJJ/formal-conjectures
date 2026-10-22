/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1968 : Family 10 := level10.get ⟨1548,by decide⟩
def sourceMap1968 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1968 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1968_checked : acceptsGraphIso
    (source (graph core1968) (root 10) 0 2) DegreeTwoThreeSpectrum3751.graph sourceMap1968=true := by decide +kernel
theorem fusedMap1968_checked : acceptsGraphIso
    (fused (graph core1968) (root 10) 0 2) DegreeTwoThreeSpectrum3026.graph fusedMap1968=true := by decide +kernel
theorem certified1968 : Certified (graph core1968) (root 10) 0 2 :=
  of_native_maps core1968 DegreeTwoThreeSpectrum3751.graph DegreeTwoThreeSpectrum3026.graph
    sourceMap1968 fusedMap1968 sourceMap1968_checked fusedMap1968_checked
    DegreeTwoThreeFiniteComparisons.comparison1968
#print axioms sourceMap1968_checked
#print axioms fusedMap1968_checked
#print axioms certified1968
def sourceMap1968swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1968swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1968swap_checked : acceptsGraphIso
    (source (graph core1968) (root 10) 2 0) DegreeTwoThreeSpectrum3751.graph sourceMap1968swap=true := by decide +kernel
theorem fusedMap1968swap_checked : acceptsGraphIso
    (fused (graph core1968) (root 10) 2 0) DegreeTwoThreeSpectrum3026.graph fusedMap1968swap=true := by decide +kernel
theorem certified1968swap : Certified (graph core1968) (root 10) 2 0 :=
  of_native_maps core1968 DegreeTwoThreeSpectrum3751.graph DegreeTwoThreeSpectrum3026.graph
    sourceMap1968swap fusedMap1968swap sourceMap1968swap_checked fusedMap1968swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1968
#print axioms sourceMap1968swap_checked
#print axioms fusedMap1968swap_checked
#print axioms certified1968swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
