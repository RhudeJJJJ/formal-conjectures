/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1870 : Family 10 := level10.get ⟨1303,by decide⟩
def sourceMap1870 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1870 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 0 2 v)
theorem sourceMap1870_checked : acceptsGraphIso
    (source (graph core1870) (root 10) 0 2) DegreeTwoThreeSpectrum3468.graph sourceMap1870=true := by decide +kernel
theorem fusedMap1870_checked : acceptsGraphIso
    (fused (graph core1870) (root 10) 0 2) DegreeTwoThreeSpectrum3470.graph fusedMap1870=true := by decide +kernel
theorem certified1870 : Certified (graph core1870) (root 10) 0 2 :=
  of_native_maps core1870 DegreeTwoThreeSpectrum3468.graph DegreeTwoThreeSpectrum3470.graph
    sourceMap1870 fusedMap1870 sourceMap1870_checked fusedMap1870_checked
    DegreeTwoThreeFiniteComparisons.comparison1870
#print axioms sourceMap1870_checked
#print axioms fusedMap1870_checked
#print axioms certified1870
def sourceMap1870swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1870swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,13,14,9,10,11,12] (fusedLabel 10 2 0 v)
theorem sourceMap1870swap_checked : acceptsGraphIso
    (source (graph core1870) (root 10) 2 0) DegreeTwoThreeSpectrum3468.graph sourceMap1870swap=true := by decide +kernel
theorem fusedMap1870swap_checked : acceptsGraphIso
    (fused (graph core1870) (root 10) 2 0) DegreeTwoThreeSpectrum3470.graph fusedMap1870swap=true := by decide +kernel
theorem certified1870swap : Certified (graph core1870) (root 10) 2 0 :=
  of_native_maps core1870 DegreeTwoThreeSpectrum3468.graph DegreeTwoThreeSpectrum3470.graph
    sourceMap1870swap fusedMap1870swap sourceMap1870swap_checked fusedMap1870swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1870
#print axioms sourceMap1870swap_checked
#print axioms fusedMap1870swap_checked
#print axioms certified1870swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
