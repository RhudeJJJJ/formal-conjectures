/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1918 : Family 10 := level10.get ⟨1414,by decide⟩
def sourceMap1918 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1918 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1918_checked : acceptsGraphIso
    (source (graph core1918) (root 10) 0 2) DegreeTwoThreeSpectrum3630.graph sourceMap1918=true := by decide +kernel
theorem fusedMap1918_checked : acceptsGraphIso
    (fused (graph core1918) (root 10) 0 2) DegreeTwoThreeSpectrum3634.graph fusedMap1918=true := by decide +kernel
theorem certified1918 : Certified (graph core1918) (root 10) 0 2 :=
  of_native_maps core1918 DegreeTwoThreeSpectrum3630.graph DegreeTwoThreeSpectrum3634.graph
    sourceMap1918 fusedMap1918 sourceMap1918_checked fusedMap1918_checked
    DegreeTwoThreeFiniteComparisons.comparison1918
#print axioms sourceMap1918_checked
#print axioms fusedMap1918_checked
#print axioms certified1918
def sourceMap1918swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1918swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1918swap_checked : acceptsGraphIso
    (source (graph core1918) (root 10) 2 0) DegreeTwoThreeSpectrum3630.graph sourceMap1918swap=true := by decide +kernel
theorem fusedMap1918swap_checked : acceptsGraphIso
    (fused (graph core1918) (root 10) 2 0) DegreeTwoThreeSpectrum3634.graph fusedMap1918swap=true := by decide +kernel
theorem certified1918swap : Certified (graph core1918) (root 10) 2 0 :=
  of_native_maps core1918 DegreeTwoThreeSpectrum3630.graph DegreeTwoThreeSpectrum3634.graph
    sourceMap1918swap fusedMap1918swap sourceMap1918swap_checked fusedMap1918swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1918
#print axioms sourceMap1918swap_checked
#print axioms fusedMap1918swap_checked
#print axioms certified1918swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
