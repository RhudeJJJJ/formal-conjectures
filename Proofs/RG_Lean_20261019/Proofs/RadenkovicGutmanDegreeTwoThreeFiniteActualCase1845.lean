/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1845 : Family 10 := level10.get ⟨1243,by decide⟩
def sourceMap1845 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1845 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1845_checked : acceptsGraphIso
    (source (graph core1845) (root 10) 0 2) DegreeTwoThreeSpectrum3379.graph sourceMap1845=true := by decide +kernel
theorem fusedMap1845_checked : acceptsGraphIso
    (fused (graph core1845) (root 10) 0 2) DegreeTwoThreeSpectrum3380.graph fusedMap1845=true := by decide +kernel
theorem certified1845 : Certified (graph core1845) (root 10) 0 2 :=
  of_native_maps core1845 DegreeTwoThreeSpectrum3379.graph DegreeTwoThreeSpectrum3380.graph
    sourceMap1845 fusedMap1845 sourceMap1845_checked fusedMap1845_checked
    DegreeTwoThreeFiniteComparisons.comparison1845
#print axioms sourceMap1845_checked
#print axioms fusedMap1845_checked
#print axioms certified1845
def sourceMap1845swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1845swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1845swap_checked : acceptsGraphIso
    (source (graph core1845) (root 10) 2 0) DegreeTwoThreeSpectrum3379.graph sourceMap1845swap=true := by decide +kernel
theorem fusedMap1845swap_checked : acceptsGraphIso
    (fused (graph core1845) (root 10) 2 0) DegreeTwoThreeSpectrum3380.graph fusedMap1845swap=true := by decide +kernel
theorem certified1845swap : Certified (graph core1845) (root 10) 2 0 :=
  of_native_maps core1845 DegreeTwoThreeSpectrum3379.graph DegreeTwoThreeSpectrum3380.graph
    sourceMap1845swap fusedMap1845swap sourceMap1845swap_checked fusedMap1845swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1845
#print axioms sourceMap1845swap_checked
#print axioms fusedMap1845swap_checked
#print axioms certified1845swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
