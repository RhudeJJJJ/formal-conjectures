/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1793 : Family 10 := level10.get ⟨1119,by decide⟩
def sourceMap1793 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1793 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1793_checked : acceptsGraphIso
    (source (graph core1793) (root 10) 0 2) DegreeTwoThreeSpectrum3194.graph sourceMap1793=true := by decide +kernel
theorem fusedMap1793_checked : acceptsGraphIso
    (fused (graph core1793) (root 10) 0 2) DegreeTwoThreeSpectrum3195.graph fusedMap1793=true := by decide +kernel
theorem certified1793 : Certified (graph core1793) (root 10) 0 2 :=
  of_native_maps core1793 DegreeTwoThreeSpectrum3194.graph DegreeTwoThreeSpectrum3195.graph
    sourceMap1793 fusedMap1793 sourceMap1793_checked fusedMap1793_checked
    DegreeTwoThreeFiniteComparisons.comparison1793
#print axioms sourceMap1793_checked
#print axioms fusedMap1793_checked
#print axioms certified1793
def sourceMap1793swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1793swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1793swap_checked : acceptsGraphIso
    (source (graph core1793) (root 10) 2 0) DegreeTwoThreeSpectrum3194.graph sourceMap1793swap=true := by decide +kernel
theorem fusedMap1793swap_checked : acceptsGraphIso
    (fused (graph core1793) (root 10) 2 0) DegreeTwoThreeSpectrum3195.graph fusedMap1793swap=true := by decide +kernel
theorem certified1793swap : Certified (graph core1793) (root 10) 2 0 :=
  of_native_maps core1793 DegreeTwoThreeSpectrum3194.graph DegreeTwoThreeSpectrum3195.graph
    sourceMap1793swap fusedMap1793swap sourceMap1793swap_checked fusedMap1793swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1793
#print axioms sourceMap1793swap_checked
#print axioms fusedMap1793swap_checked
#print axioms certified1793swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
