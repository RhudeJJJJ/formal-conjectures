/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1593 : Family 10 := level10.get ⟨584,by decide⟩
def sourceMap1593 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1593 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1593_checked : acceptsGraphIso
    (source (graph core1593) (root 10) 0 2) DegreeTwoThreeSpectrum3227.graph sourceMap1593=true := by decide +kernel
theorem fusedMap1593_checked : acceptsGraphIso
    (fused (graph core1593) (root 10) 0 2) DegreeTwoThreeSpectrum2524.graph fusedMap1593=true := by decide +kernel
theorem certified1593 : Certified (graph core1593) (root 10) 0 2 :=
  of_native_maps core1593 DegreeTwoThreeSpectrum3227.graph DegreeTwoThreeSpectrum2524.graph
    sourceMap1593 fusedMap1593 sourceMap1593_checked fusedMap1593_checked
    DegreeTwoThreeFiniteComparisons.comparison1593
#print axioms sourceMap1593_checked
#print axioms fusedMap1593_checked
#print axioms certified1593
def sourceMap1593swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1593swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1593swap_checked : acceptsGraphIso
    (source (graph core1593) (root 10) 2 0) DegreeTwoThreeSpectrum3227.graph sourceMap1593swap=true := by decide +kernel
theorem fusedMap1593swap_checked : acceptsGraphIso
    (fused (graph core1593) (root 10) 2 0) DegreeTwoThreeSpectrum2524.graph fusedMap1593swap=true := by decide +kernel
theorem certified1593swap : Certified (graph core1593) (root 10) 2 0 :=
  of_native_maps core1593 DegreeTwoThreeSpectrum3227.graph DegreeTwoThreeSpectrum2524.graph
    sourceMap1593swap fusedMap1593swap sourceMap1593swap_checked fusedMap1593swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1593
#print axioms sourceMap1593swap_checked
#print axioms fusedMap1593swap_checked
#print axioms certified1593swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
