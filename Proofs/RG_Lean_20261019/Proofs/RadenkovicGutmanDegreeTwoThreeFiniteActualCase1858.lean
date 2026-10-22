/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1858 : Family 10 := level10.get ⟨1277,by decide⟩
def sourceMap1858 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1858 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1858_checked : acceptsGraphIso
    (source (graph core1858) (root 10) 0 2) DegreeTwoThreeSpectrum3430.graph sourceMap1858=true := by decide +kernel
theorem fusedMap1858_checked : acceptsGraphIso
    (fused (graph core1858) (root 10) 0 2) DegreeTwoThreeSpectrum3431.graph fusedMap1858=true := by decide +kernel
theorem certified1858 : Certified (graph core1858) (root 10) 0 2 :=
  of_native_maps core1858 DegreeTwoThreeSpectrum3430.graph DegreeTwoThreeSpectrum3431.graph
    sourceMap1858 fusedMap1858 sourceMap1858_checked fusedMap1858_checked
    DegreeTwoThreeFiniteComparisons.comparison1858
#print axioms sourceMap1858_checked
#print axioms fusedMap1858_checked
#print axioms certified1858
def sourceMap1858swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1858swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1858swap_checked : acceptsGraphIso
    (source (graph core1858) (root 10) 2 0) DegreeTwoThreeSpectrum3430.graph sourceMap1858swap=true := by decide +kernel
theorem fusedMap1858swap_checked : acceptsGraphIso
    (fused (graph core1858) (root 10) 2 0) DegreeTwoThreeSpectrum3431.graph fusedMap1858swap=true := by decide +kernel
theorem certified1858swap : Certified (graph core1858) (root 10) 2 0 :=
  of_native_maps core1858 DegreeTwoThreeSpectrum3430.graph DegreeTwoThreeSpectrum3431.graph
    sourceMap1858swap fusedMap1858swap sourceMap1858swap_checked fusedMap1858swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1858
#print axioms sourceMap1858swap_checked
#print axioms fusedMap1858swap_checked
#print axioms certified1858swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
