/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1773 : Family 10 := level10.get ⟨1068,by decide⟩
def sourceMap1773 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1773 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1773_checked : acceptsGraphIso
    (source (graph core1773) (root 10) 0 2) DegreeTwoThreeSpectrum3120.graph sourceMap1773=true := by decide +kernel
theorem fusedMap1773_checked : acceptsGraphIso
    (fused (graph core1773) (root 10) 0 2) DegreeTwoThreeSpectrum3121.graph fusedMap1773=true := by decide +kernel
theorem certified1773 : Certified (graph core1773) (root 10) 0 2 :=
  of_native_maps core1773 DegreeTwoThreeSpectrum3120.graph DegreeTwoThreeSpectrum3121.graph
    sourceMap1773 fusedMap1773 sourceMap1773_checked fusedMap1773_checked
    DegreeTwoThreeFiniteComparisons.comparison1773
#print axioms sourceMap1773_checked
#print axioms fusedMap1773_checked
#print axioms certified1773
def sourceMap1773swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1773swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1773swap_checked : acceptsGraphIso
    (source (graph core1773) (root 10) 2 0) DegreeTwoThreeSpectrum3120.graph sourceMap1773swap=true := by decide +kernel
theorem fusedMap1773swap_checked : acceptsGraphIso
    (fused (graph core1773) (root 10) 2 0) DegreeTwoThreeSpectrum3121.graph fusedMap1773swap=true := by decide +kernel
theorem certified1773swap : Certified (graph core1773) (root 10) 2 0 :=
  of_native_maps core1773 DegreeTwoThreeSpectrum3120.graph DegreeTwoThreeSpectrum3121.graph
    sourceMap1773swap fusedMap1773swap sourceMap1773swap_checked fusedMap1773swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1773
#print axioms sourceMap1773swap_checked
#print axioms fusedMap1773swap_checked
#print axioms certified1773swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
