/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1792 : Family 10 := level10.get ⟨1117,by decide⟩
def sourceMap1792 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1792 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1792_checked : acceptsGraphIso
    (source (graph core1792) (root 10) 0 2) DegreeTwoThreeSpectrum3192.graph sourceMap1792=true := by decide +kernel
theorem fusedMap1792_checked : acceptsGraphIso
    (fused (graph core1792) (root 10) 0 2) DegreeTwoThreeSpectrum3193.graph fusedMap1792=true := by decide +kernel
theorem certified1792 : Certified (graph core1792) (root 10) 0 2 :=
  of_native_maps core1792 DegreeTwoThreeSpectrum3192.graph DegreeTwoThreeSpectrum3193.graph
    sourceMap1792 fusedMap1792 sourceMap1792_checked fusedMap1792_checked
    DegreeTwoThreeFiniteComparisons.comparison1792
#print axioms sourceMap1792_checked
#print axioms fusedMap1792_checked
#print axioms certified1792
def sourceMap1792swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1792swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1792swap_checked : acceptsGraphIso
    (source (graph core1792) (root 10) 2 0) DegreeTwoThreeSpectrum3192.graph sourceMap1792swap=true := by decide +kernel
theorem fusedMap1792swap_checked : acceptsGraphIso
    (fused (graph core1792) (root 10) 2 0) DegreeTwoThreeSpectrum3193.graph fusedMap1792swap=true := by decide +kernel
theorem certified1792swap : Certified (graph core1792) (root 10) 2 0 :=
  of_native_maps core1792 DegreeTwoThreeSpectrum3192.graph DegreeTwoThreeSpectrum3193.graph
    sourceMap1792swap fusedMap1792swap sourceMap1792swap_checked fusedMap1792swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1792
#print axioms sourceMap1792swap_checked
#print axioms fusedMap1792swap_checked
#print axioms certified1792swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
