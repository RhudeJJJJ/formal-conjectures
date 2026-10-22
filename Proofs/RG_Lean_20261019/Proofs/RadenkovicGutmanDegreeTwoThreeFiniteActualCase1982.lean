/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1982 : Family 10 := level10.get ⟨1579,by decide⟩
def sourceMap1982 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1982 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1982_checked : acceptsGraphIso
    (source (graph core1982) (root 10) 0 2) DegreeTwoThreeSpectrum3766.graph sourceMap1982=true := by decide +kernel
theorem fusedMap1982_checked : acceptsGraphIso
    (fused (graph core1982) (root 10) 0 2) DegreeTwoThreeSpectrum3074.graph fusedMap1982=true := by decide +kernel
theorem certified1982 : Certified (graph core1982) (root 10) 0 2 :=
  of_native_maps core1982 DegreeTwoThreeSpectrum3766.graph DegreeTwoThreeSpectrum3074.graph
    sourceMap1982 fusedMap1982 sourceMap1982_checked fusedMap1982_checked
    DegreeTwoThreeFiniteComparisons.comparison1982
#print axioms sourceMap1982_checked
#print axioms fusedMap1982_checked
#print axioms certified1982
def sourceMap1982swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1982swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1982swap_checked : acceptsGraphIso
    (source (graph core1982) (root 10) 2 0) DegreeTwoThreeSpectrum3766.graph sourceMap1982swap=true := by decide +kernel
theorem fusedMap1982swap_checked : acceptsGraphIso
    (fused (graph core1982) (root 10) 2 0) DegreeTwoThreeSpectrum3074.graph fusedMap1982swap=true := by decide +kernel
theorem certified1982swap : Certified (graph core1982) (root 10) 2 0 :=
  of_native_maps core1982 DegreeTwoThreeSpectrum3766.graph DegreeTwoThreeSpectrum3074.graph
    sourceMap1982swap fusedMap1982swap sourceMap1982swap_checked fusedMap1982swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1982
#print axioms sourceMap1982swap_checked
#print axioms fusedMap1982swap_checked
#print axioms certified1982swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
