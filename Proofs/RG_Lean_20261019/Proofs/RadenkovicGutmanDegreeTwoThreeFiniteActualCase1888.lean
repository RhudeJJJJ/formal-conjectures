/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1888 : Family 10 := level10.get ⟨1346,by decide⟩
def sourceMap1888 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1888 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1888_checked : acceptsGraphIso
    (source (graph core1888) (root 10) 0 2) DegreeTwoThreeSpectrum3529.graph sourceMap1888=true := by decide +kernel
theorem fusedMap1888_checked : acceptsGraphIso
    (fused (graph core1888) (root 10) 0 2) DegreeTwoThreeSpectrum3530.graph fusedMap1888=true := by decide +kernel
theorem certified1888 : Certified (graph core1888) (root 10) 0 2 :=
  of_native_maps core1888 DegreeTwoThreeSpectrum3529.graph DegreeTwoThreeSpectrum3530.graph
    sourceMap1888 fusedMap1888 sourceMap1888_checked fusedMap1888_checked
    DegreeTwoThreeFiniteComparisons.comparison1888
#print axioms sourceMap1888_checked
#print axioms fusedMap1888_checked
#print axioms certified1888
def sourceMap1888swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1888swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1888swap_checked : acceptsGraphIso
    (source (graph core1888) (root 10) 2 0) DegreeTwoThreeSpectrum3529.graph sourceMap1888swap=true := by decide +kernel
theorem fusedMap1888swap_checked : acceptsGraphIso
    (fused (graph core1888) (root 10) 2 0) DegreeTwoThreeSpectrum3530.graph fusedMap1888swap=true := by decide +kernel
theorem certified1888swap : Certified (graph core1888) (root 10) 2 0 :=
  of_native_maps core1888 DegreeTwoThreeSpectrum3529.graph DegreeTwoThreeSpectrum3530.graph
    sourceMap1888swap fusedMap1888swap sourceMap1888swap_checked fusedMap1888swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1888
#print axioms sourceMap1888swap_checked
#print axioms fusedMap1888swap_checked
#print axioms certified1888swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
