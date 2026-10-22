/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1989 : Family 10 := level10.get ⟨1592,by decide⟩
def sourceMap1989 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,14,11,12,13] (sourceLabel 10 0 2 v)
def fusedMap1989 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1989_checked : acceptsGraphIso
    (source (graph core1989) (root 10) 0 2) DegreeTwoThreeSpectrum3773.graph sourceMap1989=true := by decide +kernel
theorem fusedMap1989_checked : acceptsGraphIso
    (fused (graph core1989) (root 10) 0 2) DegreeTwoThreeSpectrum3095.graph fusedMap1989=true := by decide +kernel
theorem certified1989 : Certified (graph core1989) (root 10) 0 2 :=
  of_native_maps core1989 DegreeTwoThreeSpectrum3773.graph DegreeTwoThreeSpectrum3095.graph
    sourceMap1989 fusedMap1989 sourceMap1989_checked fusedMap1989_checked
    DegreeTwoThreeFiniteComparisons.comparison1989
#print axioms sourceMap1989_checked
#print axioms fusedMap1989_checked
#print axioms certified1989
def sourceMap1989swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (sourceLabel 10 2 0 v)
def fusedMap1989swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1989swap_checked : acceptsGraphIso
    (source (graph core1989) (root 10) 2 0) DegreeTwoThreeSpectrum3773.graph sourceMap1989swap=true := by decide +kernel
theorem fusedMap1989swap_checked : acceptsGraphIso
    (fused (graph core1989) (root 10) 2 0) DegreeTwoThreeSpectrum3095.graph fusedMap1989swap=true := by decide +kernel
theorem certified1989swap : Certified (graph core1989) (root 10) 2 0 :=
  of_native_maps core1989 DegreeTwoThreeSpectrum3773.graph DegreeTwoThreeSpectrum3095.graph
    sourceMap1989swap fusedMap1989swap sourceMap1989swap_checked fusedMap1989swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1989
#print axioms sourceMap1989swap_checked
#print axioms fusedMap1989swap_checked
#print axioms certified1989swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
