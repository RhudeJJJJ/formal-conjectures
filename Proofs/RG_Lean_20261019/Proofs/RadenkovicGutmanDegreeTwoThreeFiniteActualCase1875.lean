/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1875 : Family 10 := level10.get ⟨1314,by decide⟩
def sourceMap1875 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,14,8,9,10] (sourceLabel 10 0 2 v)
def fusedMap1875 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 0 2 v)
theorem sourceMap1875_checked : acceptsGraphIso
    (source (graph core1875) (root 10) 0 2) DegreeTwoThreeSpectrum3483.graph sourceMap1875=true := by decide +kernel
theorem fusedMap1875_checked : acceptsGraphIso
    (fused (graph core1875) (root 10) 0 2) DegreeTwoThreeSpectrum3487.graph fusedMap1875=true := by decide +kernel
theorem certified1875 : Certified (graph core1875) (root 10) 0 2 :=
  of_native_maps core1875 DegreeTwoThreeSpectrum3483.graph DegreeTwoThreeSpectrum3487.graph
    sourceMap1875 fusedMap1875 sourceMap1875_checked fusedMap1875_checked
    DegreeTwoThreeFiniteComparisons.comparison1875
#print axioms sourceMap1875_checked
#print axioms fusedMap1875_checked
#print axioms certified1875
def sourceMap1875swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,13,8,9,10,14] (sourceLabel 10 2 0 v)
def fusedMap1875swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,12,13,14,8,9,10,11] (fusedLabel 10 2 0 v)
theorem sourceMap1875swap_checked : acceptsGraphIso
    (source (graph core1875) (root 10) 2 0) DegreeTwoThreeSpectrum3483.graph sourceMap1875swap=true := by decide +kernel
theorem fusedMap1875swap_checked : acceptsGraphIso
    (fused (graph core1875) (root 10) 2 0) DegreeTwoThreeSpectrum3487.graph fusedMap1875swap=true := by decide +kernel
theorem certified1875swap : Certified (graph core1875) (root 10) 2 0 :=
  of_native_maps core1875 DegreeTwoThreeSpectrum3483.graph DegreeTwoThreeSpectrum3487.graph
    sourceMap1875swap fusedMap1875swap sourceMap1875swap_checked fusedMap1875swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1875
#print axioms sourceMap1875swap_checked
#print axioms fusedMap1875swap_checked
#print axioms certified1875swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
