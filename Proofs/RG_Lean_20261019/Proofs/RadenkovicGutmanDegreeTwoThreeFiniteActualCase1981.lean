/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1981 : Family 10 := level10.get ⟨1577,by decide⟩
def sourceMap1981 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,14,9,10,11] (sourceLabel 10 0 2 v)
def fusedMap1981 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 0 2 v)
theorem sourceMap1981_checked : acceptsGraphIso
    (source (graph core1981) (root 10) 0 2) DegreeTwoThreeSpectrum3765.graph sourceMap1981=true := by decide +kernel
theorem fusedMap1981_checked : acceptsGraphIso
    (fused (graph core1981) (root 10) 0 2) DegreeTwoThreeSpectrum3071.graph fusedMap1981=true := by decide +kernel
theorem certified1981 : Certified (graph core1981) (root 10) 0 2 :=
  of_native_maps core1981 DegreeTwoThreeSpectrum3765.graph DegreeTwoThreeSpectrum3071.graph
    sourceMap1981 fusedMap1981 sourceMap1981_checked fusedMap1981_checked
    DegreeTwoThreeFiniteComparisons.comparison1981
#print axioms sourceMap1981_checked
#print axioms fusedMap1981_checked
#print axioms certified1981
def sourceMap1981swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,12,13,9,10,11,14] (sourceLabel 10 2 0 v)
def fusedMap1981swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 10 2 0 v)
theorem sourceMap1981swap_checked : acceptsGraphIso
    (source (graph core1981) (root 10) 2 0) DegreeTwoThreeSpectrum3765.graph sourceMap1981swap=true := by decide +kernel
theorem fusedMap1981swap_checked : acceptsGraphIso
    (fused (graph core1981) (root 10) 2 0) DegreeTwoThreeSpectrum3071.graph fusedMap1981swap=true := by decide +kernel
theorem certified1981swap : Certified (graph core1981) (root 10) 2 0 :=
  of_native_maps core1981 DegreeTwoThreeSpectrum3765.graph DegreeTwoThreeSpectrum3071.graph
    sourceMap1981swap fusedMap1981swap sourceMap1981swap_checked fusedMap1981swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1981
#print axioms sourceMap1981swap_checked
#print axioms fusedMap1981swap_checked
#print axioms certified1981swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
