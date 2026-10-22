/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1797 : Family 10 := level10.get ⟨1128,by decide⟩
def sourceMap1797 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 3) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,14,10,11,12] (sourceLabel 10 0 2 v)
def fusedMap1797 : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 0 2 v)
theorem sourceMap1797_checked : acceptsGraphIso
    (source (graph core1797) (root 10) 0 2) DegreeTwoThreeSpectrum3207.graph sourceMap1797=true := by decide +kernel
theorem fusedMap1797_checked : acceptsGraphIso
    (fused (graph core1797) (root 10) 0 2) DegreeTwoThreeSpectrum3208.graph fusedMap1797=true := by decide +kernel
theorem certified1797 : Certified (graph core1797) (root 10) 0 2 :=
  of_native_maps core1797 DegreeTwoThreeSpectrum3207.graph DegreeTwoThreeSpectrum3208.graph
    sourceMap1797 fusedMap1797 sourceMap1797_checked fusedMap1797_checked
    DegreeTwoThreeFiniteComparisons.comparison1797
#print axioms sourceMap1797_checked
#print axioms fusedMap1797_checked
#print axioms certified1797
def sourceMap1797swap : (Vertices 10 ⊕ Fin 3 ⊕ Fin 1) → Fin 15 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,13,10,11,12,14] (sourceLabel 10 2 0 v)
def fusedMap1797swap : (Vertices 10 ⊕ Fin 4) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,14,10,11,12,13] (fusedLabel 10 2 0 v)
theorem sourceMap1797swap_checked : acceptsGraphIso
    (source (graph core1797) (root 10) 2 0) DegreeTwoThreeSpectrum3207.graph sourceMap1797swap=true := by decide +kernel
theorem fusedMap1797swap_checked : acceptsGraphIso
    (fused (graph core1797) (root 10) 2 0) DegreeTwoThreeSpectrum3208.graph fusedMap1797swap=true := by decide +kernel
theorem certified1797swap : Certified (graph core1797) (root 10) 2 0 :=
  of_native_maps core1797 DegreeTwoThreeSpectrum3207.graph DegreeTwoThreeSpectrum3208.graph
    sourceMap1797swap fusedMap1797swap sourceMap1797swap_checked fusedMap1797swap_checked
    DegreeTwoThreeFiniteComparisons.comparison1797
#print axioms sourceMap1797swap_checked
#print axioms fusedMap1797swap_checked
#print axioms certified1797swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
