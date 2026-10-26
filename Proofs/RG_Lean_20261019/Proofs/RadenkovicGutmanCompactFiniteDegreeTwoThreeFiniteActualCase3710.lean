/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons74
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3710 : Family 6 := level6.get ⟨5,by decide⟩
def sourceMap3710 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (sourceLabel 6 0 8 v)
def fusedMap3710 : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15,16] (fusedLabel 6 0 8 v)
theorem sourceMap3710_checked : acceptsGraphIso
    (source (graph core3710) (root 6) 0 8) DegreeTwoThreeSpectrum5115.graph sourceMap3710=true := by decide +kernel
theorem fusedMap3710_checked : acceptsGraphIso
    (fused (graph core3710) (root 6) 0 8) DegreeTwoThreeSpectrum4963.graph fusedMap3710=true := by decide +kernel
theorem certified3710 : Certified (graph core3710) (root 6) 0 8 :=
  of_native_maps core3710 DegreeTwoThreeSpectrum5115.graph DegreeTwoThreeSpectrum4963.graph
    sourceMap3710 fusedMap3710 sourceMap3710_checked fusedMap3710_checked
    DegreeTwoThreeFiniteComparisons.comparison3710
#print axioms sourceMap3710_checked
#print axioms fusedMap3710_checked
#print axioms certified3710
def sourceMap3710swap : (Vertices 6 ⊕ Fin 9 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,1,0,10,11,12,13,14,15,16,9] (sourceLabel 6 8 0 v)
def fusedMap3710swap : (Vertices 6 ⊕ Fin 10) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,1,0,9,10,11,12,13,14,15,16] (fusedLabel 6 8 0 v)
theorem sourceMap3710swap_checked : acceptsGraphIso
    (source (graph core3710) (root 6) 8 0) DegreeTwoThreeSpectrum5115.graph sourceMap3710swap=true := by decide +kernel
theorem fusedMap3710swap_checked : acceptsGraphIso
    (fused (graph core3710) (root 6) 8 0) DegreeTwoThreeSpectrum4963.graph fusedMap3710swap=true := by decide +kernel
theorem certified3710swap : Certified (graph core3710) (root 6) 8 0 :=
  of_native_maps core3710 DegreeTwoThreeSpectrum5115.graph DegreeTwoThreeSpectrum4963.graph
    sourceMap3710swap fusedMap3710swap sourceMap3710swap_checked fusedMap3710swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3710
#print axioms sourceMap3710swap_checked
#print axioms fusedMap3710swap_checked
#print axioms certified3710swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
