/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3980 : Family 7 := level7.get ⟨88,by decide⟩
def sourceMap3980 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (sourceLabel 7 1 5 v)
def fusedMap3980 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 1 5 v)
theorem sourceMap3980_checked : acceptsGraphIso
    (source (graph core3980) (root 7) 1 5) DegreeTwoThreeSpectrum4462.graph sourceMap3980=true := by decide +kernel
theorem fusedMap3980_checked : acceptsGraphIso
    (fused (graph core3980) (root 7) 1 5) DegreeTwoThreeSpectrum4004.graph fusedMap3980=true := by decide +kernel
theorem certified3980 : Certified (graph core3980) (root 7) 1 5 :=
  of_native_maps core3980 DegreeTwoThreeSpectrum4462.graph DegreeTwoThreeSpectrum4004.graph
    sourceMap3980 fusedMap3980 sourceMap3980_checked fusedMap3980_checked
    DegreeTwoThreeFiniteComparisons.comparison3980
#print axioms sourceMap3980_checked
#print axioms fusedMap3980_checked
#print axioms certified3980
def sourceMap3980swap : (Vertices 7 ⊕ Fin 6 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,0,11,12,13,14,15,9,10] (sourceLabel 7 5 1 v)
def fusedMap3980swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 5 1 v)
theorem sourceMap3980swap_checked : acceptsGraphIso
    (source (graph core3980) (root 7) 5 1) DegreeTwoThreeSpectrum4462.graph sourceMap3980swap=true := by decide +kernel
theorem fusedMap3980swap_checked : acceptsGraphIso
    (fused (graph core3980) (root 7) 5 1) DegreeTwoThreeSpectrum4004.graph fusedMap3980swap=true := by decide +kernel
theorem certified3980swap : Certified (graph core3980) (root 7) 5 1 :=
  of_native_maps core3980 DegreeTwoThreeSpectrum4462.graph DegreeTwoThreeSpectrum4004.graph
    sourceMap3980swap fusedMap3980swap sourceMap3980swap_checked fusedMap3980swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3980
#print axioms sourceMap3980swap_checked
#print axioms fusedMap3980swap_checked
#print axioms certified3980swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
