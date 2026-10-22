/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3306 : Family 9 := level9.get ⟨253,by decide⟩
def sourceMap3306 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3306 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3306_checked : acceptsGraphIso
    (source (graph core3306) (root 9) 0 5) DegreeTwoThreeSpectrum5667.graph sourceMap3306=true := by decide +kernel
theorem fusedMap3306_checked : acceptsGraphIso
    (fused (graph core3306) (root 9) 0 5) DegreeTwoThreeSpectrum5668.graph fusedMap3306=true := by decide +kernel
theorem certified3306 : Certified (graph core3306) (root 9) 0 5 :=
  of_native_maps core3306 DegreeTwoThreeSpectrum5667.graph DegreeTwoThreeSpectrum5668.graph
    sourceMap3306 fusedMap3306 sourceMap3306_checked fusedMap3306_checked
    DegreeTwoThreeFiniteComparisons.comparison3306
#print axioms sourceMap3306_checked
#print axioms fusedMap3306_checked
#print axioms certified3306
def sourceMap3306swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3306swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3306swap_checked : acceptsGraphIso
    (source (graph core3306) (root 9) 5 0) DegreeTwoThreeSpectrum5667.graph sourceMap3306swap=true := by decide +kernel
theorem fusedMap3306swap_checked : acceptsGraphIso
    (fused (graph core3306) (root 9) 5 0) DegreeTwoThreeSpectrum5668.graph fusedMap3306swap=true := by decide +kernel
theorem certified3306swap : Certified (graph core3306) (root 9) 5 0 :=
  of_native_maps core3306 DegreeTwoThreeSpectrum5667.graph DegreeTwoThreeSpectrum5668.graph
    sourceMap3306swap fusedMap3306swap sourceMap3306swap_checked fusedMap3306swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3306
#print axioms sourceMap3306swap_checked
#print axioms fusedMap3306swap_checked
#print axioms certified3306swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
