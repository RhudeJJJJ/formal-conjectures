/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons61
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3061 : Family 10 := level10.get ⟨1737,by decide⟩
def sourceMap3061 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,12,0,13,14,15,16] (sourceLabel 10 0 4 v)
def fusedMap3061 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap3061_checked : acceptsGraphIso
    (source (graph core3061) (root 10) 0 4) DegreeTwoThreeSpectrum7378.graph sourceMap3061=true := by decide +kernel
theorem fusedMap3061_checked : acceptsGraphIso
    (fused (graph core3061) (root 10) 0 4) DegreeTwoThreeSpectrum6580.graph fusedMap3061=true := by decide +kernel
theorem certified3061 : Certified (graph core3061) (root 10) 0 4 :=
  of_native_maps core3061 DegreeTwoThreeSpectrum7378.graph DegreeTwoThreeSpectrum6580.graph
    sourceMap3061 fusedMap3061 sourceMap3061_checked fusedMap3061_checked
    DegreeTwoThreeFiniteComparisons.comparison3061
#print axioms sourceMap3061_checked
#print axioms fusedMap3061_checked
#print axioms certified3061
def sourceMap3061swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,13,14,15,16,12] (sourceLabel 10 4 0 v)
def fusedMap3061swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap3061swap_checked : acceptsGraphIso
    (source (graph core3061) (root 10) 4 0) DegreeTwoThreeSpectrum7378.graph sourceMap3061swap=true := by decide +kernel
theorem fusedMap3061swap_checked : acceptsGraphIso
    (fused (graph core3061) (root 10) 4 0) DegreeTwoThreeSpectrum6580.graph fusedMap3061swap=true := by decide +kernel
theorem certified3061swap : Certified (graph core3061) (root 10) 4 0 :=
  of_native_maps core3061 DegreeTwoThreeSpectrum7378.graph DegreeTwoThreeSpectrum6580.graph
    sourceMap3061swap fusedMap3061swap sourceMap3061swap_checked fusedMap3061swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3061
#print axioms sourceMap3061swap_checked
#print axioms fusedMap3061swap_checked
#print axioms certified3061swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
