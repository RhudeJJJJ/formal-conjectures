/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3342 : Family 9 := level9.get ⟨350,by decide⟩
def sourceMap3342 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3342 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3342_checked : acceptsGraphIso
    (source (graph core3342) (root 9) 0 5) DegreeTwoThreeSpectrum6159.graph sourceMap3342=true := by decide +kernel
theorem fusedMap3342_checked : acceptsGraphIso
    (fused (graph core3342) (root 9) 0 5) DegreeTwoThreeSpectrum5201.graph fusedMap3342=true := by decide +kernel
theorem certified3342 : Certified (graph core3342) (root 9) 0 5 :=
  of_native_maps core3342 DegreeTwoThreeSpectrum6159.graph DegreeTwoThreeSpectrum5201.graph
    sourceMap3342 fusedMap3342 sourceMap3342_checked fusedMap3342_checked
    DegreeTwoThreeFiniteComparisons.comparison3342
#print axioms sourceMap3342_checked
#print axioms fusedMap3342_checked
#print axioms certified3342
def sourceMap3342swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3342swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3342swap_checked : acceptsGraphIso
    (source (graph core3342) (root 9) 5 0) DegreeTwoThreeSpectrum6159.graph sourceMap3342swap=true := by decide +kernel
theorem fusedMap3342swap_checked : acceptsGraphIso
    (fused (graph core3342) (root 9) 5 0) DegreeTwoThreeSpectrum5201.graph fusedMap3342swap=true := by decide +kernel
theorem certified3342swap : Certified (graph core3342) (root 9) 5 0 :=
  of_native_maps core3342 DegreeTwoThreeSpectrum6159.graph DegreeTwoThreeSpectrum5201.graph
    sourceMap3342swap fusedMap3342swap sourceMap3342swap_checked fusedMap3342swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3342
#print axioms sourceMap3342swap_checked
#print axioms fusedMap3342swap_checked
#print axioms certified3342swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
