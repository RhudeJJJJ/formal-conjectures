/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2648 : Family 10 := level10.get ⟨671,by decide⟩
def sourceMap2648 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,16,8,9,10,11,12] (sourceLabel 10 0 4 v)
def fusedMap2648 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2648_checked : acceptsGraphIso
    (source (graph core2648) (root 10) 0 4) DegreeTwoThreeSpectrum6453.graph sourceMap2648=true := by decide +kernel
theorem fusedMap2648_checked : acceptsGraphIso
    (fused (graph core2648) (root 10) 0 4) DegreeTwoThreeSpectrum5386.graph fusedMap2648=true := by decide +kernel
theorem certified2648 : Certified (graph core2648) (root 10) 0 4 :=
  of_native_maps core2648 DegreeTwoThreeSpectrum6453.graph DegreeTwoThreeSpectrum5386.graph
    sourceMap2648 fusedMap2648 sourceMap2648_checked fusedMap2648_checked
    DegreeTwoThreeFiniteComparisons.comparison2648
#print axioms sourceMap2648_checked
#print axioms fusedMap2648_checked
#print axioms certified2648
def sourceMap2648swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,13,14,15,8,9,10,11,12,16] (sourceLabel 10 4 0 v)
def fusedMap2648swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2648swap_checked : acceptsGraphIso
    (source (graph core2648) (root 10) 4 0) DegreeTwoThreeSpectrum6453.graph sourceMap2648swap=true := by decide +kernel
theorem fusedMap2648swap_checked : acceptsGraphIso
    (fused (graph core2648) (root 10) 4 0) DegreeTwoThreeSpectrum5386.graph fusedMap2648swap=true := by decide +kernel
theorem certified2648swap : Certified (graph core2648) (root 10) 4 0 :=
  of_native_maps core2648 DegreeTwoThreeSpectrum6453.graph DegreeTwoThreeSpectrum5386.graph
    sourceMap2648swap fusedMap2648swap sourceMap2648swap_checked fusedMap2648swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2648
#print axioms sourceMap2648swap_checked
#print axioms fusedMap2648swap_checked
#print axioms certified2648swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
