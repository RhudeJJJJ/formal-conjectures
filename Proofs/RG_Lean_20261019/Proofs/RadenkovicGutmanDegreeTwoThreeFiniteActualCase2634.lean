/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons52
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2634 : Family 10 := level10.get ⟨638,by decide⟩
def sourceMap2634 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 5) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,16,10,11,12,13,14] (sourceLabel 10 0 4 v)
def fusedMap2634 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 0 4 v)
theorem sourceMap2634_checked : acceptsGraphIso
    (source (graph core2634) (root 10) 0 4) DegreeTwoThreeSpectrum6395.graph sourceMap2634=true := by decide +kernel
theorem fusedMap2634_checked : acceptsGraphIso
    (fused (graph core2634) (root 10) 0 4) DegreeTwoThreeSpectrum5332.graph fusedMap2634=true := by decide +kernel
theorem certified2634 : Certified (graph core2634) (root 10) 0 4 :=
  of_native_maps core2634 DegreeTwoThreeSpectrum6395.graph DegreeTwoThreeSpectrum5332.graph
    sourceMap2634 fusedMap2634 sourceMap2634_checked fusedMap2634_checked
    DegreeTwoThreeFiniteComparisons.comparison2634
#print axioms sourceMap2634_checked
#print axioms fusedMap2634_checked
#print axioms certified2634
def sourceMap2634swap : (Vertices 10 ⊕ Fin 5 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,15,10,11,12,13,14,16] (sourceLabel 10 4 0 v)
def fusedMap2634swap : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 4 0 v)
theorem sourceMap2634swap_checked : acceptsGraphIso
    (source (graph core2634) (root 10) 4 0) DegreeTwoThreeSpectrum6395.graph sourceMap2634swap=true := by decide +kernel
theorem fusedMap2634swap_checked : acceptsGraphIso
    (fused (graph core2634) (root 10) 4 0) DegreeTwoThreeSpectrum5332.graph fusedMap2634swap=true := by decide +kernel
theorem certified2634swap : Certified (graph core2634) (root 10) 4 0 :=
  of_native_maps core2634 DegreeTwoThreeSpectrum6395.graph DegreeTwoThreeSpectrum5332.graph
    sourceMap2634swap fusedMap2634swap sourceMap2634swap_checked fusedMap2634swap_checked
    DegreeTwoThreeFiniteComparisons.comparison2634
#print axioms sourceMap2634swap_checked
#print axioms fusedMap2634swap_checked
#print axioms certified2634swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
