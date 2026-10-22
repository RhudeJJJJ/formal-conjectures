/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons62
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3141 : Family 8 := level8.get ⟨13,by decide⟩
def sourceMap3141 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,15,8,9,10,11,12,13] (sourceLabel 8 0 5 v)
def fusedMap3141 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 0 5 v)
theorem sourceMap3141_checked : acceptsGraphIso
    (source (graph core3141) (root 8) 0 5) DegreeTwoThreeSpectrum3981.graph sourceMap3141=true := by decide +kernel
theorem fusedMap3141_checked : acceptsGraphIso
    (fused (graph core3141) (root 8) 0 5) DegreeTwoThreeSpectrum3859.graph fusedMap3141=true := by decide +kernel
theorem certified3141 : Certified (graph core3141) (root 8) 0 5 :=
  of_native_maps core3141 DegreeTwoThreeSpectrum3981.graph DegreeTwoThreeSpectrum3859.graph
    sourceMap3141 fusedMap3141 sourceMap3141_checked fusedMap3141_checked
    DegreeTwoThreeFiniteComparisons.comparison3141
#print axioms sourceMap3141_checked
#print axioms fusedMap3141_checked
#print axioms certified3141
def sourceMap3141swap : (Vertices 8 ⊕ Fin 6 ⊕ Fin 1) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,14,8,9,10,11,12,13,15] (sourceLabel 8 5 0 v)
def fusedMap3141swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 8 5 0 v)
theorem sourceMap3141swap_checked : acceptsGraphIso
    (source (graph core3141) (root 8) 5 0) DegreeTwoThreeSpectrum3981.graph sourceMap3141swap=true := by decide +kernel
theorem fusedMap3141swap_checked : acceptsGraphIso
    (fused (graph core3141) (root 8) 5 0) DegreeTwoThreeSpectrum3859.graph fusedMap3141swap=true := by decide +kernel
theorem certified3141swap : Certified (graph core3141) (root 8) 5 0 :=
  of_native_maps core3141 DegreeTwoThreeSpectrum3981.graph DegreeTwoThreeSpectrum3859.graph
    sourceMap3141swap fusedMap3141swap sourceMap3141swap_checked fusedMap3141swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3141
#print axioms sourceMap3141swap_checked
#print axioms fusedMap3141swap_checked
#print axioms certified3141swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
