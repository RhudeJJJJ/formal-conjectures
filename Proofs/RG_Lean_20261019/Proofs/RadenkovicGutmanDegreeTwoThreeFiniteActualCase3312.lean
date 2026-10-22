/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3312 : Family 9 := level9.get ⟨272,by decide⟩
def sourceMap3312 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3312 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3312_checked : acceptsGraphIso
    (source (graph core3312) (root 9) 0 5) DegreeTwoThreeSpectrum5745.graph sourceMap3312=true := by decide +kernel
theorem fusedMap3312_checked : acceptsGraphIso
    (fused (graph core3312) (root 9) 0 5) DegreeTwoThreeSpectrum5746.graph fusedMap3312=true := by decide +kernel
theorem certified3312 : Certified (graph core3312) (root 9) 0 5 :=
  of_native_maps core3312 DegreeTwoThreeSpectrum5745.graph DegreeTwoThreeSpectrum5746.graph
    sourceMap3312 fusedMap3312 sourceMap3312_checked fusedMap3312_checked
    DegreeTwoThreeFiniteComparisons.comparison3312
#print axioms sourceMap3312_checked
#print axioms fusedMap3312_checked
#print axioms certified3312
def sourceMap3312swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3312swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3312swap_checked : acceptsGraphIso
    (source (graph core3312) (root 9) 5 0) DegreeTwoThreeSpectrum5745.graph sourceMap3312swap=true := by decide +kernel
theorem fusedMap3312swap_checked : acceptsGraphIso
    (fused (graph core3312) (root 9) 5 0) DegreeTwoThreeSpectrum5746.graph fusedMap3312swap=true := by decide +kernel
theorem certified3312swap : Certified (graph core3312) (root 9) 5 0 :=
  of_native_maps core3312 DegreeTwoThreeSpectrum5745.graph DegreeTwoThreeSpectrum5746.graph
    sourceMap3312swap fusedMap3312swap sourceMap3312swap_checked fusedMap3312swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3312
#print axioms sourceMap3312swap_checked
#print axioms fusedMap3312swap_checked
#print axioms certified3312swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
