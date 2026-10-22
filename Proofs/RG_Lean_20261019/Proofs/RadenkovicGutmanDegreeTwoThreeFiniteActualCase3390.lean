/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3390 : Family 9 := level9.get ⟨471,by decide⟩
def sourceMap3390 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3390 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3390_checked : acceptsGraphIso
    (source (graph core3390) (root 9) 0 5) DegreeTwoThreeSpectrum6723.graph sourceMap3390=true := by decide +kernel
theorem fusedMap3390_checked : acceptsGraphIso
    (fused (graph core3390) (root 9) 0 5) DegreeTwoThreeSpectrum5564.graph fusedMap3390=true := by decide +kernel
theorem certified3390 : Certified (graph core3390) (root 9) 0 5 :=
  of_native_maps core3390 DegreeTwoThreeSpectrum6723.graph DegreeTwoThreeSpectrum5564.graph
    sourceMap3390 fusedMap3390 sourceMap3390_checked fusedMap3390_checked
    DegreeTwoThreeFiniteComparisons.comparison3390
#print axioms sourceMap3390_checked
#print axioms fusedMap3390_checked
#print axioms certified3390
def sourceMap3390swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3390swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3390swap_checked : acceptsGraphIso
    (source (graph core3390) (root 9) 5 0) DegreeTwoThreeSpectrum6723.graph sourceMap3390swap=true := by decide +kernel
theorem fusedMap3390swap_checked : acceptsGraphIso
    (fused (graph core3390) (root 9) 5 0) DegreeTwoThreeSpectrum5564.graph fusedMap3390swap=true := by decide +kernel
theorem certified3390swap : Certified (graph core3390) (root 9) 5 0 :=
  of_native_maps core3390 DegreeTwoThreeSpectrum6723.graph DegreeTwoThreeSpectrum5564.graph
    sourceMap3390swap fusedMap3390swap sourceMap3390swap_checked fusedMap3390swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3390
#print axioms sourceMap3390swap_checked
#print axioms fusedMap3390swap_checked
#print axioms certified3390swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
