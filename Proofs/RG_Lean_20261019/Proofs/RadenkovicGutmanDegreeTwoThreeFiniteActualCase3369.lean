/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3369 : Family 9 := level9.get ⟨420,by decide⟩
def sourceMap3369 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3369 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3369_checked : acceptsGraphIso
    (source (graph core3369) (root 9) 0 5) DegreeTwoThreeSpectrum6501.graph sourceMap3369=true := by decide +kernel
theorem fusedMap3369_checked : acceptsGraphIso
    (fused (graph core3369) (root 9) 0 5) DegreeTwoThreeSpectrum5425.graph fusedMap3369=true := by decide +kernel
theorem certified3369 : Certified (graph core3369) (root 9) 0 5 :=
  of_native_maps core3369 DegreeTwoThreeSpectrum6501.graph DegreeTwoThreeSpectrum5425.graph
    sourceMap3369 fusedMap3369 sourceMap3369_checked fusedMap3369_checked
    DegreeTwoThreeFiniteComparisons.comparison3369
#print axioms sourceMap3369_checked
#print axioms fusedMap3369_checked
#print axioms certified3369
def sourceMap3369swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3369swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3369swap_checked : acceptsGraphIso
    (source (graph core3369) (root 9) 5 0) DegreeTwoThreeSpectrum6501.graph sourceMap3369swap=true := by decide +kernel
theorem fusedMap3369swap_checked : acceptsGraphIso
    (fused (graph core3369) (root 9) 5 0) DegreeTwoThreeSpectrum5425.graph fusedMap3369swap=true := by decide +kernel
theorem certified3369swap : Certified (graph core3369) (root 9) 5 0 :=
  of_native_maps core3369 DegreeTwoThreeSpectrum6501.graph DegreeTwoThreeSpectrum5425.graph
    sourceMap3369swap fusedMap3369swap sourceMap3369swap_checked fusedMap3369swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3369
#print axioms sourceMap3369swap_checked
#print axioms fusedMap3369swap_checked
#print axioms certified3369swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
