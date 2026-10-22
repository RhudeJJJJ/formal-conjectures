/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3374 : Family 9 := level9.get ⟨432,by decide⟩
def sourceMap3374 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3374 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3374_checked : acceptsGraphIso
    (source (graph core3374) (root 9) 0 5) DegreeTwoThreeSpectrum6556.graph sourceMap3374=true := by decide +kernel
theorem fusedMap3374_checked : acceptsGraphIso
    (fused (graph core3374) (root 9) 0 5) DegreeTwoThreeSpectrum5450.graph fusedMap3374=true := by decide +kernel
theorem certified3374 : Certified (graph core3374) (root 9) 0 5 :=
  of_native_maps core3374 DegreeTwoThreeSpectrum6556.graph DegreeTwoThreeSpectrum5450.graph
    sourceMap3374 fusedMap3374 sourceMap3374_checked fusedMap3374_checked
    DegreeTwoThreeFiniteComparisons.comparison3374
#print axioms sourceMap3374_checked
#print axioms fusedMap3374_checked
#print axioms certified3374
def sourceMap3374swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3374swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3374swap_checked : acceptsGraphIso
    (source (graph core3374) (root 9) 5 0) DegreeTwoThreeSpectrum6556.graph sourceMap3374swap=true := by decide +kernel
theorem fusedMap3374swap_checked : acceptsGraphIso
    (fused (graph core3374) (root 9) 5 0) DegreeTwoThreeSpectrum5450.graph fusedMap3374swap=true := by decide +kernel
theorem certified3374swap : Certified (graph core3374) (root 9) 5 0 :=
  of_native_maps core3374 DegreeTwoThreeSpectrum6556.graph DegreeTwoThreeSpectrum5450.graph
    sourceMap3374swap fusedMap3374swap sourceMap3374swap_checked fusedMap3374swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3374
#print axioms sourceMap3374swap_checked
#print axioms fusedMap3374swap_checked
#print axioms certified3374swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
