/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3438 : Family 9 := level9.get ⟨587,by decide⟩
def sourceMap3438 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3438 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3438_checked : acceptsGraphIso
    (source (graph core3438) (root 9) 0 5) DegreeTwoThreeSpectrum6175.graph sourceMap3438=true := by decide +kernel
theorem fusedMap3438_checked : acceptsGraphIso
    (fused (graph core3438) (root 9) 0 5) DegreeTwoThreeSpectrum6176.graph fusedMap3438=true := by decide +kernel
theorem certified3438 : Certified (graph core3438) (root 9) 0 5 :=
  of_native_maps core3438 DegreeTwoThreeSpectrum6175.graph DegreeTwoThreeSpectrum6176.graph
    sourceMap3438 fusedMap3438 sourceMap3438_checked fusedMap3438_checked
    DegreeTwoThreeFiniteComparisons.comparison3438
#print axioms sourceMap3438_checked
#print axioms fusedMap3438_checked
#print axioms certified3438
def sourceMap3438swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3438swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3438swap_checked : acceptsGraphIso
    (source (graph core3438) (root 9) 5 0) DegreeTwoThreeSpectrum6175.graph sourceMap3438swap=true := by decide +kernel
theorem fusedMap3438swap_checked : acceptsGraphIso
    (fused (graph core3438) (root 9) 5 0) DegreeTwoThreeSpectrum6176.graph fusedMap3438swap=true := by decide +kernel
theorem certified3438swap : Certified (graph core3438) (root 9) 5 0 :=
  of_native_maps core3438 DegreeTwoThreeSpectrum6175.graph DegreeTwoThreeSpectrum6176.graph
    sourceMap3438swap fusedMap3438swap sourceMap3438swap_checked fusedMap3438swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3438
#print axioms sourceMap3438swap_checked
#print axioms fusedMap3438swap_checked
#print axioms certified3438swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
