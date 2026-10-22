/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3410 : Family 9 := level9.get ⟨514,by decide⟩
def sourceMap3410 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3410 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3410_checked : acceptsGraphIso
    (source (graph core3410) (root 9) 0 5) DegreeTwoThreeSpectrum6954.graph sourceMap3410=true := by decide +kernel
theorem fusedMap3410_checked : acceptsGraphIso
    (fused (graph core3410) (root 9) 0 5) DegreeTwoThreeSpectrum5738.graph fusedMap3410=true := by decide +kernel
theorem certified3410 : Certified (graph core3410) (root 9) 0 5 :=
  of_native_maps core3410 DegreeTwoThreeSpectrum6954.graph DegreeTwoThreeSpectrum5738.graph
    sourceMap3410 fusedMap3410 sourceMap3410_checked fusedMap3410_checked
    DegreeTwoThreeFiniteComparisons.comparison3410
#print axioms sourceMap3410_checked
#print axioms fusedMap3410_checked
#print axioms certified3410
def sourceMap3410swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3410swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3410swap_checked : acceptsGraphIso
    (source (graph core3410) (root 9) 5 0) DegreeTwoThreeSpectrum6954.graph sourceMap3410swap=true := by decide +kernel
theorem fusedMap3410swap_checked : acceptsGraphIso
    (fused (graph core3410) (root 9) 5 0) DegreeTwoThreeSpectrum5738.graph fusedMap3410swap=true := by decide +kernel
theorem certified3410swap : Certified (graph core3410) (root 9) 5 0 :=
  of_native_maps core3410 DegreeTwoThreeSpectrum6954.graph DegreeTwoThreeSpectrum5738.graph
    sourceMap3410swap fusedMap3410swap sourceMap3410swap_checked fusedMap3410swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3410
#print axioms sourceMap3410swap_checked
#print axioms fusedMap3410swap_checked
#print axioms certified3410swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
