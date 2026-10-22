/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons71
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3587 : Family 8 := level8.get ⟨157,by decide⟩
def sourceMap3587 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3587 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3587_checked : acceptsGraphIso
    (source (graph core3587) (root 8) 0 6) DegreeTwoThreeSpectrum5599.graph sourceMap3587=true := by decide +kernel
theorem fusedMap3587_checked : acceptsGraphIso
    (fused (graph core3587) (root 8) 0 6) DegreeTwoThreeSpectrum5601.graph fusedMap3587=true := by decide +kernel
theorem certified3587 : Certified (graph core3587) (root 8) 0 6 :=
  of_native_maps core3587 DegreeTwoThreeSpectrum5599.graph DegreeTwoThreeSpectrum5601.graph
    sourceMap3587 fusedMap3587 sourceMap3587_checked fusedMap3587_checked
    DegreeTwoThreeFiniteComparisons.comparison3587
#print axioms sourceMap3587_checked
#print axioms fusedMap3587_checked
#print axioms certified3587
def sourceMap3587swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,11,12,13,14,15,16,10] (sourceLabel 8 6 0 v)
def fusedMap3587swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3587swap_checked : acceptsGraphIso
    (source (graph core3587) (root 8) 6 0) DegreeTwoThreeSpectrum5599.graph sourceMap3587swap=true := by decide +kernel
theorem fusedMap3587swap_checked : acceptsGraphIso
    (fused (graph core3587) (root 8) 6 0) DegreeTwoThreeSpectrum5601.graph fusedMap3587swap=true := by decide +kernel
theorem certified3587swap : Certified (graph core3587) (root 8) 6 0 :=
  of_native_maps core3587 DegreeTwoThreeSpectrum5599.graph DegreeTwoThreeSpectrum5601.graph
    sourceMap3587swap fusedMap3587swap sourceMap3587swap_checked fusedMap3587swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3587
#print axioms sourceMap3587swap_checked
#print axioms fusedMap3587swap_checked
#print axioms certified3587swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
