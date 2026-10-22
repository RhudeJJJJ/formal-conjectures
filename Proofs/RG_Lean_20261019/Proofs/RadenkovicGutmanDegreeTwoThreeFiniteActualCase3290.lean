/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3290 : Family 9 := level9.get ⟨207,by decide⟩
def sourceMap3290 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3290 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3290_checked : acceptsGraphIso
    (source (graph core3290) (root 9) 0 5) DegreeTwoThreeSpectrum5455.graph sourceMap3290=true := by decide +kernel
theorem fusedMap3290_checked : acceptsGraphIso
    (fused (graph core3290) (root 9) 0 5) DegreeTwoThreeSpectrum5456.graph fusedMap3290=true := by decide +kernel
theorem certified3290 : Certified (graph core3290) (root 9) 0 5 :=
  of_native_maps core3290 DegreeTwoThreeSpectrum5455.graph DegreeTwoThreeSpectrum5456.graph
    sourceMap3290 fusedMap3290 sourceMap3290_checked fusedMap3290_checked
    DegreeTwoThreeFiniteComparisons.comparison3290
#print axioms sourceMap3290_checked
#print axioms fusedMap3290_checked
#print axioms certified3290
def sourceMap3290swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3290swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3290swap_checked : acceptsGraphIso
    (source (graph core3290) (root 9) 5 0) DegreeTwoThreeSpectrum5455.graph sourceMap3290swap=true := by decide +kernel
theorem fusedMap3290swap_checked : acceptsGraphIso
    (fused (graph core3290) (root 9) 5 0) DegreeTwoThreeSpectrum5456.graph fusedMap3290swap=true := by decide +kernel
theorem certified3290swap : Certified (graph core3290) (root 9) 5 0 :=
  of_native_maps core3290 DegreeTwoThreeSpectrum5455.graph DegreeTwoThreeSpectrum5456.graph
    sourceMap3290swap fusedMap3290swap sourceMap3290swap_checked fusedMap3290swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3290
#print axioms sourceMap3290swap_checked
#print axioms fusedMap3290swap_checked
#print axioms certified3290swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
