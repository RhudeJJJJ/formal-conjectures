/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons66
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3333 : Family 9 := level9.get ⟨327,by decide⟩
def sourceMap3333 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3333 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3333_checked : acceptsGraphIso
    (source (graph core3333) (root 9) 0 5) DegreeTwoThreeSpectrum6035.graph sourceMap3333=true := by decide +kernel
theorem fusedMap3333_checked : acceptsGraphIso
    (fused (graph core3333) (root 9) 0 5) DegreeTwoThreeSpectrum5147.graph fusedMap3333=true := by decide +kernel
theorem certified3333 : Certified (graph core3333) (root 9) 0 5 :=
  of_native_maps core3333 DegreeTwoThreeSpectrum6035.graph DegreeTwoThreeSpectrum5147.graph
    sourceMap3333 fusedMap3333 sourceMap3333_checked fusedMap3333_checked
    DegreeTwoThreeFiniteComparisons.comparison3333
#print axioms sourceMap3333_checked
#print axioms fusedMap3333_checked
#print axioms certified3333
def sourceMap3333swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3333swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3333swap_checked : acceptsGraphIso
    (source (graph core3333) (root 9) 5 0) DegreeTwoThreeSpectrum6035.graph sourceMap3333swap=true := by decide +kernel
theorem fusedMap3333swap_checked : acceptsGraphIso
    (fused (graph core3333) (root 9) 5 0) DegreeTwoThreeSpectrum5147.graph fusedMap3333swap=true := by decide +kernel
theorem certified3333swap : Certified (graph core3333) (root 9) 5 0 :=
  of_native_maps core3333 DegreeTwoThreeSpectrum6035.graph DegreeTwoThreeSpectrum5147.graph
    sourceMap3333swap fusedMap3333swap sourceMap3333swap_checked fusedMap3333swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3333
#print axioms sourceMap3333swap_checked
#print axioms fusedMap3333swap_checked
#print axioms certified3333swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
