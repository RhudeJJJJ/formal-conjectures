/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3412 : Family 9 := level9.get ⟨518,by decide⟩
def sourceMap3412 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3412 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3412_checked : acceptsGraphIso
    (source (graph core3412) (root 9) 0 5) DegreeTwoThreeSpectrum6967.graph sourceMap3412=true := by decide +kernel
theorem fusedMap3412_checked : acceptsGraphIso
    (fused (graph core3412) (root 9) 0 5) DegreeTwoThreeSpectrum5761.graph fusedMap3412=true := by decide +kernel
theorem certified3412 : Certified (graph core3412) (root 9) 0 5 :=
  of_native_maps core3412 DegreeTwoThreeSpectrum6967.graph DegreeTwoThreeSpectrum5761.graph
    sourceMap3412 fusedMap3412 sourceMap3412_checked fusedMap3412_checked
    DegreeTwoThreeFiniteComparisons.comparison3412
#print axioms sourceMap3412_checked
#print axioms fusedMap3412_checked
#print axioms certified3412
def sourceMap3412swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3412swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3412swap_checked : acceptsGraphIso
    (source (graph core3412) (root 9) 5 0) DegreeTwoThreeSpectrum6967.graph sourceMap3412swap=true := by decide +kernel
theorem fusedMap3412swap_checked : acceptsGraphIso
    (fused (graph core3412) (root 9) 5 0) DegreeTwoThreeSpectrum5761.graph fusedMap3412swap=true := by decide +kernel
theorem certified3412swap : Certified (graph core3412) (root 9) 5 0 :=
  of_native_maps core3412 DegreeTwoThreeSpectrum6967.graph DegreeTwoThreeSpectrum5761.graph
    sourceMap3412swap fusedMap3412swap sourceMap3412swap_checked fusedMap3412swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3412
#print axioms sourceMap3412swap_checked
#print axioms fusedMap3412swap_checked
#print axioms certified3412swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
