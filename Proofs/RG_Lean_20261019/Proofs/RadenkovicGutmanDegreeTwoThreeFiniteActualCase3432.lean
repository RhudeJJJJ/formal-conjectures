/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3432 : Family 9 := level9.get ⟨571,by decide⟩
def sourceMap3432 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3432 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3432_checked : acceptsGraphIso
    (source (graph core3432) (root 9) 0 5) DegreeTwoThreeSpectrum6081.graph sourceMap3432=true := by decide +kernel
theorem fusedMap3432_checked : acceptsGraphIso
    (fused (graph core3432) (root 9) 0 5) DegreeTwoThreeSpectrum6082.graph fusedMap3432=true := by decide +kernel
theorem certified3432 : Certified (graph core3432) (root 9) 0 5 :=
  of_native_maps core3432 DegreeTwoThreeSpectrum6081.graph DegreeTwoThreeSpectrum6082.graph
    sourceMap3432 fusedMap3432 sourceMap3432_checked fusedMap3432_checked
    DegreeTwoThreeFiniteComparisons.comparison3432
#print axioms sourceMap3432_checked
#print axioms fusedMap3432_checked
#print axioms certified3432
def sourceMap3432swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3432swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3432swap_checked : acceptsGraphIso
    (source (graph core3432) (root 9) 5 0) DegreeTwoThreeSpectrum6081.graph sourceMap3432swap=true := by decide +kernel
theorem fusedMap3432swap_checked : acceptsGraphIso
    (fused (graph core3432) (root 9) 5 0) DegreeTwoThreeSpectrum6082.graph fusedMap3432swap=true := by decide +kernel
theorem certified3432swap : Certified (graph core3432) (root 9) 5 0 :=
  of_native_maps core3432 DegreeTwoThreeSpectrum6081.graph DegreeTwoThreeSpectrum6082.graph
    sourceMap3432swap fusedMap3432swap sourceMap3432swap_checked fusedMap3432swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3432
#print axioms sourceMap3432swap_checked
#print axioms fusedMap3432swap_checked
#print axioms certified3432swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
