/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3411 : Family 9 := level9.get ⟨517,by decide⟩
def sourceMap3411 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3411 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3411_checked : acceptsGraphIso
    (source (graph core3411) (root 9) 0 5) DegreeTwoThreeSpectrum6962.graph sourceMap3411=true := by decide +kernel
theorem fusedMap3411_checked : acceptsGraphIso
    (fused (graph core3411) (root 9) 0 5) DegreeTwoThreeSpectrum5760.graph fusedMap3411=true := by decide +kernel
theorem certified3411 : Certified (graph core3411) (root 9) 0 5 :=
  of_native_maps core3411 DegreeTwoThreeSpectrum6962.graph DegreeTwoThreeSpectrum5760.graph
    sourceMap3411 fusedMap3411 sourceMap3411_checked fusedMap3411_checked
    DegreeTwoThreeFiniteComparisons.comparison3411
#print axioms sourceMap3411_checked
#print axioms fusedMap3411_checked
#print axioms certified3411
def sourceMap3411swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3411swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3411swap_checked : acceptsGraphIso
    (source (graph core3411) (root 9) 5 0) DegreeTwoThreeSpectrum6962.graph sourceMap3411swap=true := by decide +kernel
theorem fusedMap3411swap_checked : acceptsGraphIso
    (fused (graph core3411) (root 9) 5 0) DegreeTwoThreeSpectrum5760.graph fusedMap3411swap=true := by decide +kernel
theorem certified3411swap : Certified (graph core3411) (root 9) 5 0 :=
  of_native_maps core3411 DegreeTwoThreeSpectrum6962.graph DegreeTwoThreeSpectrum5760.graph
    sourceMap3411swap fusedMap3411swap sourceMap3411swap_checked fusedMap3411swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3411
#print axioms sourceMap3411swap_checked
#print axioms fusedMap3411swap_checked
#print axioms certified3411swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
