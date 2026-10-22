/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons65
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3284 : Family 9 := level9.get ⟨190,by decide⟩
def sourceMap3284 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3284 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3284_checked : acceptsGraphIso
    (source (graph core3284) (root 9) 0 5) DegreeTwoThreeSpectrum5375.graph sourceMap3284=true := by decide +kernel
theorem fusedMap3284_checked : acceptsGraphIso
    (fused (graph core3284) (root 9) 0 5) DegreeTwoThreeSpectrum5376.graph fusedMap3284=true := by decide +kernel
theorem certified3284 : Certified (graph core3284) (root 9) 0 5 :=
  of_native_maps core3284 DegreeTwoThreeSpectrum5375.graph DegreeTwoThreeSpectrum5376.graph
    sourceMap3284 fusedMap3284 sourceMap3284_checked fusedMap3284_checked
    DegreeTwoThreeFiniteComparisons.comparison3284
#print axioms sourceMap3284_checked
#print axioms fusedMap3284_checked
#print axioms certified3284
def sourceMap3284swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16,10] (sourceLabel 9 5 0 v)
def fusedMap3284swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3284swap_checked : acceptsGraphIso
    (source (graph core3284) (root 9) 5 0) DegreeTwoThreeSpectrum5375.graph sourceMap3284swap=true := by decide +kernel
theorem fusedMap3284swap_checked : acceptsGraphIso
    (fused (graph core3284) (root 9) 5 0) DegreeTwoThreeSpectrum5376.graph fusedMap3284swap=true := by decide +kernel
theorem certified3284swap : Certified (graph core3284) (root 9) 5 0 :=
  of_native_maps core3284 DegreeTwoThreeSpectrum5375.graph DegreeTwoThreeSpectrum5376.graph
    sourceMap3284swap fusedMap3284swap sourceMap3284swap_checked fusedMap3284swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3284
#print axioms sourceMap3284swap_checked
#print axioms fusedMap3284swap_checked
#print axioms certified3284swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
