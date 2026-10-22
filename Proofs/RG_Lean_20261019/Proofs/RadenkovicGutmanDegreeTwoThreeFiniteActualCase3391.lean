/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3391 : Family 9 := level9.get ⟨473,by decide⟩
def sourceMap3391 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3391 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3391_checked : acceptsGraphIso
    (source (graph core3391) (root 9) 0 5) DegreeTwoThreeSpectrum6734.graph sourceMap3391=true := by decide +kernel
theorem fusedMap3391_checked : acceptsGraphIso
    (fused (graph core3391) (root 9) 0 5) DegreeTwoThreeSpectrum5573.graph fusedMap3391=true := by decide +kernel
theorem certified3391 : Certified (graph core3391) (root 9) 0 5 :=
  of_native_maps core3391 DegreeTwoThreeSpectrum6734.graph DegreeTwoThreeSpectrum5573.graph
    sourceMap3391 fusedMap3391 sourceMap3391_checked fusedMap3391_checked
    DegreeTwoThreeFiniteComparisons.comparison3391
#print axioms sourceMap3391_checked
#print axioms fusedMap3391_checked
#print axioms certified3391
def sourceMap3391swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3391swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3391swap_checked : acceptsGraphIso
    (source (graph core3391) (root 9) 5 0) DegreeTwoThreeSpectrum6734.graph sourceMap3391swap=true := by decide +kernel
theorem fusedMap3391swap_checked : acceptsGraphIso
    (fused (graph core3391) (root 9) 5 0) DegreeTwoThreeSpectrum5573.graph fusedMap3391swap=true := by decide +kernel
theorem certified3391swap : Certified (graph core3391) (root 9) 5 0 :=
  of_native_maps core3391 DegreeTwoThreeSpectrum6734.graph DegreeTwoThreeSpectrum5573.graph
    sourceMap3391swap fusedMap3391swap sourceMap3391swap_checked fusedMap3391swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3391
#print axioms sourceMap3391swap_checked
#print axioms fusedMap3391swap_checked
#print axioms certified3391swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
