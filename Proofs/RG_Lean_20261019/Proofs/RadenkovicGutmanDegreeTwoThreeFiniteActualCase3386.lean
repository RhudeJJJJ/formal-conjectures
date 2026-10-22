/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3386 : Family 9 := level9.get ⟨463,by decide⟩
def sourceMap3386 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3386 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3386_checked : acceptsGraphIso
    (source (graph core3386) (root 9) 0 5) DegreeTwoThreeSpectrum6695.graph sourceMap3386=true := by decide +kernel
theorem fusedMap3386_checked : acceptsGraphIso
    (fused (graph core3386) (root 9) 0 5) DegreeTwoThreeSpectrum5547.graph fusedMap3386=true := by decide +kernel
theorem certified3386 : Certified (graph core3386) (root 9) 0 5 :=
  of_native_maps core3386 DegreeTwoThreeSpectrum6695.graph DegreeTwoThreeSpectrum5547.graph
    sourceMap3386 fusedMap3386 sourceMap3386_checked fusedMap3386_checked
    DegreeTwoThreeFiniteComparisons.comparison3386
#print axioms sourceMap3386_checked
#print axioms fusedMap3386_checked
#print axioms certified3386
def sourceMap3386swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3386swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3386swap_checked : acceptsGraphIso
    (source (graph core3386) (root 9) 5 0) DegreeTwoThreeSpectrum6695.graph sourceMap3386swap=true := by decide +kernel
theorem fusedMap3386swap_checked : acceptsGraphIso
    (fused (graph core3386) (root 9) 5 0) DegreeTwoThreeSpectrum5547.graph fusedMap3386swap=true := by decide +kernel
theorem certified3386swap : Certified (graph core3386) (root 9) 5 0 :=
  of_native_maps core3386 DegreeTwoThreeSpectrum6695.graph DegreeTwoThreeSpectrum5547.graph
    sourceMap3386swap fusedMap3386swap sourceMap3386swap_checked fusedMap3386swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3386
#print axioms sourceMap3386swap_checked
#print axioms fusedMap3386swap_checked
#print axioms certified3386swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
