/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3372 : Family 9 := level9.get ⟨429,by decide⟩
def sourceMap3372 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3372 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3372_checked : acceptsGraphIso
    (source (graph core3372) (root 9) 0 5) DegreeTwoThreeSpectrum6544.graph sourceMap3372=true := by decide +kernel
theorem fusedMap3372_checked : acceptsGraphIso
    (fused (graph core3372) (root 9) 0 5) DegreeTwoThreeSpectrum5444.graph fusedMap3372=true := by decide +kernel
theorem certified3372 : Certified (graph core3372) (root 9) 0 5 :=
  of_native_maps core3372 DegreeTwoThreeSpectrum6544.graph DegreeTwoThreeSpectrum5444.graph
    sourceMap3372 fusedMap3372 sourceMap3372_checked fusedMap3372_checked
    DegreeTwoThreeFiniteComparisons.comparison3372
#print axioms sourceMap3372_checked
#print axioms fusedMap3372_checked
#print axioms certified3372
def sourceMap3372swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3372swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3372swap_checked : acceptsGraphIso
    (source (graph core3372) (root 9) 5 0) DegreeTwoThreeSpectrum6544.graph sourceMap3372swap=true := by decide +kernel
theorem fusedMap3372swap_checked : acceptsGraphIso
    (fused (graph core3372) (root 9) 5 0) DegreeTwoThreeSpectrum5444.graph fusedMap3372swap=true := by decide +kernel
theorem certified3372swap : Certified (graph core3372) (root 9) 5 0 :=
  of_native_maps core3372 DegreeTwoThreeSpectrum6544.graph DegreeTwoThreeSpectrum5444.graph
    sourceMap3372swap fusedMap3372swap sourceMap3372swap_checked fusedMap3372swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3372
#print axioms sourceMap3372swap_checked
#print axioms fusedMap3372swap_checked
#print axioms certified3372swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
