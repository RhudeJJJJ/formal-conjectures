/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3380 : Family 9 := level9.get ⟨449,by decide⟩
def sourceMap3380 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3380 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3380_checked : acceptsGraphIso
    (source (graph core3380) (root 9) 0 5) DegreeTwoThreeSpectrum6637.graph sourceMap3380=true := by decide +kernel
theorem fusedMap3380_checked : acceptsGraphIso
    (fused (graph core3380) (root 9) 0 5) DegreeTwoThreeSpectrum5502.graph fusedMap3380=true := by decide +kernel
theorem certified3380 : Certified (graph core3380) (root 9) 0 5 :=
  of_native_maps core3380 DegreeTwoThreeSpectrum6637.graph DegreeTwoThreeSpectrum5502.graph
    sourceMap3380 fusedMap3380 sourceMap3380_checked fusedMap3380_checked
    DegreeTwoThreeFiniteComparisons.comparison3380
#print axioms sourceMap3380_checked
#print axioms fusedMap3380_checked
#print axioms certified3380
def sourceMap3380swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3380swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3380swap_checked : acceptsGraphIso
    (source (graph core3380) (root 9) 5 0) DegreeTwoThreeSpectrum6637.graph sourceMap3380swap=true := by decide +kernel
theorem fusedMap3380swap_checked : acceptsGraphIso
    (fused (graph core3380) (root 9) 5 0) DegreeTwoThreeSpectrum5502.graph fusedMap3380swap=true := by decide +kernel
theorem certified3380swap : Certified (graph core3380) (root 9) 5 0 :=
  of_native_maps core3380 DegreeTwoThreeSpectrum6637.graph DegreeTwoThreeSpectrum5502.graph
    sourceMap3380swap fusedMap3380swap sourceMap3380swap_checked fusedMap3380swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3380
#print axioms sourceMap3380swap_checked
#print axioms fusedMap3380swap_checked
#print axioms certified3380swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
