/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3359 : Family 9 := level9.get ⟨396,by decide⟩
def sourceMap3359 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3359 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3359_checked : acceptsGraphIso
    (source (graph core3359) (root 9) 0 5) DegreeTwoThreeSpectrum6380.graph sourceMap3359=true := by decide +kernel
theorem fusedMap3359_checked : acceptsGraphIso
    (fused (graph core3359) (root 9) 0 5) DegreeTwoThreeSpectrum5319.graph fusedMap3359=true := by decide +kernel
theorem certified3359 : Certified (graph core3359) (root 9) 0 5 :=
  of_native_maps core3359 DegreeTwoThreeSpectrum6380.graph DegreeTwoThreeSpectrum5319.graph
    sourceMap3359 fusedMap3359 sourceMap3359_checked fusedMap3359_checked
    DegreeTwoThreeFiniteComparisons.comparison3359
#print axioms sourceMap3359_checked
#print axioms fusedMap3359_checked
#print axioms certified3359
def sourceMap3359swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3359swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3359swap_checked : acceptsGraphIso
    (source (graph core3359) (root 9) 5 0) DegreeTwoThreeSpectrum6380.graph sourceMap3359swap=true := by decide +kernel
theorem fusedMap3359swap_checked : acceptsGraphIso
    (fused (graph core3359) (root 9) 5 0) DegreeTwoThreeSpectrum5319.graph fusedMap3359swap=true := by decide +kernel
theorem certified3359swap : Certified (graph core3359) (root 9) 5 0 :=
  of_native_maps core3359 DegreeTwoThreeSpectrum6380.graph DegreeTwoThreeSpectrum5319.graph
    sourceMap3359swap fusedMap3359swap sourceMap3359swap_checked fusedMap3359swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3359
#print axioms sourceMap3359swap_checked
#print axioms fusedMap3359swap_checked
#print axioms certified3359swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
