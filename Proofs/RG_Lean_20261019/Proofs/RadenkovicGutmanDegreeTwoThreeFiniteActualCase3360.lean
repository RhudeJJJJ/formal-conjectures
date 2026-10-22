/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons67
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3360 : Family 9 := level9.get ⟨399,by decide⟩
def sourceMap3360 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3360 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3360_checked : acceptsGraphIso
    (source (graph core3360) (root 9) 0 5) DegreeTwoThreeSpectrum6388.graph sourceMap3360=true := by decide +kernel
theorem fusedMap3360_checked : acceptsGraphIso
    (fused (graph core3360) (root 9) 0 5) DegreeTwoThreeSpectrum5328.graph fusedMap3360=true := by decide +kernel
theorem certified3360 : Certified (graph core3360) (root 9) 0 5 :=
  of_native_maps core3360 DegreeTwoThreeSpectrum6388.graph DegreeTwoThreeSpectrum5328.graph
    sourceMap3360 fusedMap3360 sourceMap3360_checked fusedMap3360_checked
    DegreeTwoThreeFiniteComparisons.comparison3360
#print axioms sourceMap3360_checked
#print axioms fusedMap3360_checked
#print axioms certified3360
def sourceMap3360swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3360swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3360swap_checked : acceptsGraphIso
    (source (graph core3360) (root 9) 5 0) DegreeTwoThreeSpectrum6388.graph sourceMap3360swap=true := by decide +kernel
theorem fusedMap3360swap_checked : acceptsGraphIso
    (fused (graph core3360) (root 9) 5 0) DegreeTwoThreeSpectrum5328.graph fusedMap3360swap=true := by decide +kernel
theorem certified3360swap : Certified (graph core3360) (root 9) 5 0 :=
  of_native_maps core3360 DegreeTwoThreeSpectrum6388.graph DegreeTwoThreeSpectrum5328.graph
    sourceMap3360swap fusedMap3360swap sourceMap3360swap_checked fusedMap3360swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3360
#print axioms sourceMap3360swap_checked
#print axioms fusedMap3360swap_checked
#print axioms certified3360swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
