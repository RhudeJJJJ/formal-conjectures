/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3430 : Family 9 := level9.get ⟨567,by decide⟩
def sourceMap3430 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3430 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3430_checked : acceptsGraphIso
    (source (graph core3430) (root 9) 0 5) DegreeTwoThreeSpectrum6064.graph sourceMap3430=true := by decide +kernel
theorem fusedMap3430_checked : acceptsGraphIso
    (fused (graph core3430) (root 9) 0 5) DegreeTwoThreeSpectrum6065.graph fusedMap3430=true := by decide +kernel
theorem certified3430 : Certified (graph core3430) (root 9) 0 5 :=
  of_native_maps core3430 DegreeTwoThreeSpectrum6064.graph DegreeTwoThreeSpectrum6065.graph
    sourceMap3430 fusedMap3430 sourceMap3430_checked fusedMap3430_checked
    DegreeTwoThreeFiniteComparisons.comparison3430
#print axioms sourceMap3430_checked
#print axioms fusedMap3430_checked
#print axioms certified3430
def sourceMap3430swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3430swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3430swap_checked : acceptsGraphIso
    (source (graph core3430) (root 9) 5 0) DegreeTwoThreeSpectrum6064.graph sourceMap3430swap=true := by decide +kernel
theorem fusedMap3430swap_checked : acceptsGraphIso
    (fused (graph core3430) (root 9) 5 0) DegreeTwoThreeSpectrum6065.graph fusedMap3430swap=true := by decide +kernel
theorem certified3430swap : Certified (graph core3430) (root 9) 5 0 :=
  of_native_maps core3430 DegreeTwoThreeSpectrum6064.graph DegreeTwoThreeSpectrum6065.graph
    sourceMap3430swap fusedMap3430swap sourceMap3430swap_checked fusedMap3430swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3430
#print axioms sourceMap3430swap_checked
#print axioms fusedMap3430swap_checked
#print axioms certified3430swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
