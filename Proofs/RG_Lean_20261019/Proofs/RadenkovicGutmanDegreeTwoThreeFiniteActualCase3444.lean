/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3444 : Family 9 := level9.get ⟨597,by decide⟩
def sourceMap3444 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3444 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3444_checked : acceptsGraphIso
    (source (graph core3444) (root 9) 0 5) DegreeTwoThreeSpectrum6218.graph sourceMap3444=true := by decide +kernel
theorem fusedMap3444_checked : acceptsGraphIso
    (fused (graph core3444) (root 9) 0 5) DegreeTwoThreeSpectrum6219.graph fusedMap3444=true := by decide +kernel
theorem certified3444 : Certified (graph core3444) (root 9) 0 5 :=
  of_native_maps core3444 DegreeTwoThreeSpectrum6218.graph DegreeTwoThreeSpectrum6219.graph
    sourceMap3444 fusedMap3444 sourceMap3444_checked fusedMap3444_checked
    DegreeTwoThreeFiniteComparisons.comparison3444
#print axioms sourceMap3444_checked
#print axioms fusedMap3444_checked
#print axioms certified3444
def sourceMap3444swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3444swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3444swap_checked : acceptsGraphIso
    (source (graph core3444) (root 9) 5 0) DegreeTwoThreeSpectrum6218.graph sourceMap3444swap=true := by decide +kernel
theorem fusedMap3444swap_checked : acceptsGraphIso
    (fused (graph core3444) (root 9) 5 0) DegreeTwoThreeSpectrum6219.graph fusedMap3444swap=true := by decide +kernel
theorem certified3444swap : Certified (graph core3444) (root 9) 5 0 :=
  of_native_maps core3444 DegreeTwoThreeSpectrum6218.graph DegreeTwoThreeSpectrum6219.graph
    sourceMap3444swap fusedMap3444swap sourceMap3444swap_checked fusedMap3444swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3444
#print axioms sourceMap3444swap_checked
#print axioms fusedMap3444swap_checked
#print axioms certified3444swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
