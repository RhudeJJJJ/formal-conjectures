/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3619 : Family 8 := level8.get ⟨231,by decide⟩
def sourceMap3619 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3619 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3619_checked : acceptsGraphIso
    (source (graph core3619) (root 8) 0 6) DegreeTwoThreeSpectrum6479.graph sourceMap3619=true := by decide +kernel
theorem fusedMap3619_checked : acceptsGraphIso
    (fused (graph core3619) (root 8) 0 6) DegreeTwoThreeSpectrum5421.graph fusedMap3619=true := by decide +kernel
theorem certified3619 : Certified (graph core3619) (root 8) 0 6 :=
  of_native_maps core3619 DegreeTwoThreeSpectrum6479.graph DegreeTwoThreeSpectrum5421.graph
    sourceMap3619 fusedMap3619 sourceMap3619_checked fusedMap3619_checked
    DegreeTwoThreeFiniteComparisons.comparison3619
#print axioms sourceMap3619_checked
#print axioms fusedMap3619_checked
#print axioms certified3619
def sourceMap3619swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3619swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3619swap_checked : acceptsGraphIso
    (source (graph core3619) (root 8) 6 0) DegreeTwoThreeSpectrum6479.graph sourceMap3619swap=true := by decide +kernel
theorem fusedMap3619swap_checked : acceptsGraphIso
    (fused (graph core3619) (root 8) 6 0) DegreeTwoThreeSpectrum5421.graph fusedMap3619swap=true := by decide +kernel
theorem certified3619swap : Certified (graph core3619) (root 8) 6 0 :=
  of_native_maps core3619 DegreeTwoThreeSpectrum6479.graph DegreeTwoThreeSpectrum5421.graph
    sourceMap3619swap fusedMap3619swap sourceMap3619swap_checked fusedMap3619swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3619
#print axioms sourceMap3619swap_checked
#print axioms fusedMap3619swap_checked
#print axioms certified3619swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
