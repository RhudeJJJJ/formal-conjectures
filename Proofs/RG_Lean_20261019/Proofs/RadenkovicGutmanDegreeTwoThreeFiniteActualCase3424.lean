/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons68
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3424 : Family 9 := level9.get ⟨554,by decide⟩
def sourceMap3424 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (sourceLabel 9 0 5 v)
def fusedMap3424 : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 0 5 v)
theorem sourceMap3424_checked : acceptsGraphIso
    (source (graph core3424) (root 9) 0 5) DegreeTwoThreeSpectrum6006.graph sourceMap3424=true := by decide +kernel
theorem fusedMap3424_checked : acceptsGraphIso
    (fused (graph core3424) (root 9) 0 5) DegreeTwoThreeSpectrum6007.graph fusedMap3424=true := by decide +kernel
theorem certified3424 : Certified (graph core3424) (root 9) 0 5 :=
  of_native_maps core3424 DegreeTwoThreeSpectrum6006.graph DegreeTwoThreeSpectrum6007.graph
    sourceMap3424 fusedMap3424 sourceMap3424_checked fusedMap3424_checked
    DegreeTwoThreeFiniteComparisons.comparison3424
#print axioms sourceMap3424_checked
#print axioms fusedMap3424_checked
#print axioms certified3424
def sourceMap3424swap : (Vertices 9 ⊕ Fin 6 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,12,13,14,15,16,11] (sourceLabel 9 5 0 v)
def fusedMap3424swap : (Vertices 9 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (fusedLabel 9 5 0 v)
theorem sourceMap3424swap_checked : acceptsGraphIso
    (source (graph core3424) (root 9) 5 0) DegreeTwoThreeSpectrum6006.graph sourceMap3424swap=true := by decide +kernel
theorem fusedMap3424swap_checked : acceptsGraphIso
    (fused (graph core3424) (root 9) 5 0) DegreeTwoThreeSpectrum6007.graph fusedMap3424swap=true := by decide +kernel
theorem certified3424swap : Certified (graph core3424) (root 9) 5 0 :=
  of_native_maps core3424 DegreeTwoThreeSpectrum6006.graph DegreeTwoThreeSpectrum6007.graph
    sourceMap3424swap fusedMap3424swap sourceMap3424swap_checked fusedMap3424swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3424
#print axioms sourceMap3424swap_checked
#print axioms fusedMap3424swap_checked
#print axioms certified3424swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
