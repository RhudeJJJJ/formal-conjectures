/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3662 : Family 7 := level7.get ⟨6,by decide⟩
def sourceMap3662 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3662 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3662_checked : acceptsGraphIso
    (source (graph core3662) (root 7) 0 7) DegreeTwoThreeSpectrum5130.graph sourceMap3662=true := by decide +kernel
theorem fusedMap3662_checked : acceptsGraphIso
    (fused (graph core3662) (root 7) 0 7) DegreeTwoThreeSpectrum4964.graph fusedMap3662=true := by decide +kernel
theorem certified3662 : Certified (graph core3662) (root 7) 0 7 :=
  of_native_maps core3662 DegreeTwoThreeSpectrum5130.graph DegreeTwoThreeSpectrum4964.graph
    sourceMap3662 fusedMap3662 sourceMap3662_checked fusedMap3662_checked
    DegreeTwoThreeFiniteComparisons.comparison3662
#print axioms sourceMap3662_checked
#print axioms fusedMap3662_checked
#print axioms certified3662
def sourceMap3662swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,0,10,11,12,13,14,15,16,9] (sourceLabel 7 7 0 v)
def fusedMap3662swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,0,9,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3662swap_checked : acceptsGraphIso
    (source (graph core3662) (root 7) 7 0) DegreeTwoThreeSpectrum5130.graph sourceMap3662swap=true := by decide +kernel
theorem fusedMap3662swap_checked : acceptsGraphIso
    (fused (graph core3662) (root 7) 7 0) DegreeTwoThreeSpectrum4964.graph fusedMap3662swap=true := by decide +kernel
theorem certified3662swap : Certified (graph core3662) (root 7) 7 0 :=
  of_native_maps core3662 DegreeTwoThreeSpectrum5130.graph DegreeTwoThreeSpectrum4964.graph
    sourceMap3662swap fusedMap3662swap sourceMap3662swap_checked fusedMap3662swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3662
#print axioms sourceMap3662swap_checked
#print axioms fusedMap3662swap_checked
#print axioms certified3662swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
