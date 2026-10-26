/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons73
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3668 : Family 7 := level7.get ⟨29,by decide⟩
def sourceMap3668 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 8) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15,16] (sourceLabel 7 0 7 v)
def fusedMap3668 : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 0 7 v)
theorem sourceMap3668_checked : acceptsGraphIso
    (source (graph core3668) (root 7) 0 7) DegreeTwoThreeSpectrum5207.graph sourceMap3668=true := by decide +kernel
theorem fusedMap3668_checked : acceptsGraphIso
    (fused (graph core3668) (root 7) 0 7) DegreeTwoThreeSpectrum4968.graph fusedMap3668=true := by decide +kernel
theorem certified3668 : Certified (graph core3668) (root 7) 0 7 :=
  of_native_maps core3668 DegreeTwoThreeSpectrum5207.graph DegreeTwoThreeSpectrum4968.graph
    sourceMap3668 fusedMap3668 sourceMap3668_checked fusedMap3668_checked
    DegreeTwoThreeFiniteComparisons.comparison3668
#print axioms sourceMap3668_checked
#print axioms fusedMap3668_checked
#print axioms certified3668
def sourceMap3668swap : (Vertices 7 ⊕ Fin 8 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,16,10] (sourceLabel 7 7 0 v)
def fusedMap3668swap : (Vertices 7 ⊕ Fin 9) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15,16] (fusedLabel 7 7 0 v)
theorem sourceMap3668swap_checked : acceptsGraphIso
    (source (graph core3668) (root 7) 7 0) DegreeTwoThreeSpectrum5207.graph sourceMap3668swap=true := by decide +kernel
theorem fusedMap3668swap_checked : acceptsGraphIso
    (fused (graph core3668) (root 7) 7 0) DegreeTwoThreeSpectrum4968.graph fusedMap3668swap=true := by decide +kernel
theorem certified3668swap : Certified (graph core3668) (root 7) 7 0 :=
  of_native_maps core3668 DegreeTwoThreeSpectrum5207.graph DegreeTwoThreeSpectrum4968.graph
    sourceMap3668swap fusedMap3668swap sourceMap3668swap_checked fusedMap3668swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3668
#print axioms sourceMap3668swap_checked
#print axioms fusedMap3668swap_checked
#print axioms certified3668swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
