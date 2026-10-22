/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons70
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3532 : Family 7 := level7.get ⟨88,by decide⟩
def sourceMap3532 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (sourceLabel 7 0 6 v)
def fusedMap3532 : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 0 6 v)
theorem sourceMap3532_checked : acceptsGraphIso
    (source (graph core3532) (root 7) 0 6) DegreeTwoThreeSpectrum4463.graph sourceMap3532=true := by decide +kernel
theorem fusedMap3532_checked : acceptsGraphIso
    (fused (graph core3532) (root 7) 0 6) DegreeTwoThreeSpectrum4004.graph fusedMap3532=true := by decide +kernel
theorem certified3532 : Certified (graph core3532) (root 7) 0 6 :=
  of_native_maps core3532 DegreeTwoThreeSpectrum4463.graph DegreeTwoThreeSpectrum4004.graph
    sourceMap3532 fusedMap3532 sourceMap3532_checked fusedMap3532_checked
    DegreeTwoThreeFiniteComparisons.comparison3532
#print axioms sourceMap3532_checked
#print axioms fusedMap3532_checked
#print axioms certified3532
def sourceMap3532swap : (Vertices 7 ⊕ Fin 7 ⊕ Fin 1) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,11,12,13,14,15,10] (sourceLabel 7 6 0 v)
def fusedMap3532swap : (Vertices 7 ⊕ Fin 8) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,1,0,10,11,12,13,14,15] (fusedLabel 7 6 0 v)
theorem sourceMap3532swap_checked : acceptsGraphIso
    (source (graph core3532) (root 7) 6 0) DegreeTwoThreeSpectrum4463.graph sourceMap3532swap=true := by decide +kernel
theorem fusedMap3532swap_checked : acceptsGraphIso
    (fused (graph core3532) (root 7) 6 0) DegreeTwoThreeSpectrum4004.graph fusedMap3532swap=true := by decide +kernel
theorem certified3532swap : Certified (graph core3532) (root 7) 6 0 :=
  of_native_maps core3532 DegreeTwoThreeSpectrum4463.graph DegreeTwoThreeSpectrum4004.graph
    sourceMap3532swap fusedMap3532swap sourceMap3532swap_checked fusedMap3532swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3532
#print axioms sourceMap3532swap_checked
#print axioms fusedMap3532swap_checked
#print axioms certified3532swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
