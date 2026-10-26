/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3632 : Family 8 := level8.get ⟨266,by decide⟩
def sourceMap3632 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3632 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3632_checked : acceptsGraphIso
    (source (graph core3632) (root 8) 0 6) DegreeTwoThreeSpectrum5972.graph sourceMap3632=true := by decide +kernel
theorem fusedMap3632_checked : acceptsGraphIso
    (fused (graph core3632) (root 8) 0 6) DegreeTwoThreeSpectrum5974.graph fusedMap3632=true := by decide +kernel
theorem certified3632 : Certified (graph core3632) (root 8) 0 6 :=
  of_native_maps core3632 DegreeTwoThreeSpectrum5972.graph DegreeTwoThreeSpectrum5974.graph
    sourceMap3632 fusedMap3632 sourceMap3632_checked fusedMap3632_checked
    DegreeTwoThreeFiniteComparisons.comparison3632
#print axioms sourceMap3632_checked
#print axioms fusedMap3632_checked
#print axioms certified3632
def sourceMap3632swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3632swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3632swap_checked : acceptsGraphIso
    (source (graph core3632) (root 8) 6 0) DegreeTwoThreeSpectrum5972.graph sourceMap3632swap=true := by decide +kernel
theorem fusedMap3632swap_checked : acceptsGraphIso
    (fused (graph core3632) (root 8) 6 0) DegreeTwoThreeSpectrum5974.graph fusedMap3632swap=true := by decide +kernel
theorem certified3632swap : Certified (graph core3632) (root 8) 6 0 :=
  of_native_maps core3632 DegreeTwoThreeSpectrum5972.graph DegreeTwoThreeSpectrum5974.graph
    sourceMap3632swap fusedMap3632swap sourceMap3632swap_checked fusedMap3632swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3632
#print axioms sourceMap3632swap_checked
#print axioms fusedMap3632swap_checked
#print axioms certified3632swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
