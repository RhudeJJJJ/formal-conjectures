/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons78
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3912 : Family 8 := level8.get ⟨241,by decide⟩
def sourceMap3912 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 5) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,9,10,0,12,13,14,15] (sourceLabel 8 1 4 v)
def fusedMap3912 : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 1 4 v)
theorem sourceMap3912_checked : acceptsGraphIso
    (source (graph core3912) (root 8) 1 4) DegreeTwoThreeSpectrum4815.graph sourceMap3912=true := by decide +kernel
theorem fusedMap3912_checked : acceptsGraphIso
    (fused (graph core3912) (root 8) 1 4) DegreeTwoThreeSpectrum4442.graph fusedMap3912=true := by decide +kernel
theorem certified3912 : Certified (graph core3912) (root 8) 1 4 :=
  of_native_maps core3912 DegreeTwoThreeSpectrum4815.graph DegreeTwoThreeSpectrum4442.graph
    sourceMap3912 fusedMap3912 sourceMap3912_checked fusedMap3912_checked
    DegreeTwoThreeFiniteComparisons.comparison3912
#print axioms sourceMap3912_checked
#print axioms fusedMap3912_checked
#print axioms certified3912
def sourceMap3912swap : (Vertices 8 ⊕ Fin 5 ⊕ Fin 2) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,11,0,12,13,14,15,9,10] (sourceLabel 8 4 1 v)
def fusedMap3912swap : (Vertices 8 ⊕ Fin 7) → Fin 16 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,11,12,13,14,15] (fusedLabel 8 4 1 v)
theorem sourceMap3912swap_checked : acceptsGraphIso
    (source (graph core3912) (root 8) 4 1) DegreeTwoThreeSpectrum4815.graph sourceMap3912swap=true := by decide +kernel
theorem fusedMap3912swap_checked : acceptsGraphIso
    (fused (graph core3912) (root 8) 4 1) DegreeTwoThreeSpectrum4442.graph fusedMap3912swap=true := by decide +kernel
theorem certified3912swap : Certified (graph core3912) (root 8) 4 1 :=
  of_native_maps core3912 DegreeTwoThreeSpectrum4815.graph DegreeTwoThreeSpectrum4442.graph
    sourceMap3912swap fusedMap3912swap sourceMap3912swap_checked fusedMap3912swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3912
#print axioms sourceMap3912swap_checked
#print axioms fusedMap3912swap_checked
#print axioms certified3912swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
