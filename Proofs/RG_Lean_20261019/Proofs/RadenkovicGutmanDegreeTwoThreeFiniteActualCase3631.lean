/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons72
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3631 : Family 8 := level8.get ⟨265,by decide⟩
def sourceMap3631 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 7) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,11,1,0,12,13,14,15,16] (sourceLabel 8 0 6 v)
def fusedMap3631 : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 0 6 v)
theorem sourceMap3631_checked : acceptsGraphIso
    (source (graph core3631) (root 8) 0 6) DegreeTwoThreeSpectrum5963.graph sourceMap3631=true := by decide +kernel
theorem fusedMap3631_checked : acceptsGraphIso
    (fused (graph core3631) (root 8) 0 6) DegreeTwoThreeSpectrum5965.graph fusedMap3631=true := by decide +kernel
theorem certified3631 : Certified (graph core3631) (root 8) 0 6 :=
  of_native_maps core3631 DegreeTwoThreeSpectrum5963.graph DegreeTwoThreeSpectrum5965.graph
    sourceMap3631 fusedMap3631 sourceMap3631_checked fusedMap3631_checked
    DegreeTwoThreeFiniteComparisons.comparison3631
#print axioms sourceMap3631_checked
#print axioms fusedMap3631_checked
#print axioms certified3631
def sourceMap3631swap : (Vertices 8 ⊕ Fin 7 ⊕ Fin 1) → Fin 17 :=
  fun v => ![2,3,4,5,6,7,8,9,10,1,0,12,13,14,15,16,11] (sourceLabel 8 6 0 v)
def fusedMap3631swap : (Vertices 8 ⊕ Fin 8) → Fin 17 :=
  fun v => ![3,4,5,6,7,8,9,10,11,2,1,0,12,13,14,15,16] (fusedLabel 8 6 0 v)
theorem sourceMap3631swap_checked : acceptsGraphIso
    (source (graph core3631) (root 8) 6 0) DegreeTwoThreeSpectrum5963.graph sourceMap3631swap=true := by decide +kernel
theorem fusedMap3631swap_checked : acceptsGraphIso
    (fused (graph core3631) (root 8) 6 0) DegreeTwoThreeSpectrum5965.graph fusedMap3631swap=true := by decide +kernel
theorem certified3631swap : Certified (graph core3631) (root 8) 6 0 :=
  of_native_maps core3631 DegreeTwoThreeSpectrum5963.graph DegreeTwoThreeSpectrum5965.graph
    sourceMap3631swap fusedMap3631swap sourceMap3631swap_checked fusedMap3631swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3631
#print axioms sourceMap3631swap_checked
#print axioms fusedMap3631swap_checked
#print axioms certified3631swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
