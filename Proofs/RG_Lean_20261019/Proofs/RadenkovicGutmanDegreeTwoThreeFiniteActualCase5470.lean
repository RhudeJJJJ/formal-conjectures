/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5470 : Family 4 := level4.get ⟨7,by decide⟩
def sourceMap5470 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,2,3,4,5,6,0,7,8,9,10] (sourceLabel 4 0 4 v)
def fusedMap5470 : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 0 4 v)
theorem sourceMap5470_checked : acceptsGraphIso
    (source (graph core5470) (root 4) 0 4) SmallGeFourSpectrum038.graph sourceMap5470=true := by decide +kernel
theorem fusedMap5470_checked : acceptsGraphIso
    (fused (graph core5470) (root 4) 0 4) DegreeOneSmallSpectrum207.graph fusedMap5470=true := by decide +kernel
theorem certified5470 : Certified (graph core5470) (root 4) 0 4 :=
  of_native_maps core5470 SmallGeFourSpectrum038.graph DegreeOneSmallSpectrum207.graph
    sourceMap5470 fusedMap5470 sourceMap5470_checked fusedMap5470_checked
    DegreeTwoThreeFiniteComparisons.comparison5470
#print axioms sourceMap5470_checked
#print axioms fusedMap5470_checked
#print axioms certified5470
def sourceMap5470swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,2,3,4,5,0,7,8,9,10,6] (sourceLabel 4 4 0 v)
def fusedMap5470swap : (Vertices 4 ⊕ Fin 6) → Fin 11 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10] (fusedLabel 4 4 0 v)
theorem sourceMap5470swap_checked : acceptsGraphIso
    (source (graph core5470) (root 4) 4 0) SmallGeFourSpectrum038.graph sourceMap5470swap=true := by decide +kernel
theorem fusedMap5470swap_checked : acceptsGraphIso
    (fused (graph core5470) (root 4) 4 0) DegreeOneSmallSpectrum207.graph fusedMap5470swap=true := by decide +kernel
theorem certified5470swap : Certified (graph core5470) (root 4) 4 0 :=
  of_native_maps core5470 SmallGeFourSpectrum038.graph DegreeOneSmallSpectrum207.graph
    sourceMap5470swap fusedMap5470swap sourceMap5470swap_checked fusedMap5470swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5470
#print axioms sourceMap5470swap_checked
#print axioms fusedMap5470swap_checked
#print axioms certified5470swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
