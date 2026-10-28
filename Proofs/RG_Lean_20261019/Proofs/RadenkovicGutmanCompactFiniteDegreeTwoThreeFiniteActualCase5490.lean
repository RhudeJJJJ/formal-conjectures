/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5490 : Family 3 := level3.get ⟨3,by decide⟩
def sourceMap5490 : (Vertices 3 ⊕ Fin 2 ⊕ Fin 5) → Fin 11 :=
  fun v => ![1,4,5,6,2,3,0,7,8,9,10] (sourceLabel 3 1 4 v)
def fusedMap5490 : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10] (fusedLabel 3 1 4 v)
theorem sourceMap5490_checked : acceptsGraphIso
    (source (graph core5490) (root 3) 1 4) SmallGeFourSpectrum038.graph sourceMap5490=true := by decide +kernel
theorem fusedMap5490_checked : acceptsGraphIso
    (fused (graph core5490) (root 3) 1 4) DegreeOneSmallSpectrum175.graph fusedMap5490=true := by decide +kernel
theorem certified5490 : Certified (graph core5490) (root 3) 1 4 :=
  of_native_maps core5490 SmallGeFourSpectrum038.graph DegreeOneSmallSpectrum175.graph
    sourceMap5490 fusedMap5490 sourceMap5490_checked fusedMap5490_checked
    DegreeTwoThreeFiniteComparisons.comparison5490
#print axioms sourceMap5490_checked
#print axioms fusedMap5490_checked
#print axioms certified5490
def sourceMap5490swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,4,5,6,0,7,8,9,10,2,3] (sourceLabel 3 4 1 v)
def fusedMap5490swap : (Vertices 3 ⊕ Fin 7) → Fin 11 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10] (fusedLabel 3 4 1 v)
theorem sourceMap5490swap_checked : acceptsGraphIso
    (source (graph core5490) (root 3) 4 1) SmallGeFourSpectrum038.graph sourceMap5490swap=true := by decide +kernel
theorem fusedMap5490swap_checked : acceptsGraphIso
    (fused (graph core5490) (root 3) 4 1) DegreeOneSmallSpectrum175.graph fusedMap5490swap=true := by decide +kernel
theorem certified5490swap : Certified (graph core5490) (root 3) 4 1 :=
  of_native_maps core5490 SmallGeFourSpectrum038.graph DegreeOneSmallSpectrum175.graph
    sourceMap5490swap fusedMap5490swap sourceMap5490swap_checked fusedMap5490swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5490
#print axioms sourceMap5490swap_checked
#print axioms fusedMap5490swap_checked
#print axioms certified5490swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
