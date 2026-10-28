/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5057 : Family 4 := level4.get ⟨3,by decide⟩
def sourceMap5057 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,2,3,4,8,5,6,7,0,9,10,11,12] (sourceLabel 4 2 4 v)
def fusedMap5057 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 2 4 v)
theorem sourceMap5057_checked : acceptsGraphIso
    (source (graph core5057) (root 4) 2 4) DegreeOneSmallSpectrum1459.graph sourceMap5057=true := by decide +kernel
theorem fusedMap5057_checked : acceptsGraphIso
    (fused (graph core5057) (root 4) 2 4) DegreeOneSmallSpectrum858.graph fusedMap5057=true := by decide +kernel
theorem certified5057 : Certified (graph core5057) (root 4) 2 4 :=
  of_native_maps core5057 DegreeOneSmallSpectrum1459.graph DegreeOneSmallSpectrum858.graph
    sourceMap5057 fusedMap5057 sourceMap5057_checked fusedMap5057_checked
    DegreeTwoThreeFiniteComparisons.comparison5057
#print axioms sourceMap5057_checked
#print axioms fusedMap5057_checked
#print axioms certified5057
def sourceMap5057swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,2,3,4,8,0,9,10,11,12,5,6,7] (sourceLabel 4 4 2 v)
def fusedMap5057swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 4 2 v)
theorem sourceMap5057swap_checked : acceptsGraphIso
    (source (graph core5057) (root 4) 4 2) DegreeOneSmallSpectrum1459.graph sourceMap5057swap=true := by decide +kernel
theorem fusedMap5057swap_checked : acceptsGraphIso
    (fused (graph core5057) (root 4) 4 2) DegreeOneSmallSpectrum858.graph fusedMap5057swap=true := by decide +kernel
theorem certified5057swap : Certified (graph core5057) (root 4) 4 2 :=
  of_native_maps core5057 DegreeOneSmallSpectrum1459.graph DegreeOneSmallSpectrum858.graph
    sourceMap5057swap fusedMap5057swap sourceMap5057swap_checked fusedMap5057swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5057
#print axioms sourceMap5057swap_checked
#print axioms fusedMap5057swap_checked
#print axioms certified5057swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
