/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons104
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5216 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5216 : (Vertices 3 ⊕ Fin 3 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,5,6,7,2,3,4,0,8,9,10,11,12] (sourceLabel 3 2 5 v)
def fusedMap5216 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 2 5 v)
theorem sourceMap5216_checked : acceptsGraphIso
    (source (graph core5216) (root 3) 2 5) DegreeOneSmallSpectrum947.graph sourceMap5216=true := by decide +kernel
theorem fusedMap5216_checked : acceptsGraphIso
    (fused (graph core5216) (root 3) 2 5) DegreeOneSmallSpectrum857.graph fusedMap5216=true := by decide +kernel
theorem certified5216 : Certified (graph core5216) (root 3) 2 5 :=
  of_native_maps core5216 DegreeOneSmallSpectrum947.graph DegreeOneSmallSpectrum857.graph
    sourceMap5216 fusedMap5216 sourceMap5216_checked fusedMap5216_checked
    DegreeTwoThreeFiniteComparisons.comparison5216
#print axioms sourceMap5216_checked
#print axioms fusedMap5216_checked
#print axioms certified5216
def sourceMap5216swap : (Vertices 3 ⊕ Fin 6 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,5,6,7,0,8,9,10,11,12,2,3,4] (sourceLabel 3 5 2 v)
def fusedMap5216swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 5 2 v)
theorem sourceMap5216swap_checked : acceptsGraphIso
    (source (graph core5216) (root 3) 5 2) DegreeOneSmallSpectrum947.graph sourceMap5216swap=true := by decide +kernel
theorem fusedMap5216swap_checked : acceptsGraphIso
    (fused (graph core5216) (root 3) 5 2) DegreeOneSmallSpectrum857.graph fusedMap5216swap=true := by decide +kernel
theorem certified5216swap : Certified (graph core5216) (root 3) 5 2 :=
  of_native_maps core5216 DegreeOneSmallSpectrum947.graph DegreeOneSmallSpectrum857.graph
    sourceMap5216swap fusedMap5216swap sourceMap5216swap_checked fusedMap5216swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5216
#print axioms sourceMap5216swap_checked
#print axioms fusedMap5216swap_checked
#print axioms certified5216swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
