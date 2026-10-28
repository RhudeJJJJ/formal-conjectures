/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5326 : Family 3 := level3.get ⟨2,by decide⟩
def sourceMap5326 : (Vertices 3 ⊕ Fin 4 ⊕ Fin 5) → Fin 13 :=
  fun v => ![0,5,6,7,1,2,3,4,8,9,10,11,12] (sourceLabel 3 3 4 v)
def fusedMap5326 : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 3 4 v)
theorem sourceMap5326_checked : acceptsGraphIso
    (source (graph core5326) (root 3) 3 4) DegreeOneSmallSpectrum969.graph sourceMap5326=true := by decide +kernel
theorem fusedMap5326_checked : acceptsGraphIso
    (fused (graph core5326) (root 3) 3 4) DegreeOneSmallSpectrum857.graph fusedMap5326=true := by decide +kernel
theorem certified5326 : Certified (graph core5326) (root 3) 3 4 :=
  of_native_maps core5326 DegreeOneSmallSpectrum969.graph DegreeOneSmallSpectrum857.graph
    sourceMap5326 fusedMap5326 sourceMap5326_checked fusedMap5326_checked
    DegreeTwoThreeFiniteComparisons.comparison5326
#print axioms sourceMap5326_checked
#print axioms fusedMap5326_checked
#print axioms certified5326
def sourceMap5326swap : (Vertices 3 ⊕ Fin 5 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,5,6,7,8,9,10,11,12,1,2,3,4] (sourceLabel 3 4 3 v)
def fusedMap5326swap : (Vertices 3 ⊕ Fin 9) → Fin 13 :=
  fun v => ![3,4,5,6,2,1,0,7,8,9,10,11,12] (fusedLabel 3 4 3 v)
theorem sourceMap5326swap_checked : acceptsGraphIso
    (source (graph core5326) (root 3) 4 3) DegreeOneSmallSpectrum969.graph sourceMap5326swap=true := by decide +kernel
theorem fusedMap5326swap_checked : acceptsGraphIso
    (fused (graph core5326) (root 3) 4 3) DegreeOneSmallSpectrum857.graph fusedMap5326swap=true := by decide +kernel
theorem certified5326swap : Certified (graph core5326) (root 3) 4 3 :=
  of_native_maps core5326 DegreeOneSmallSpectrum969.graph DegreeOneSmallSpectrum857.graph
    sourceMap5326swap fusedMap5326swap sourceMap5326swap_checked fusedMap5326swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5326
#print axioms sourceMap5326swap_checked
#print axioms fusedMap5326swap_checked
#print axioms certified5326swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
