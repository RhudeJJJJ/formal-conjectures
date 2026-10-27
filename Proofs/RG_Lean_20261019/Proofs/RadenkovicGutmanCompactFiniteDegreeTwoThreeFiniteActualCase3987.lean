/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons79
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core3987 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap3987 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 7) → Fin 12 :=
  fun v => ![2,5,6,3,4,1,0,7,8,9,10,11] (sourceLabel 2 1 6 v)
def fusedMap3987 : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11] (fusedLabel 2 1 6 v)
theorem sourceMap3987_checked : acceptsGraphIso
    (source (graph core3987) (root 2) 1 6) DegreeOneSmallSpectrum380.graph sourceMap3987=true := by decide +kernel
theorem fusedMap3987_checked : acceptsGraphIso
    (fused (graph core3987) (root 2) 1 6) DegreeOneSmallSpectrum378.graph fusedMap3987=true := by decide +kernel
theorem certified3987 : Certified (graph core3987) (root 2) 1 6 :=
  of_native_maps core3987 DegreeOneSmallSpectrum380.graph DegreeOneSmallSpectrum378.graph
    sourceMap3987 fusedMap3987 sourceMap3987_checked fusedMap3987_checked
    DegreeTwoThreeFiniteComparisons.comparison3987
#print axioms sourceMap3987_checked
#print axioms fusedMap3987_checked
#print axioms certified3987
def sourceMap3987swap : (Vertices 2 ⊕ Fin 7 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,5,6,1,0,7,8,9,10,11,3,4] (sourceLabel 2 6 1 v)
def fusedMap3987swap : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11] (fusedLabel 2 6 1 v)
theorem sourceMap3987swap_checked : acceptsGraphIso
    (source (graph core3987) (root 2) 6 1) DegreeOneSmallSpectrum380.graph sourceMap3987swap=true := by decide +kernel
theorem fusedMap3987swap_checked : acceptsGraphIso
    (fused (graph core3987) (root 2) 6 1) DegreeOneSmallSpectrum378.graph fusedMap3987swap=true := by decide +kernel
theorem certified3987swap : Certified (graph core3987) (root 2) 6 1 :=
  of_native_maps core3987 DegreeOneSmallSpectrum380.graph DegreeOneSmallSpectrum378.graph
    sourceMap3987swap fusedMap3987swap sourceMap3987swap_checked fusedMap3987swap_checked
    DegreeTwoThreeFiniteComparisons.comparison3987
#print axioms sourceMap3987swap_checked
#print axioms fusedMap3987swap_checked
#print axioms certified3987swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
