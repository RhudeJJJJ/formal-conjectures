/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons109
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5487 : Family 4 := level4.get ⟨7,by decide⟩
def sourceMap5487 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (sourceLabel 4 0 6 v)
def fusedMap5487 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 0 6 v)
theorem sourceMap5487_checked : acceptsGraphIso
    (source (graph core5487) (root 4) 0 6) DegreeOneSmallSpectrum916.graph sourceMap5487=true := by decide +kernel
theorem fusedMap5487_checked : acceptsGraphIso
    (fused (graph core5487) (root 4) 0 6) DegreeOneSmallSpectrum922.graph fusedMap5487=true := by decide +kernel
theorem certified5487 : Certified (graph core5487) (root 4) 0 6 :=
  of_native_maps core5487 DegreeOneSmallSpectrum916.graph DegreeOneSmallSpectrum922.graph
    sourceMap5487 fusedMap5487 sourceMap5487_checked fusedMap5487_checked
    DegreeTwoThreeFiniteComparisons.comparison5487
#print axioms sourceMap5487_checked
#print axioms fusedMap5487_checked
#print axioms certified5487
def sourceMap5487swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,11,12,7] (sourceLabel 4 6 0 v)
def fusedMap5487swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 6 0 v)
theorem sourceMap5487swap_checked : acceptsGraphIso
    (source (graph core5487) (root 4) 6 0) DegreeOneSmallSpectrum916.graph sourceMap5487swap=true := by decide +kernel
theorem fusedMap5487swap_checked : acceptsGraphIso
    (fused (graph core5487) (root 4) 6 0) DegreeOneSmallSpectrum922.graph fusedMap5487swap=true := by decide +kernel
theorem certified5487swap : Certified (graph core5487) (root 4) 6 0 :=
  of_native_maps core5487 DegreeOneSmallSpectrum916.graph DegreeOneSmallSpectrum922.graph
    sourceMap5487swap fusedMap5487swap sourceMap5487swap_checked fusedMap5487swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5487
#print axioms sourceMap5487swap_checked
#print axioms fusedMap5487swap_checked
#print axioms certified5487swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
