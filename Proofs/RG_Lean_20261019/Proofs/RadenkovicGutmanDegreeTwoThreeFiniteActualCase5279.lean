/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons105
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5279 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5279 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,6,7,3,4,5,1,0,8,9,10,11,12] (sourceLabel 2 2 6 v)
def fusedMap5279 : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 2 6 v)
theorem sourceMap5279_checked : acceptsGraphIso
    (source (graph core5279) (root 2) 2 6) DegreeOneSmallSpectrum956.graph sourceMap5279=true := by decide +kernel
theorem fusedMap5279_checked : acceptsGraphIso
    (fused (graph core5279) (root 2) 2 6) DegreeOneSmallSpectrum856.graph fusedMap5279=true := by decide +kernel
theorem certified5279 : Certified (graph core5279) (root 2) 2 6 :=
  of_native_maps core5279 DegreeOneSmallSpectrum956.graph DegreeOneSmallSpectrum856.graph
    sourceMap5279 fusedMap5279 sourceMap5279_checked fusedMap5279_checked
    DegreeTwoThreeFiniteComparisons.comparison5279
#print axioms sourceMap5279_checked
#print axioms fusedMap5279_checked
#print axioms certified5279
def sourceMap5279swap : (Vertices 2 ⊕ Fin 7 ⊕ Fin 3) → Fin 13 :=
  fun v => ![2,6,7,1,0,8,9,10,11,12,3,4,5] (sourceLabel 2 6 2 v)
def fusedMap5279swap : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 6 2 v)
theorem sourceMap5279swap_checked : acceptsGraphIso
    (source (graph core5279) (root 2) 6 2) DegreeOneSmallSpectrum956.graph sourceMap5279swap=true := by decide +kernel
theorem fusedMap5279swap_checked : acceptsGraphIso
    (fused (graph core5279) (root 2) 6 2) DegreeOneSmallSpectrum856.graph fusedMap5279swap=true := by decide +kernel
theorem certified5279swap : Certified (graph core5279) (root 2) 6 2 :=
  of_native_maps core5279 DegreeOneSmallSpectrum956.graph DegreeOneSmallSpectrum856.graph
    sourceMap5279swap fusedMap5279swap sourceMap5279swap_checked fusedMap5279swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5279
#print axioms sourceMap5279swap_checked
#print axioms fusedMap5279swap_checked
#print axioms certified5279swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
