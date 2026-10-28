/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons106
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5325 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5325 : (Vertices 2 ⊕ Fin 4 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,5,6,1,2,3,4,7,8,9,10,11] (sourceLabel 2 3 4 v)
def fusedMap5325 : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11] (fusedLabel 2 3 4 v)
theorem sourceMap5325_checked : acceptsGraphIso
    (source (graph core5325) (root 2) 3 4) DegreeOneSmallSpectrum394.graph sourceMap5325=true := by decide +kernel
theorem fusedMap5325_checked : acceptsGraphIso
    (fused (graph core5325) (root 2) 3 4) DegreeOneSmallSpectrum378.graph fusedMap5325=true := by decide +kernel
theorem certified5325 : Certified (graph core5325) (root 2) 3 4 :=
  of_native_maps core5325 DegreeOneSmallSpectrum394.graph DegreeOneSmallSpectrum378.graph
    sourceMap5325 fusedMap5325 sourceMap5325_checked fusedMap5325_checked
    DegreeTwoThreeFiniteComparisons.comparison5325
#print axioms sourceMap5325_checked
#print axioms fusedMap5325_checked
#print axioms certified5325
def sourceMap5325swap : (Vertices 2 ⊕ Fin 5 ⊕ Fin 4) → Fin 12 :=
  fun v => ![0,5,6,7,8,9,10,11,1,2,3,4] (sourceLabel 2 4 3 v)
def fusedMap5325swap : (Vertices 2 ⊕ Fin 9) → Fin 12 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11] (fusedLabel 2 4 3 v)
theorem sourceMap5325swap_checked : acceptsGraphIso
    (source (graph core5325) (root 2) 4 3) DegreeOneSmallSpectrum394.graph sourceMap5325swap=true := by decide +kernel
theorem fusedMap5325swap_checked : acceptsGraphIso
    (fused (graph core5325) (root 2) 4 3) DegreeOneSmallSpectrum378.graph fusedMap5325swap=true := by decide +kernel
theorem certified5325swap : Certified (graph core5325) (root 2) 4 3 :=
  of_native_maps core5325 DegreeOneSmallSpectrum394.graph DegreeOneSmallSpectrum378.graph
    sourceMap5325swap fusedMap5325swap sourceMap5325swap_checked fusedMap5325swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5325
#print axioms sourceMap5325swap_checked
#print axioms fusedMap5325swap_checked
#print axioms certified5325swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
