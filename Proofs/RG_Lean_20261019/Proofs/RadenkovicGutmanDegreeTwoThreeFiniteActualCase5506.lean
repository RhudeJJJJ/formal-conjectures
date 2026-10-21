/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons110
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5506 : Family 4 := level4.get ⟨7,by decide⟩
def sourceMap5506 : (Vertices 4 ⊕ Fin 3 ⊕ Fin 5) → Fin 13 :=
  fun v => ![1,5,6,7,8,2,3,4,0,9,10,11,12] (sourceLabel 4 2 4 v)
def fusedMap5506 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 2 4 v)
theorem sourceMap5506_checked : acceptsGraphIso
    (source (graph core5506) (root 4) 2 4) DegreeOneSmallSpectrum1481.graph sourceMap5506=true := by decide +kernel
theorem fusedMap5506_checked : acceptsGraphIso
    (fused (graph core5506) (root 4) 2 4) DegreeOneSmallSpectrum922.graph fusedMap5506=true := by decide +kernel
theorem certified5506 : Certified (graph core5506) (root 4) 2 4 :=
  of_native_maps core5506 DegreeOneSmallSpectrum1481.graph DegreeOneSmallSpectrum922.graph
    sourceMap5506 fusedMap5506 sourceMap5506_checked fusedMap5506_checked
    DegreeTwoThreeFiniteComparisons.comparison5506
#print axioms sourceMap5506_checked
#print axioms fusedMap5506_checked
#print axioms certified5506
def sourceMap5506swap : (Vertices 4 ⊕ Fin 5 ⊕ Fin 3) → Fin 13 :=
  fun v => ![1,5,6,7,8,0,9,10,11,12,2,3,4] (sourceLabel 4 4 2 v)
def fusedMap5506swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,4,5,6,7,2,1,0,8,9,10,11,12] (fusedLabel 4 4 2 v)
theorem sourceMap5506swap_checked : acceptsGraphIso
    (source (graph core5506) (root 4) 4 2) DegreeOneSmallSpectrum1481.graph sourceMap5506swap=true := by decide +kernel
theorem fusedMap5506swap_checked : acceptsGraphIso
    (fused (graph core5506) (root 4) 4 2) DegreeOneSmallSpectrum922.graph fusedMap5506swap=true := by decide +kernel
theorem certified5506swap : Certified (graph core5506) (root 4) 4 2 :=
  of_native_maps core5506 DegreeOneSmallSpectrum1481.graph DegreeOneSmallSpectrum922.graph
    sourceMap5506swap fusedMap5506swap sourceMap5506swap_checked fusedMap5506swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5506
#print axioms sourceMap5506swap_checked
#print axioms fusedMap5506swap_checked
#print axioms certified5506swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
