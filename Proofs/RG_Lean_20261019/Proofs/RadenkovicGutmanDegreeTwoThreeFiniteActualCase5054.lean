/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons101
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core5054 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap5054 : (Vertices 2 ⊕ Fin 3 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,4,5,1,2,3,6,7,8,9] (sourceLabel 2 2 3 v)
def fusedMap5054 : (Vertices 2 ⊕ Fin 7) → Fin 10 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9] (fusedLabel 2 2 3 v)
theorem sourceMap5054_checked : acceptsGraphIso
    (source (graph core5054) (root 2) 2 3) DegreeOneSmallSpectrum088.graph sourceMap5054=true := by decide +kernel
theorem fusedMap5054_checked : acceptsGraphIso
    (fused (graph core5054) (root 2) 2 3) DegreeOneSmallSpectrum080.graph fusedMap5054=true := by decide +kernel
theorem certified5054 : Certified (graph core5054) (root 2) 2 3 :=
  of_native_maps core5054 DegreeOneSmallSpectrum088.graph DegreeOneSmallSpectrum080.graph
    sourceMap5054 fusedMap5054 sourceMap5054_checked fusedMap5054_checked
    DegreeTwoThreeFiniteComparisons.comparison5054
#print axioms sourceMap5054_checked
#print axioms fusedMap5054_checked
#print axioms certified5054
def sourceMap5054swap : (Vertices 2 ⊕ Fin 4 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,4,5,6,7,8,9,1,2,3] (sourceLabel 2 3 2 v)
def fusedMap5054swap : (Vertices 2 ⊕ Fin 7) → Fin 10 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9] (fusedLabel 2 3 2 v)
theorem sourceMap5054swap_checked : acceptsGraphIso
    (source (graph core5054) (root 2) 3 2) DegreeOneSmallSpectrum088.graph sourceMap5054swap=true := by decide +kernel
theorem fusedMap5054swap_checked : acceptsGraphIso
    (fused (graph core5054) (root 2) 3 2) DegreeOneSmallSpectrum080.graph fusedMap5054swap=true := by decide +kernel
theorem certified5054swap : Certified (graph core5054) (root 2) 3 2 :=
  of_native_maps core5054 DegreeOneSmallSpectrum088.graph DegreeOneSmallSpectrum080.graph
    sourceMap5054swap fusedMap5054swap sourceMap5054swap_checked fusedMap5054swap_checked
    DegreeTwoThreeFiniteComparisons.comparison5054
#print axioms sourceMap5054swap_checked
#print axioms fusedMap5054swap_checked
#print axioms certified5054swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
