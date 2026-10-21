/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0133 : Family 4 := level4.get ⟨2,by decide⟩
def sourceMap0133 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (sourceLabel 4 0 6 v)
def fusedMap0133 : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 0 6 v)
theorem sourceMap0133_checked : acceptsGraphIso
    (source (graph core0133) (root 4) 0 6) DegreeOneSmallSpectrum929.graph sourceMap0133=true := by decide +kernel
theorem fusedMap0133_checked : acceptsGraphIso
    (fused (graph core0133) (root 4) 0 6) DegreeOneSmallSpectrum857.graph fusedMap0133=true := by decide +kernel
theorem certified0133 : Certified (graph core0133) (root 4) 0 6 :=
  of_native_maps core0133 DegreeOneSmallSpectrum929.graph DegreeOneSmallSpectrum857.graph
    sourceMap0133 fusedMap0133 sourceMap0133_checked fusedMap0133_checked
    DegreeOneSmallComparisons.comparison0133
#print axioms sourceMap0133_checked
#print axioms fusedMap0133_checked
#print axioms certified0133
def sourceMap0133swap : (Vertices 4 ⊕ Fin 7 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,8,9,10,11,12,7] (sourceLabel 4 6 0 v)
def fusedMap0133swap : (Vertices 4 ⊕ Fin 8) → Fin 13 :=
  fun v => ![2,3,4,5,6,1,0,7,8,9,10,11,12] (fusedLabel 4 6 0 v)
theorem sourceMap0133swap_checked : acceptsGraphIso
    (source (graph core0133) (root 4) 6 0) DegreeOneSmallSpectrum929.graph sourceMap0133swap=true := by decide +kernel
theorem fusedMap0133swap_checked : acceptsGraphIso
    (fused (graph core0133) (root 4) 6 0) DegreeOneSmallSpectrum857.graph fusedMap0133swap=true := by decide +kernel
theorem certified0133swap : Certified (graph core0133) (root 4) 6 0 :=
  of_native_maps core0133 DegreeOneSmallSpectrum929.graph DegreeOneSmallSpectrum857.graph
    sourceMap0133swap fusedMap0133swap sourceMap0133swap_checked fusedMap0133swap_checked
    DegreeOneSmallComparisons.comparison0133
#print axioms sourceMap0133swap_checked
#print axioms fusedMap0133swap_checked
#print axioms certified0133swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
