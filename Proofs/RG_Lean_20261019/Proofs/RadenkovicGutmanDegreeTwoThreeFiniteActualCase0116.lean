/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0116 : Family 8 := level8.get ⟨168,by decide⟩
def sourceMap0116 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,8,9,10,5,6,7,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0116 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0116_checked : acceptsGraphIso
    (source (graph core0116) (root 8) 0 0) DegreeOneSmallSpectrum246.graph sourceMap0116=true := by decide +kernel
theorem fusedMap0116_checked : acceptsGraphIso
    (fused (graph core0116) (root 8) 0 0) DegreeOneSmallSpectrum343.graph fusedMap0116=true := by decide +kernel
theorem certified0116 : Certified (graph core0116) (root 8) 0 0 :=
  of_native_maps core0116 DegreeOneSmallSpectrum246.graph DegreeOneSmallSpectrum343.graph
    sourceMap0116 fusedMap0116 sourceMap0116_checked fusedMap0116_checked
    DegreeTwoThreeFiniteComparisons.comparison0116
#print axioms sourceMap0116_checked
#print axioms fusedMap0116_checked
#print axioms certified0116
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
