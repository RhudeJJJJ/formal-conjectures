/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0231 : Family 9 := level9.get ⟨257,by decide⟩
def sourceMap0231 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0231 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0231_checked : acceptsGraphIso
    (source (graph core0231) (root 9) 0 0) DegreeOneSmallSpectrum670.graph sourceMap0231=true := by decide +kernel
theorem fusedMap0231_checked : acceptsGraphIso
    (fused (graph core0231) (root 9) 0 0) DegreeOneSmallSpectrum553.graph fusedMap0231=true := by decide +kernel
theorem certified0231 : Certified (graph core0231) (root 9) 0 0 :=
  of_native_maps core0231 DegreeOneSmallSpectrum670.graph DegreeOneSmallSpectrum553.graph
    sourceMap0231 fusedMap0231 sourceMap0231_checked fusedMap0231_checked
    DegreeTwoThreeFiniteComparisons.comparison0231
#print axioms sourceMap0231_checked
#print axioms fusedMap0231_checked
#print axioms certified0231
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
