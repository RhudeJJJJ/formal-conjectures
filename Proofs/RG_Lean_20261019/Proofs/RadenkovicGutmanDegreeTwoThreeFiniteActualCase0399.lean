/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0399 : Family 10 := level10.get ⟨9,by decide⟩
def sourceMap0399 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,3,2,1,0,8,9,10,11,12,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0399 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0399_checked : acceptsGraphIso
    (source (graph core0399) (root 10) 0 0) DegreeOneSmallSpectrum870.graph sourceMap0399=true := by decide +kernel
theorem fusedMap0399_checked : acceptsGraphIso
    (fused (graph core0399) (root 10) 0 0) DegreeOneSmallSpectrum857.graph fusedMap0399=true := by decide +kernel
theorem certified0399 : Certified (graph core0399) (root 10) 0 0 :=
  of_native_maps core0399 DegreeOneSmallSpectrum870.graph DegreeOneSmallSpectrum857.graph
    sourceMap0399 fusedMap0399 sourceMap0399_checked fusedMap0399_checked
    DegreeTwoThreeFiniteComparisons.comparison0399
#print axioms sourceMap0399_checked
#print axioms fusedMap0399_checked
#print axioms certified0399
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
