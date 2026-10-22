/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0459 : Family 10 := level10.get ⟨263,by decide⟩
def sourceMap0459 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0459 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0459_checked : acceptsGraphIso
    (source (graph core0459) (root 10) 0 0) DegreeOneSmallSpectrum1041.graph sourceMap0459=true := by decide +kernel
theorem fusedMap0459_checked : acceptsGraphIso
    (fused (graph core0459) (root 10) 0 0) DegreeOneSmallSpectrum1272.graph fusedMap0459=true := by decide +kernel
theorem certified0459 : Certified (graph core0459) (root 10) 0 0 :=
  of_native_maps core0459 DegreeOneSmallSpectrum1041.graph DegreeOneSmallSpectrum1272.graph
    sourceMap0459 fusedMap0459 sourceMap0459_checked fusedMap0459_checked
    DegreeTwoThreeFiniteComparisons.comparison0459
#print axioms sourceMap0459_checked
#print axioms fusedMap0459_checked
#print axioms certified0459
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
