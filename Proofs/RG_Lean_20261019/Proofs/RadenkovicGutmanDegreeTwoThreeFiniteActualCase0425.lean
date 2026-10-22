/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0425 : Family 10 := level10.get ⟨139,by decide⟩
def sourceMap0425 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0425 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0425_checked : acceptsGraphIso
    (source (graph core0425) (root 10) 0 0) DegreeOneSmallSpectrum1058.graph sourceMap0425=true := by decide +kernel
theorem fusedMap0425_checked : acceptsGraphIso
    (fused (graph core0425) (root 10) 0 0) DegreeOneSmallSpectrum933.graph fusedMap0425=true := by decide +kernel
theorem certified0425 : Certified (graph core0425) (root 10) 0 0 :=
  of_native_maps core0425 DegreeOneSmallSpectrum1058.graph DegreeOneSmallSpectrum933.graph
    sourceMap0425 fusedMap0425 sourceMap0425_checked fusedMap0425_checked
    DegreeTwoThreeFiniteComparisons.comparison0425
#print axioms sourceMap0425_checked
#print axioms fusedMap0425_checked
#print axioms certified0425
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
