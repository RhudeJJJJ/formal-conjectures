/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0983 : Family 10 := level10.get ⟨1655,by decide⟩
def sourceMap0983 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0983 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0983_checked : acceptsGraphIso
    (source (graph core0983) (root 10) 0 0) DegreeOneSmallSpectrum1806.graph sourceMap0983=true := by decide +kernel
theorem fusedMap0983_checked : acceptsGraphIso
    (fused (graph core0983) (root 10) 0 0) DegreeOneSmallSpectrum1805.graph fusedMap0983=true := by decide +kernel
theorem certified0983 : Certified (graph core0983) (root 10) 0 0 :=
  of_native_maps core0983 DegreeOneSmallSpectrum1806.graph DegreeOneSmallSpectrum1805.graph
    sourceMap0983 fusedMap0983 sourceMap0983_checked fusedMap0983_checked
    DegreeTwoThreeFiniteComparisons.comparison0983
#print axioms sourceMap0983_checked
#print axioms fusedMap0983_checked
#print axioms certified0983
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
