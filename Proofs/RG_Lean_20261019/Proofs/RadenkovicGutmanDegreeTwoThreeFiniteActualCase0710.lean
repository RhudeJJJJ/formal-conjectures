/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0710 : Family 10 := level10.get ⟨978,by decide⟩
def sourceMap0710 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0710 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0710_checked : acceptsGraphIso
    (source (graph core0710) (root 10) 0 0) DegreeOneSmallSpectrum958.graph sourceMap0710=true := by decide +kernel
theorem fusedMap0710_checked : acceptsGraphIso
    (fused (graph core0710) (root 10) 0 0) DegreeOneSmallSpectrum957.graph fusedMap0710=true := by decide +kernel
theorem certified0710 : Certified (graph core0710) (root 10) 0 0 :=
  of_native_maps core0710 DegreeOneSmallSpectrum958.graph DegreeOneSmallSpectrum957.graph
    sourceMap0710 fusedMap0710 sourceMap0710_checked fusedMap0710_checked
    DegreeTwoThreeFiniteComparisons.comparison0710
#print axioms sourceMap0710_checked
#print axioms fusedMap0710_checked
#print axioms certified0710
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
