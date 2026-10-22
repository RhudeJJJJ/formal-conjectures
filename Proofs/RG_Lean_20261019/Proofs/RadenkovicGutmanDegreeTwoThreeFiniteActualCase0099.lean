/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0099 : Family 8 := level8.get ⟨125,by decide⟩
def sourceMap0099 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,5,6,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0099 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,9,10,8,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap0099_checked : acceptsGraphIso
    (source (graph core0099) (root 8) 0 0) DegreeOneSmallSpectrum251.graph sourceMap0099=true := by decide +kernel
theorem fusedMap0099_checked : acceptsGraphIso
    (fused (graph core0099) (root 8) 0 0) DegreeOneSmallSpectrum311.graph fusedMap0099=true := by decide +kernel
theorem certified0099 : Certified (graph core0099) (root 8) 0 0 :=
  of_native_maps core0099 DegreeOneSmallSpectrum251.graph DegreeOneSmallSpectrum311.graph
    sourceMap0099 fusedMap0099 sourceMap0099_checked fusedMap0099_checked
    DegreeTwoThreeFiniteComparisons.comparison0099
#print axioms sourceMap0099_checked
#print axioms fusedMap0099_checked
#print axioms certified0099
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
