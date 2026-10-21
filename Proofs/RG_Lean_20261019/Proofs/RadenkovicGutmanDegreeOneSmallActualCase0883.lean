/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0883 : Family 8 := level8.get ⟨48,by decide⟩
def sourceMap0883 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,5,6,3,4] (sourceLabel 8 0 0 v)
def fusedMap0883 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,5,0,1,2,3,4,9,10,7,8] (fusedLabel 8 0 0 v)
theorem sourceMap0883_checked : acceptsGraphIso
    (source (graph core0883) (root 8) 0 0) DegreeOneSmallSpectrum277.graph sourceMap0883=true := by decide +kernel
theorem fusedMap0883_checked : acceptsGraphIso
    (fused (graph core0883) (root 8) 0 0) DegreeOneSmallSpectrum194.graph fusedMap0883=true := by decide +kernel
theorem certified0883 : Certified (graph core0883) (root 8) 0 0 :=
  of_native_maps core0883 DegreeOneSmallSpectrum277.graph DegreeOneSmallSpectrum194.graph
    sourceMap0883 fusedMap0883 sourceMap0883_checked fusedMap0883_checked
    DegreeOneSmallComparisons.comparison0883
#print axioms sourceMap0883_checked
#print axioms fusedMap0883_checked
#print axioms certified0883
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
