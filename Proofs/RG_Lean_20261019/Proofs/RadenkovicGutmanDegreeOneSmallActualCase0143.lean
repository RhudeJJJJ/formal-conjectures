/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0143 : Family 4 := level4.get ⟨4,by decide⟩
def sourceMap0143 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 1) → Fin 7 :=
  fun v => ![4,0,1,2,3,5,6] (sourceLabel 4 0 0 v)
def fusedMap0143 : (Vertices 4 ⊕ Fin 2) → Fin 7 :=
  fun v => ![0,1,2,3,4,5,6] (fusedLabel 4 0 0 v)
theorem sourceMap0143_checked : acceptsGraphIso
    (source (graph core0143) (root 4) 0 0) DegreeOneSmallSpectrum011.graph sourceMap0143=true := by decide +kernel
theorem fusedMap0143_checked : acceptsGraphIso
    (fused (graph core0143) (root 4) 0 0) DegreeOneSmallSpectrum012.graph fusedMap0143=true := by decide +kernel
theorem certified0143 : Certified (graph core0143) (root 4) 0 0 :=
  of_native_maps core0143 DegreeOneSmallSpectrum011.graph DegreeOneSmallSpectrum012.graph
    sourceMap0143 fusedMap0143 sourceMap0143_checked fusedMap0143_checked
    DegreeOneSmallComparisons.comparison0143
#print axioms sourceMap0143_checked
#print axioms fusedMap0143_checked
#print axioms certified0143
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
