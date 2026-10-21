/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0975 : Family 8 := level8.get ⟨85,by decide⟩
def sourceMap0975 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,8,9,10,5,6,7,3,4] (sourceLabel 8 0 0 v)
def fusedMap0975 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,4,5,6,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0975_checked : acceptsGraphIso
    (source (graph core0975) (root 8) 0 0) DegreeOneSmallSpectrum275.graph sourceMap0975=true := by decide +kernel
theorem fusedMap0975_checked : acceptsGraphIso
    (fused (graph core0975) (root 8) 0 0) DegreeOneSmallSpectrum220.graph fusedMap0975=true := by decide +kernel
theorem certified0975 : Certified (graph core0975) (root 8) 0 0 :=
  of_native_maps core0975 DegreeOneSmallSpectrum275.graph DegreeOneSmallSpectrum220.graph
    sourceMap0975 fusedMap0975 sourceMap0975_checked fusedMap0975_checked
    DegreeOneSmallComparisons.comparison0975
#print axioms sourceMap0975_checked
#print axioms fusedMap0975_checked
#print axioms certified0975
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
