/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0967 : Family 8 := level8.get ⟨83,by decide⟩
def sourceMap0967 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![4,0,7,8,9,10,1,2,3,5,6] (sourceLabel 8 0 0 v)
def fusedMap0967 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,7,8,9,10,4,5,6,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0967_checked : acceptsGraphIso
    (source (graph core0967) (root 8) 0 0) DegreeOneSmallSpectrum219.graph sourceMap0967=true := by decide +kernel
theorem fusedMap0967_checked : acceptsGraphIso
    (fused (graph core0967) (root 8) 0 0) DegreeOneSmallSpectrum218.graph fusedMap0967=true := by decide +kernel
theorem certified0967 : Certified (graph core0967) (root 8) 0 0 :=
  of_native_maps core0967 DegreeOneSmallSpectrum219.graph DegreeOneSmallSpectrum218.graph
    sourceMap0967 fusedMap0967 sourceMap0967_checked fusedMap0967_checked
    DegreeOneSmallComparisons.comparison0967
#print axioms sourceMap0967_checked
#print axioms fusedMap0967_checked
#print axioms certified0967
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
