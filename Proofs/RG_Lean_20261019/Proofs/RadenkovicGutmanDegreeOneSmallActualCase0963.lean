/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0963 : Family 8 := level8.get ⟨79,by decide⟩
def sourceMap0963 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,5,6,3,4] (sourceLabel 8 0 0 v)
def fusedMap0963 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,4,5,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0963_checked : acceptsGraphIso
    (source (graph core0963) (root 8) 0 0) DegreeOneSmallSpectrum291.graph sourceMap0963=true := by decide +kernel
theorem fusedMap0963_checked : acceptsGraphIso
    (fused (graph core0963) (root 8) 0 0) DegreeOneSmallSpectrum224.graph fusedMap0963=true := by decide +kernel
theorem certified0963 : Certified (graph core0963) (root 8) 0 0 :=
  of_native_maps core0963 DegreeOneSmallSpectrum291.graph DegreeOneSmallSpectrum224.graph
    sourceMap0963 fusedMap0963 sourceMap0963_checked fusedMap0963_checked
    DegreeOneSmallComparisons.comparison0963
#print axioms sourceMap0963_checked
#print axioms fusedMap0963_checked
#print axioms certified0963
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
