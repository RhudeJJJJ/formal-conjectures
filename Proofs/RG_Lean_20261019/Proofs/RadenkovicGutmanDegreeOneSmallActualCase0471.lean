/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0471 : Family 7 := level7.get ⟨4,by decide⟩
def sourceMap0471 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,6,7,8,9,5,3,4] (sourceLabel 7 0 0 v)
def fusedMap0471 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![2,1,0,5,6,7,8,9,3,4] (fusedLabel 7 0 0 v)
theorem sourceMap0471_checked : acceptsGraphIso
    (source (graph core0471) (root 7) 0 0) DegreeOneSmallSpectrum076.graph sourceMap0471=true := by decide +kernel
theorem fusedMap0471_checked : acceptsGraphIso
    (fused (graph core0471) (root 7) 0 0) DegreeOneSmallSpectrum091.graph fusedMap0471=true := by decide +kernel
theorem certified0471 : Certified (graph core0471) (root 7) 0 0 :=
  of_native_maps core0471 DegreeOneSmallSpectrum076.graph DegreeOneSmallSpectrum091.graph
    sourceMap0471 fusedMap0471 sourceMap0471_checked fusedMap0471_checked
    DegreeOneSmallComparisons.comparison0471
#print axioms sourceMap0471_checked
#print axioms fusedMap0471_checked
#print axioms certified0471
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
