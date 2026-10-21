/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0051 : Family 2 := level2.get ⟨0,by decide⟩
def sourceMap0051 : (Vertices 2 ⊕ Fin 4 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,9,10,1,2,3,4,5,6,7,8] (sourceLabel 2 3 3 v)
def fusedMap0051 : (Vertices 2 ⊕ Fin 8) → Fin 11 :=
  fun v => ![3,4,5,2,1,0,6,7,8,9,10] (fusedLabel 2 3 3 v)
theorem sourceMap0051_checked : acceptsGraphIso
    (source (graph core0051) (root 2) 3 3) DegreeOneSmallSpectrum228.graph sourceMap0051=true := by decide +kernel
theorem fusedMap0051_checked : acceptsGraphIso
    (fused (graph core0051) (root 2) 3 3) DegreeOneSmallSpectrum168.graph fusedMap0051=true := by decide +kernel
theorem certified0051 : Certified (graph core0051) (root 2) 3 3 :=
  of_native_maps core0051 DegreeOneSmallSpectrum228.graph DegreeOneSmallSpectrum168.graph
    sourceMap0051 fusedMap0051 sourceMap0051_checked fusedMap0051_checked
    DegreeOneSmallComparisons.comparison0051
#print axioms sourceMap0051_checked
#print axioms fusedMap0051_checked
#print axioms certified0051
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
