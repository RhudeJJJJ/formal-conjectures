/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0051 : Family 7 := level7.get ⟨75,by decide⟩
def sourceMap0051 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap0051 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0051_checked : acceptsGraphIso
    (source (graph core0051) (root 7) 0 0) DegreeOneSmallSpectrum119.graph sourceMap0051=true := by decide +kernel
theorem fusedMap0051_checked : acceptsGraphIso
    (fused (graph core0051) (root 7) 0 0) DegreeOneSmallSpectrum118.graph fusedMap0051=true := by decide +kernel
theorem certified0051 : Certified (graph core0051) (root 7) 0 0 :=
  of_native_maps core0051 DegreeOneSmallSpectrum119.graph DegreeOneSmallSpectrum118.graph
    sourceMap0051 fusedMap0051 sourceMap0051_checked fusedMap0051_checked
    DegreeTwoThreeFiniteComparisons.comparison0051
#print axioms sourceMap0051_checked
#print axioms fusedMap0051_checked
#print axioms certified0051
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
