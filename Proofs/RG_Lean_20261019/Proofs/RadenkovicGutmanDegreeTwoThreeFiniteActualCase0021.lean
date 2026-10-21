/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0021 : Family 6 := level6.get ⟨31,by decide⟩
def sourceMap0021 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![0,5,6,7,8,1,2,3,4] (sourceLabel 6 0 0 v)
def fusedMap0021 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,5,6,7,8,1,2,3,4] (fusedLabel 6 0 0 v)
theorem sourceMap0021_checked : acceptsGraphIso
    (source (graph core0021) (root 6) 0 0) DegreeOneSmallSpectrum057.graph sourceMap0021=true := by decide +kernel
theorem fusedMap0021_checked : acceptsGraphIso
    (fused (graph core0021) (root 6) 0 0) DegreeOneSmallSpectrum054.graph fusedMap0021=true := by decide +kernel
theorem certified0021 : Certified (graph core0021) (root 6) 0 0 :=
  of_native_maps core0021 DegreeOneSmallSpectrum057.graph DegreeOneSmallSpectrum054.graph
    sourceMap0021 fusedMap0021 sourceMap0021_checked fusedMap0021_checked
    DegreeTwoThreeFiniteComparisons.comparison0021
#print axioms sourceMap0021_checked
#print axioms fusedMap0021_checked
#print axioms certified0021
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
