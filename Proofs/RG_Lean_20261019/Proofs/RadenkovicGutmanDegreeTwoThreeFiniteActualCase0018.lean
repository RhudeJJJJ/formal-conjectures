/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0018 : Family 6 := level6.get ⟨25,by decide⟩
def sourceMap0018 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![4,0,1,2,3,5,6,7,8] (sourceLabel 6 0 0 v)
def fusedMap0018 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![4,0,1,2,3,5,6,7,8] (fusedLabel 6 0 0 v)
theorem sourceMap0018_checked : acceptsGraphIso
    (source (graph core0018) (root 6) 0 0) DegreeOneSmallSpectrum050.graph sourceMap0018=true := by decide +kernel
theorem fusedMap0018_checked : acceptsGraphIso
    (fused (graph core0018) (root 6) 0 0) DegreeOneSmallSpectrum049.graph fusedMap0018=true := by decide +kernel
theorem certified0018 : Certified (graph core0018) (root 6) 0 0 :=
  of_native_maps core0018 DegreeOneSmallSpectrum050.graph DegreeOneSmallSpectrum049.graph
    sourceMap0018 fusedMap0018 sourceMap0018_checked fusedMap0018_checked
    DegreeTwoThreeFiniteComparisons.comparison0018
#print axioms sourceMap0018_checked
#print axioms fusedMap0018_checked
#print axioms certified0018
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
