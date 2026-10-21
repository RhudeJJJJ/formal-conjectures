/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0020 : Family 6 := level6.get ⟨30,by decide⟩
def sourceMap0020 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,2,3,4] (sourceLabel 6 0 0 v)
def fusedMap0020 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,8,6,7] (fusedLabel 6 0 0 v)
theorem sourceMap0020_checked : acceptsGraphIso
    (source (graph core0020) (root 6) 0 0) DegreeTwoThreeSpectrum064.graph sourceMap0020=true := by decide +kernel
theorem fusedMap0020_checked : acceptsGraphIso
    (fused (graph core0020) (root 6) 0 0) DegreeOneSmallSpectrum057.graph fusedMap0020=true := by decide +kernel
theorem certified0020 : Certified (graph core0020) (root 6) 0 0 :=
  of_native_maps core0020 DegreeTwoThreeSpectrum064.graph DegreeOneSmallSpectrum057.graph
    sourceMap0020 fusedMap0020 sourceMap0020_checked fusedMap0020_checked
    DegreeTwoThreeFiniteComparisons.comparison0020
#print axioms sourceMap0020_checked
#print axioms fusedMap0020_checked
#print axioms certified0020
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
