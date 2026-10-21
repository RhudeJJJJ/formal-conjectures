/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0024 : Family 6 := level6.get ⟨38,by decide⟩
def sourceMap0024 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,6,7,8] (sourceLabel 6 0 0 v)
def fusedMap0024 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,8,6,7] (fusedLabel 6 0 0 v)
theorem sourceMap0024_checked : acceptsGraphIso
    (source (graph core0024) (root 6) 0 0) DegreeTwoThreeSpectrum058.graph sourceMap0024=true := by decide +kernel
theorem fusedMap0024_checked : acceptsGraphIso
    (fused (graph core0024) (root 6) 0 0) DegreeOneSmallSpectrum066.graph fusedMap0024=true := by decide +kernel
theorem certified0024 : Certified (graph core0024) (root 6) 0 0 :=
  of_native_maps core0024 DegreeTwoThreeSpectrum058.graph DegreeOneSmallSpectrum066.graph
    sourceMap0024 fusedMap0024 sourceMap0024_checked fusedMap0024_checked
    DegreeTwoThreeFiniteComparisons.comparison0024
#print axioms sourceMap0024_checked
#print axioms fusedMap0024_checked
#print axioms certified0024
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
