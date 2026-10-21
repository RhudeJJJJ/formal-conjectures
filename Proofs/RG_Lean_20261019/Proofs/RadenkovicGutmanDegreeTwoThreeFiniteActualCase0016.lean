/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0016 : Family 6 := level6.get ⟨21,by decide⟩
def sourceMap0016 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 1) → Fin 9 :=
  fun v => ![1,0,5,6,7,8,2,3,4] (sourceLabel 6 0 0 v)
def fusedMap0016 : (Vertices 6 ⊕ Fin 2) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,8,6,7] (fusedLabel 6 0 0 v)
theorem sourceMap0016_checked : acceptsGraphIso
    (source (graph core0016) (root 6) 0 0) DegreeTwoThreeSpectrum061.graph sourceMap0016=true := by decide +kernel
theorem fusedMap0016_checked : acceptsGraphIso
    (fused (graph core0016) (root 6) 0 0) DegreeOneSmallSpectrum041.graph fusedMap0016=true := by decide +kernel
theorem certified0016 : Certified (graph core0016) (root 6) 0 0 :=
  of_native_maps core0016 DegreeTwoThreeSpectrum061.graph DegreeOneSmallSpectrum041.graph
    sourceMap0016 fusedMap0016 sourceMap0016_checked fusedMap0016_checked
    DegreeTwoThreeFiniteComparisons.comparison0016
#print axioms sourceMap0016_checked
#print axioms fusedMap0016_checked
#print axioms certified0016
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
