/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0046 : Family 7 := level7.get ⟨64,by decide⟩
def sourceMap0046 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap0046 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0046_checked : acceptsGraphIso
    (source (graph core0046) (root 7) 0 0) DegreeTwoThreeSpectrum141.graph sourceMap0046=true := by decide +kernel
theorem fusedMap0046_checked : acceptsGraphIso
    (fused (graph core0046) (root 7) 0 0) DegreeOneSmallSpectrum095.graph fusedMap0046=true := by decide +kernel
theorem certified0046 : Certified (graph core0046) (root 7) 0 0 :=
  of_native_maps core0046 DegreeTwoThreeSpectrum141.graph DegreeOneSmallSpectrum095.graph
    sourceMap0046 fusedMap0046 sourceMap0046_checked fusedMap0046_checked
    DegreeTwoThreeFiniteComparisons.comparison0046
#print axioms sourceMap0046_checked
#print axioms fusedMap0046_checked
#print axioms certified0046
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
