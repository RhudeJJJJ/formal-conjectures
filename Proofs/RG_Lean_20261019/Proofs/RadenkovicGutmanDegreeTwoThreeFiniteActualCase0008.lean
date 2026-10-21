/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0008 : Family 5 := level5.get ⟨11,by decide⟩
def sourceMap0008 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,5,6,7,1,2,3,4] (sourceLabel 5 0 0 v)
def fusedMap0008 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![0,5,6,7,1,2,3,4] (fusedLabel 5 0 0 v)
theorem sourceMap0008_checked : acceptsGraphIso
    (source (graph core0008) (root 5) 0 0) DegreeOneSmallSpectrum023.graph sourceMap0008=true := by decide +kernel
theorem fusedMap0008_checked : acceptsGraphIso
    (fused (graph core0008) (root 5) 0 0) DegreeOneSmallSpectrum022.graph fusedMap0008=true := by decide +kernel
theorem certified0008 : Certified (graph core0008) (root 5) 0 0 :=
  of_native_maps core0008 DegreeOneSmallSpectrum023.graph DegreeOneSmallSpectrum022.graph
    sourceMap0008 fusedMap0008 sourceMap0008_checked fusedMap0008_checked
    DegreeTwoThreeFiniteComparisons.comparison0008
#print axioms sourceMap0008_checked
#print axioms fusedMap0008_checked
#print axioms certified0008
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
