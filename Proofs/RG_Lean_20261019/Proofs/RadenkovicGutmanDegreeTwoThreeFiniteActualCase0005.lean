/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0005 : Family 5 := level5.get ⟨4,by decide⟩
def sourceMap0005 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 1) → Fin 8 :=
  fun v => ![1,0,5,6,7,2,3,4] (sourceLabel 5 0 0 v)
def fusedMap0005 : (Vertices 5 ⊕ Fin 2) → Fin 8 :=
  fun v => ![1,0,5,6,7,4,2,3] (fusedLabel 5 0 0 v)
theorem sourceMap0005_checked : acceptsGraphIso
    (source (graph core0005) (root 5) 0 0) DegreeOneSmallSpectrum017.graph sourceMap0005=true := by decide +kernel
theorem fusedMap0005_checked : acceptsGraphIso
    (fused (graph core0005) (root 5) 0 0) DegreeOneSmallSpectrum025.graph fusedMap0005=true := by decide +kernel
theorem certified0005 : Certified (graph core0005) (root 5) 0 0 :=
  of_native_maps core0005 DegreeOneSmallSpectrum017.graph DegreeOneSmallSpectrum025.graph
    sourceMap0005 fusedMap0005 sourceMap0005_checked fusedMap0005_checked
    DegreeTwoThreeFiniteComparisons.comparison0005
#print axioms sourceMap0005_checked
#print axioms fusedMap0005_checked
#print axioms certified0005
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
