/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0031 : Family 7 := level7.get ⟨23,by decide⟩
def sourceMap0031 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![2,1,0,7,8,9,6,3,4,5] (sourceLabel 7 0 0 v)
def fusedMap0031 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![1,0,6,7,8,9,5,4,2,3] (fusedLabel 7 0 0 v)
theorem sourceMap0031_checked : acceptsGraphIso
    (source (graph core0031) (root 7) 0 0) DegreeOneSmallSpectrum101.graph sourceMap0031=true := by decide +kernel
theorem fusedMap0031_checked : acceptsGraphIso
    (fused (graph core0031) (root 7) 0 0) DegreeOneSmallSpectrum083.graph fusedMap0031=true := by decide +kernel
theorem certified0031 : Certified (graph core0031) (root 7) 0 0 :=
  of_native_maps core0031 DegreeOneSmallSpectrum101.graph DegreeOneSmallSpectrum083.graph
    sourceMap0031 fusedMap0031 sourceMap0031_checked fusedMap0031_checked
    DegreeTwoThreeFiniteComparisons.comparison0031
#print axioms sourceMap0031_checked
#print axioms fusedMap0031_checked
#print axioms certified0031
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
