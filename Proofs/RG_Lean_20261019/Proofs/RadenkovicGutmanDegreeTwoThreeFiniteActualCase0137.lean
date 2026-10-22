/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0137 : Family 8 := level8.get ⟨215,by decide⟩
def sourceMap0137 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0137 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0137_checked : acceptsGraphIso
    (source (graph core0137) (root 8) 0 0) DegreeOneSmallSpectrum361.graph sourceMap0137=true := by decide +kernel
theorem fusedMap0137_checked : acceptsGraphIso
    (fused (graph core0137) (root 8) 0 0) DegreeOneSmallSpectrum284.graph fusedMap0137=true := by decide +kernel
theorem certified0137 : Certified (graph core0137) (root 8) 0 0 :=
  of_native_maps core0137 DegreeOneSmallSpectrum361.graph DegreeOneSmallSpectrum284.graph
    sourceMap0137 fusedMap0137 sourceMap0137_checked fusedMap0137_checked
    DegreeTwoThreeFiniteComparisons.comparison0137
#print axioms sourceMap0137_checked
#print axioms fusedMap0137_checked
#print axioms certified0137
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
