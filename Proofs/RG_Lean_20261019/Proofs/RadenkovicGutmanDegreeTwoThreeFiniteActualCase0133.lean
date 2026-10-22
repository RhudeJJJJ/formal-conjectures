/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0133 : Family 8 := level8.get ⟨204,by decide⟩
def sourceMap0133 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0133 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap0133_checked : acceptsGraphIso
    (source (graph core0133) (root 8) 0 0) DegreeOneSmallSpectrum260.graph sourceMap0133=true := by decide +kernel
theorem fusedMap0133_checked : acceptsGraphIso
    (fused (graph core0133) (root 8) 0 0) DegreeOneSmallSpectrum259.graph fusedMap0133=true := by decide +kernel
theorem certified0133 : Certified (graph core0133) (root 8) 0 0 :=
  of_native_maps core0133 DegreeOneSmallSpectrum260.graph DegreeOneSmallSpectrum259.graph
    sourceMap0133 fusedMap0133 sourceMap0133_checked fusedMap0133_checked
    DegreeTwoThreeFiniteComparisons.comparison0133
#print axioms sourceMap0133_checked
#print axioms fusedMap0133_checked
#print axioms certified0133
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
