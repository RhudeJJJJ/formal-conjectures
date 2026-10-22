/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0385 : Family 9 := level9.get ⟨642,by decide⟩
def sourceMap0385 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0385 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0385_checked : acceptsGraphIso
    (source (graph core0385) (root 9) 0 0) DegreeOneSmallSpectrum793.graph sourceMap0385=true := by decide +kernel
theorem fusedMap0385_checked : acceptsGraphIso
    (fused (graph core0385) (root 9) 0 0) DegreeOneSmallSpectrum792.graph fusedMap0385=true := by decide +kernel
theorem certified0385 : Certified (graph core0385) (root 9) 0 0 :=
  of_native_maps core0385 DegreeOneSmallSpectrum793.graph DegreeOneSmallSpectrum792.graph
    sourceMap0385 fusedMap0385 sourceMap0385_checked fusedMap0385_checked
    DegreeTwoThreeFiniteComparisons.comparison0385
#print axioms sourceMap0385_checked
#print axioms fusedMap0385_checked
#print axioms certified0385
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
