/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0232 : Family 9 := level9.get ⟨261,by decide⟩
def sourceMap0232 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0232 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0232_checked : acceptsGraphIso
    (source (graph core0232) (root 9) 0 0) DegreeOneSmallSpectrum671.graph sourceMap0232=true := by decide +kernel
theorem fusedMap0232_checked : acceptsGraphIso
    (fused (graph core0232) (root 9) 0 0) DegreeOneSmallSpectrum554.graph fusedMap0232=true := by decide +kernel
theorem certified0232 : Certified (graph core0232) (root 9) 0 0 :=
  of_native_maps core0232 DegreeOneSmallSpectrum671.graph DegreeOneSmallSpectrum554.graph
    sourceMap0232 fusedMap0232 sourceMap0232_checked fusedMap0232_checked
    DegreeTwoThreeFiniteComparisons.comparison0232
#print axioms sourceMap0232_checked
#print axioms fusedMap0232_checked
#print axioms certified0232
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
