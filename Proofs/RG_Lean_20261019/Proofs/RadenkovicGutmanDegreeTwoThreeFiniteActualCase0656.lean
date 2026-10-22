/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0656 : Family 10 := level10.get ⟨850,by decide⟩
def sourceMap0656 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0656 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0656_checked : acceptsGraphIso
    (source (graph core0656) (root 10) 0 0) DegreeOneSmallSpectrum1386.graph sourceMap0656=true := by decide +kernel
theorem fusedMap0656_checked : acceptsGraphIso
    (fused (graph core0656) (root 10) 0 0) DegreeOneSmallSpectrum1341.graph fusedMap0656=true := by decide +kernel
theorem certified0656 : Certified (graph core0656) (root 10) 0 0 :=
  of_native_maps core0656 DegreeOneSmallSpectrum1386.graph DegreeOneSmallSpectrum1341.graph
    sourceMap0656 fusedMap0656 sourceMap0656_checked fusedMap0656_checked
    DegreeTwoThreeFiniteComparisons.comparison0656
#print axioms sourceMap0656_checked
#print axioms fusedMap0656_checked
#print axioms certified0656
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
