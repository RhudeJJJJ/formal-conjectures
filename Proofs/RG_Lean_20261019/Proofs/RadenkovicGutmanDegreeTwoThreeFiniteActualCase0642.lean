/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0642 : Family 10 := level10.get ⟨814,by decide⟩
def sourceMap0642 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,6,7,8,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0642 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,8,9,10,11,12,5,6,7,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0642_checked : acceptsGraphIso
    (source (graph core0642) (root 10) 0 0) DegreeOneSmallSpectrum1645.graph sourceMap0642=true := by decide +kernel
theorem fusedMap0642_checked : acceptsGraphIso
    (fused (graph core0642) (root 10) 0 0) DegreeOneSmallSpectrum1416.graph fusedMap0642=true := by decide +kernel
theorem certified0642 : Certified (graph core0642) (root 10) 0 0 :=
  of_native_maps core0642 DegreeOneSmallSpectrum1645.graph DegreeOneSmallSpectrum1416.graph
    sourceMap0642 fusedMap0642 sourceMap0642_checked fusedMap0642_checked
    DegreeTwoThreeFiniteComparisons.comparison0642
#print axioms sourceMap0642_checked
#print axioms fusedMap0642_checked
#print axioms certified0642
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
