/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0862 : Family 10 := level10.get ⟨1361,by decide⟩
def sourceMap0862 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0862 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0862_checked : acceptsGraphIso
    (source (graph core0862) (root 10) 0 0) DegreeOneSmallSpectrum1619.graph sourceMap0862=true := by decide +kernel
theorem fusedMap0862_checked : acceptsGraphIso
    (fused (graph core0862) (root 10) 0 0) DegreeOneSmallSpectrum1960.graph fusedMap0862=true := by decide +kernel
theorem certified0862 : Certified (graph core0862) (root 10) 0 0 :=
  of_native_maps core0862 DegreeOneSmallSpectrum1619.graph DegreeOneSmallSpectrum1960.graph
    sourceMap0862 fusedMap0862 sourceMap0862_checked fusedMap0862_checked
    DegreeTwoThreeFiniteComparisons.comparison0862
#print axioms sourceMap0862_checked
#print axioms fusedMap0862_checked
#print axioms certified0862
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
