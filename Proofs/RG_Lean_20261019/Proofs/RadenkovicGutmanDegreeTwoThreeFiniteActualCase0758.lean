/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0758 : Family 10 := level10.get ⟨1111,by decide⟩
def sourceMap0758 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,5,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0758 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0758_checked : acceptsGraphIso
    (source (graph core0758) (root 10) 0 0) DegreeOneSmallSpectrum1656.graph sourceMap0758=true := by decide +kernel
theorem fusedMap0758_checked : acceptsGraphIso
    (fused (graph core0758) (root 10) 0 0) DegreeOneSmallSpectrum1752.graph fusedMap0758=true := by decide +kernel
theorem certified0758 : Certified (graph core0758) (root 10) 0 0 :=
  of_native_maps core0758 DegreeOneSmallSpectrum1656.graph DegreeOneSmallSpectrum1752.graph
    sourceMap0758 fusedMap0758 sourceMap0758_checked fusedMap0758_checked
    DegreeTwoThreeFiniteComparisons.comparison0758
#print axioms sourceMap0758_checked
#print axioms fusedMap0758_checked
#print axioms certified0758
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
