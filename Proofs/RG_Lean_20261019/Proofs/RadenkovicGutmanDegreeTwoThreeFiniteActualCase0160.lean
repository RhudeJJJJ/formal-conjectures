/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0160 : Family 9 := level9.get ⟨8,by decide⟩
def sourceMap0160 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0160 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![3,2,1,0,7,8,9,10,11,6,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0160_checked : acceptsGraphIso
    (source (graph core0160) (root 9) 0 0) DegreeOneSmallSpectrum370.graph sourceMap0160=true := by decide +kernel
theorem fusedMap0160_checked : acceptsGraphIso
    (fused (graph core0160) (root 9) 0 0) DegreeOneSmallSpectrum386.graph fusedMap0160=true := by decide +kernel
theorem certified0160 : Certified (graph core0160) (root 9) 0 0 :=
  of_native_maps core0160 DegreeOneSmallSpectrum370.graph DegreeOneSmallSpectrum386.graph
    sourceMap0160 fusedMap0160 sourceMap0160_checked fusedMap0160_checked
    DegreeTwoThreeFiniteComparisons.comparison0160
#print axioms sourceMap0160_checked
#print axioms fusedMap0160_checked
#print axioms certified0160
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
