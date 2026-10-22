/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0750 : Family 10 := level10.get ⟨1086,by decide⟩
def sourceMap0750 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0750 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0750_checked : acceptsGraphIso
    (source (graph core0750) (root 10) 0 0) DegreeOneSmallSpectrum1065.graph sourceMap0750=true := by decide +kernel
theorem fusedMap0750_checked : acceptsGraphIso
    (fused (graph core0750) (root 10) 0 0) DegreeOneSmallSpectrum1064.graph fusedMap0750=true := by decide +kernel
theorem certified0750 : Certified (graph core0750) (root 10) 0 0 :=
  of_native_maps core0750 DegreeOneSmallSpectrum1065.graph DegreeOneSmallSpectrum1064.graph
    sourceMap0750 fusedMap0750 sourceMap0750_checked fusedMap0750_checked
    DegreeTwoThreeFiniteComparisons.comparison0750
#print axioms sourceMap0750_checked
#print axioms fusedMap0750_checked
#print axioms certified0750
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
