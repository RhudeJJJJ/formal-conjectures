/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0790 : Family 10 := level10.get ⟨1191,by decide⟩
def sourceMap0790 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0790 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,8,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0790_checked : acceptsGraphIso
    (source (graph core0790) (root 10) 0 0) DegreeOneSmallSpectrum1607.graph sourceMap0790=true := by decide +kernel
theorem fusedMap0790_checked : acceptsGraphIso
    (fused (graph core0790) (root 10) 0 0) DegreeOneSmallSpectrum1872.graph fusedMap0790=true := by decide +kernel
theorem certified0790 : Certified (graph core0790) (root 10) 0 0 :=
  of_native_maps core0790 DegreeOneSmallSpectrum1607.graph DegreeOneSmallSpectrum1872.graph
    sourceMap0790 fusedMap0790 sourceMap0790_checked fusedMap0790_checked
    DegreeTwoThreeFiniteComparisons.comparison0790
#print axioms sourceMap0790_checked
#print axioms fusedMap0790_checked
#print axioms certified0790
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
