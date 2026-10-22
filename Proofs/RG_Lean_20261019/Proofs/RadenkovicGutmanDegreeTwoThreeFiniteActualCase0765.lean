/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0765 : Family 10 := level10.get ⟨1128,by decide⟩
def sourceMap0765 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0765 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0765_checked : acceptsGraphIso
    (source (graph core0765) (root 10) 0 0) DegreeOneSmallSpectrum1676.graph sourceMap0765=true := by decide +kernel
theorem fusedMap0765_checked : acceptsGraphIso
    (fused (graph core0765) (root 10) 0 0) DegreeOneSmallSpectrum1782.graph fusedMap0765=true := by decide +kernel
theorem certified0765 : Certified (graph core0765) (root 10) 0 0 :=
  of_native_maps core0765 DegreeOneSmallSpectrum1676.graph DegreeOneSmallSpectrum1782.graph
    sourceMap0765 fusedMap0765 sourceMap0765_checked fusedMap0765_checked
    DegreeTwoThreeFiniteComparisons.comparison0765
#print axioms sourceMap0765_checked
#print axioms fusedMap0765_checked
#print axioms certified0765
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
