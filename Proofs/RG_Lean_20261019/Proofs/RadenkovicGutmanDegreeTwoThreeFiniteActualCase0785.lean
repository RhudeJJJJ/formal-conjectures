/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0785 : Family 10 := level10.get ⟨1176,by decide⟩
def sourceMap0785 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0785 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0785_checked : acceptsGraphIso
    (source (graph core0785) (root 10) 0 0) DegreeOneSmallSpectrum1842.graph sourceMap0785=true := by decide +kernel
theorem fusedMap0785_checked : acceptsGraphIso
    (fused (graph core0785) (root 10) 0 0) DegreeOneSmallSpectrum1840.graph fusedMap0785=true := by decide +kernel
theorem certified0785 : Certified (graph core0785) (root 10) 0 0 :=
  of_native_maps core0785 DegreeOneSmallSpectrum1842.graph DegreeOneSmallSpectrum1840.graph
    sourceMap0785 fusedMap0785 sourceMap0785_checked fusedMap0785_checked
    DegreeTwoThreeFiniteComparisons.comparison0785
#print axioms sourceMap0785_checked
#print axioms fusedMap0785_checked
#print axioms certified0785
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
