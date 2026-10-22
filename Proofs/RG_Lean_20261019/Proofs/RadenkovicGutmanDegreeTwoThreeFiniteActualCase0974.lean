/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0974 : Family 10 := level10.get ⟨1635,by decide⟩
def sourceMap0974 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0974 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0974_checked : acceptsGraphIso
    (source (graph core0974) (root 10) 0 0) DegreeOneSmallSpectrum1745.graph sourceMap0974=true := by decide +kernel
theorem fusedMap0974_checked : acceptsGraphIso
    (fused (graph core0974) (root 10) 0 0) DegreeOneSmallSpectrum1744.graph fusedMap0974=true := by decide +kernel
theorem certified0974 : Certified (graph core0974) (root 10) 0 0 :=
  of_native_maps core0974 DegreeOneSmallSpectrum1745.graph DegreeOneSmallSpectrum1744.graph
    sourceMap0974 fusedMap0974 sourceMap0974_checked fusedMap0974_checked
    DegreeTwoThreeFiniteComparisons.comparison0974
#print axioms sourceMap0974_checked
#print axioms fusedMap0974_checked
#print axioms certified0974
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
