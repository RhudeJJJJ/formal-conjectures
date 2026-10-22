/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0787 : Family 10 := level10.get ⟨1183,by decide⟩
def sourceMap0787 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0787 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,8,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0787_checked : acceptsGraphIso
    (source (graph core0787) (root 10) 0 0) DegreeOneSmallSpectrum1879.graph sourceMap0787=true := by decide +kernel
theorem fusedMap0787_checked : acceptsGraphIso
    (fused (graph core0787) (root 10) 0 0) DegreeOneSmallSpectrum1870.graph fusedMap0787=true := by decide +kernel
theorem certified0787 : Certified (graph core0787) (root 10) 0 0 :=
  of_native_maps core0787 DegreeOneSmallSpectrum1879.graph DegreeOneSmallSpectrum1870.graph
    sourceMap0787 fusedMap0787 sourceMap0787_checked fusedMap0787_checked
    DegreeTwoThreeFiniteComparisons.comparison0787
#print axioms sourceMap0787_checked
#print axioms fusedMap0787_checked
#print axioms certified0787
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
