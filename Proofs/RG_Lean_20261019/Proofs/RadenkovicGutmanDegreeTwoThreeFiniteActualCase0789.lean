/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0789 : Family 10 := level10.get ⟨1188,by decide⟩
def sourceMap0789 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,5,6,7,8,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0789 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,9,10,11,12,8,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0789_checked : acceptsGraphIso
    (source (graph core0789) (root 10) 0 0) DegreeOneSmallSpectrum1602.graph sourceMap0789=true := by decide +kernel
theorem fusedMap0789_checked : acceptsGraphIso
    (fused (graph core0789) (root 10) 0 0) DegreeOneSmallSpectrum1871.graph fusedMap0789=true := by decide +kernel
theorem certified0789 : Certified (graph core0789) (root 10) 0 0 :=
  of_native_maps core0789 DegreeOneSmallSpectrum1602.graph DegreeOneSmallSpectrum1871.graph
    sourceMap0789 fusedMap0789 sourceMap0789_checked fusedMap0789_checked
    DegreeTwoThreeFiniteComparisons.comparison0789
#print axioms sourceMap0789_checked
#print axioms fusedMap0789_checked
#print axioms certified0789
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
