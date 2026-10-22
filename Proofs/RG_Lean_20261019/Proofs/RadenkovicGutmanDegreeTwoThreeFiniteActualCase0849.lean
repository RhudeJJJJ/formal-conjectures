/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0849 : Family 10 := level10.get ⟨1330,by decide⟩
def sourceMap0849 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0849 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0849_checked : acceptsGraphIso
    (source (graph core0849) (root 10) 0 0) DegreeTwoThreeSpectrum1644.graph sourceMap0849=true := by decide +kernel
theorem fusedMap0849_checked : acceptsGraphIso
    (fused (graph core0849) (root 10) 0 0) DegreeOneSmallSpectrum1921.graph fusedMap0849=true := by decide +kernel
theorem certified0849 : Certified (graph core0849) (root 10) 0 0 :=
  of_native_maps core0849 DegreeTwoThreeSpectrum1644.graph DegreeOneSmallSpectrum1921.graph
    sourceMap0849 fusedMap0849 sourceMap0849_checked fusedMap0849_checked
    DegreeTwoThreeFiniteComparisons.comparison0849
#print axioms sourceMap0849_checked
#print axioms fusedMap0849_checked
#print axioms certified0849
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
