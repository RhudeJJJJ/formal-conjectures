/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0892 : Family 10 := level10.get ⟨1430,by decide⟩
def sourceMap0892 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0892 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,6,7,8,9,10,11,12,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap0892_checked : acceptsGraphIso
    (source (graph core0892) (root 10) 0 0) DegreeOneSmallSpectrum1952.graph sourceMap0892=true := by decide +kernel
theorem fusedMap0892_checked : acceptsGraphIso
    (fused (graph core0892) (root 10) 0 0) DegreeOneSmallSpectrum1928.graph fusedMap0892=true := by decide +kernel
theorem certified0892 : Certified (graph core0892) (root 10) 0 0 :=
  of_native_maps core0892 DegreeOneSmallSpectrum1952.graph DegreeOneSmallSpectrum1928.graph
    sourceMap0892 fusedMap0892 sourceMap0892_checked fusedMap0892_checked
    DegreeTwoThreeFiniteComparisons.comparison0892
#print axioms sourceMap0892_checked
#print axioms fusedMap0892_checked
#print axioms certified0892
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
