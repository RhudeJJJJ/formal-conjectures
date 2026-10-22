/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0856 : Family 10 := level10.get ⟨1346,by decide⟩
def sourceMap0856 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0856 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0856_checked : acceptsGraphIso
    (source (graph core0856) (root 10) 0 0) DegreeOneSmallSpectrum1958.graph sourceMap0856=true := by decide +kernel
theorem fusedMap0856_checked : acceptsGraphIso
    (fused (graph core0856) (root 10) 0 0) DegreeOneSmallSpectrum1956.graph fusedMap0856=true := by decide +kernel
theorem certified0856 : Certified (graph core0856) (root 10) 0 0 :=
  of_native_maps core0856 DegreeOneSmallSpectrum1958.graph DegreeOneSmallSpectrum1956.graph
    sourceMap0856 fusedMap0856 sourceMap0856_checked fusedMap0856_checked
    DegreeTwoThreeFiniteComparisons.comparison0856
#print axioms sourceMap0856_checked
#print axioms fusedMap0856_checked
#print axioms certified0856
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
