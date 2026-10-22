/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0933 : Family 10 := level10.get ⟨1539,by decide⟩
def sourceMap0933 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0933 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0933_checked : acceptsGraphIso
    (source (graph core0933) (root 10) 0 0) DegreeOneSmallSpectrum1547.graph sourceMap0933=true := by decide +kernel
theorem fusedMap0933_checked : acceptsGraphIso
    (fused (graph core0933) (root 10) 0 0) DegreeOneSmallSpectrum1546.graph fusedMap0933=true := by decide +kernel
theorem certified0933 : Certified (graph core0933) (root 10) 0 0 :=
  of_native_maps core0933 DegreeOneSmallSpectrum1547.graph DegreeOneSmallSpectrum1546.graph
    sourceMap0933 fusedMap0933 sourceMap0933_checked fusedMap0933_checked
    DegreeTwoThreeFiniteComparisons.comparison0933
#print axioms sourceMap0933_checked
#print axioms fusedMap0933_checked
#print axioms certified0933
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
