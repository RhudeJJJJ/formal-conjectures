/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0432 : Family 10 := level10.get ⟨162,by decide⟩
def sourceMap0432 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0432 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0432_checked : acceptsGraphIso
    (source (graph core0432) (root 10) 0 0) DegreeOneSmallSpectrum921.graph sourceMap0432=true := by decide +kernel
theorem fusedMap0432_checked : acceptsGraphIso
    (fused (graph core0432) (root 10) 0 0) DegreeOneSmallSpectrum914.graph fusedMap0432=true := by decide +kernel
theorem certified0432 : Certified (graph core0432) (root 10) 0 0 :=
  of_native_maps core0432 DegreeOneSmallSpectrum921.graph DegreeOneSmallSpectrum914.graph
    sourceMap0432 fusedMap0432 sourceMap0432_checked fusedMap0432_checked
    DegreeTwoThreeFiniteComparisons.comparison0432
#print axioms sourceMap0432_checked
#print axioms fusedMap0432_checked
#print axioms certified0432
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
