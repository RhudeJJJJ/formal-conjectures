/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0115 : Family 8 := level8.get ⟨165,by decide⟩
def sourceMap0115 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,8,9,10,5,6,7,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0115 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0115_checked : acceptsGraphIso
    (source (graph core0115) (root 8) 0 0) DegreeOneSmallSpectrum245.graph sourceMap0115=true := by decide +kernel
theorem fusedMap0115_checked : acceptsGraphIso
    (fused (graph core0115) (root 8) 0 0) DegreeOneSmallSpectrum342.graph fusedMap0115=true := by decide +kernel
theorem certified0115 : Certified (graph core0115) (root 8) 0 0 :=
  of_native_maps core0115 DegreeOneSmallSpectrum245.graph DegreeOneSmallSpectrum342.graph
    sourceMap0115 fusedMap0115 sourceMap0115_checked fusedMap0115_checked
    DegreeTwoThreeFiniteComparisons.comparison0115
#print axioms sourceMap0115_checked
#print axioms fusedMap0115_checked
#print axioms certified0115
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
