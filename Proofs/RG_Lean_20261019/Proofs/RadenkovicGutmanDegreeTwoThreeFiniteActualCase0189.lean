/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0189 : Family 9 := level9.get ⟨128,by decide⟩
def sourceMap0189 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0189 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,5,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0189_checked : acceptsGraphIso
    (source (graph core0189) (root 9) 0 0) DegreeOneSmallSpectrum405.graph sourceMap0189=true := by decide +kernel
theorem fusedMap0189_checked : acceptsGraphIso
    (fused (graph core0189) (root 9) 0 0) DegreeOneSmallSpectrum540.graph fusedMap0189=true := by decide +kernel
theorem certified0189 : Certified (graph core0189) (root 9) 0 0 :=
  of_native_maps core0189 DegreeOneSmallSpectrum405.graph DegreeOneSmallSpectrum540.graph
    sourceMap0189 fusedMap0189 sourceMap0189_checked fusedMap0189_checked
    DegreeTwoThreeFiniteComparisons.comparison0189
#print axioms sourceMap0189_checked
#print axioms fusedMap0189_checked
#print axioms certified0189
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
