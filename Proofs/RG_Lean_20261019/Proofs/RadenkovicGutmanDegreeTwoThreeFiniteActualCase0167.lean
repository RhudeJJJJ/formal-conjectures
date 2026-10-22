/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0167 : Family 9 := level9.get ⟨41,by decide⟩
def sourceMap0167 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,3,4,5,6] (sourceLabel 9 0 0 v)
def fusedMap0167 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,3,4,5,6] (fusedLabel 9 0 0 v)
theorem sourceMap0167_checked : acceptsGraphIso
    (source (graph core0167) (root 9) 0 0) DegreeOneSmallSpectrum380.graph sourceMap0167=true := by decide +kernel
theorem fusedMap0167_checked : acceptsGraphIso
    (fused (graph core0167) (root 9) 0 0) DegreeOneSmallSpectrum379.graph fusedMap0167=true := by decide +kernel
theorem certified0167 : Certified (graph core0167) (root 9) 0 0 :=
  of_native_maps core0167 DegreeOneSmallSpectrum380.graph DegreeOneSmallSpectrum379.graph
    sourceMap0167 fusedMap0167 sourceMap0167_checked fusedMap0167_checked
    DegreeTwoThreeFiniteComparisons.comparison0167
#print axioms sourceMap0167_checked
#print axioms fusedMap0167_checked
#print axioms certified0167
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
