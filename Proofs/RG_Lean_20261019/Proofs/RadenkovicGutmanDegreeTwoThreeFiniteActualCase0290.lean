/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0290 : Family 9 := level9.get ⟨408,by decide⟩
def sourceMap0290 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0290 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0290_checked : acceptsGraphIso
    (source (graph core0290) (root 9) 0 0) DegreeOneSmallSpectrum488.graph sourceMap0290=true := by decide +kernel
theorem fusedMap0290_checked : acceptsGraphIso
    (fused (graph core0290) (root 9) 0 0) DegreeOneSmallSpectrum487.graph fusedMap0290=true := by decide +kernel
theorem certified0290 : Certified (graph core0290) (root 9) 0 0 :=
  of_native_maps core0290 DegreeOneSmallSpectrum488.graph DegreeOneSmallSpectrum487.graph
    sourceMap0290 fusedMap0290 sourceMap0290_checked fusedMap0290_checked
    DegreeTwoThreeFiniteComparisons.comparison0290
#print axioms sourceMap0290_checked
#print axioms fusedMap0290_checked
#print axioms certified0290
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
