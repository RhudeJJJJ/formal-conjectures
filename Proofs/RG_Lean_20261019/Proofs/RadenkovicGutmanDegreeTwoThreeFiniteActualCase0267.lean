/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0267 : Family 9 := level9.get ⟨351,by decide⟩
def sourceMap0267 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0267 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0267_checked : acceptsGraphIso
    (source (graph core0267) (root 9) 0 0) DegreeOneSmallSpectrum662.graph sourceMap0267=true := by decide +kernel
theorem fusedMap0267_checked : acceptsGraphIso
    (fused (graph core0267) (root 9) 0 0) DegreeOneSmallSpectrum660.graph fusedMap0267=true := by decide +kernel
theorem certified0267 : Certified (graph core0267) (root 9) 0 0 :=
  of_native_maps core0267 DegreeOneSmallSpectrum662.graph DegreeOneSmallSpectrum660.graph
    sourceMap0267 fusedMap0267 sourceMap0267_checked fusedMap0267_checked
    DegreeTwoThreeFiniteComparisons.comparison0267
#print axioms sourceMap0267_checked
#print axioms fusedMap0267_checked
#print axioms certified0267
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
