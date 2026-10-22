/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0262 : Family 9 := level9.get ⟨340,by decide⟩
def sourceMap0262 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0262 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0262_checked : acceptsGraphIso
    (source (graph core0262) (root 9) 0 0) DegreeTwoThreeSpectrum571.graph sourceMap0262=true := by decide +kernel
theorem fusedMap0262_checked : acceptsGraphIso
    (fused (graph core0262) (root 9) 0 0) DegreeOneSmallSpectrum654.graph fusedMap0262=true := by decide +kernel
theorem certified0262 : Certified (graph core0262) (root 9) 0 0 :=
  of_native_maps core0262 DegreeTwoThreeSpectrum571.graph DegreeOneSmallSpectrum654.graph
    sourceMap0262 fusedMap0262 sourceMap0262_checked fusedMap0262_checked
    DegreeTwoThreeFiniteComparisons.comparison0262
#print axioms sourceMap0262_checked
#print axioms fusedMap0262_checked
#print axioms certified0262
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
