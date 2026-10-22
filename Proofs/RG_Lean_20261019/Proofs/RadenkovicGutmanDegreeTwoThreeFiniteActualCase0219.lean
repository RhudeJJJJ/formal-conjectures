/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0219 : Family 9 := level9.get ⟨223,by decide⟩
def sourceMap0219 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,6,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0219 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,6,0,1,2,3,4,5,11,10,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap0219_checked : acceptsGraphIso
    (source (graph core0219) (root 9) 0 0) DegreeTwoThreeSpectrum571.graph sourceMap0219=true := by decide +kernel
theorem fusedMap0219_checked : acceptsGraphIso
    (fused (graph core0219) (root 9) 0 0) DegreeOneSmallSpectrum529.graph fusedMap0219=true := by decide +kernel
theorem certified0219 : Certified (graph core0219) (root 9) 0 0 :=
  of_native_maps core0219 DegreeTwoThreeSpectrum571.graph DegreeOneSmallSpectrum529.graph
    sourceMap0219 fusedMap0219 sourceMap0219_checked fusedMap0219_checked
    DegreeTwoThreeFiniteComparisons.comparison0219
#print axioms sourceMap0219_checked
#print axioms fusedMap0219_checked
#print axioms certified0219
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
