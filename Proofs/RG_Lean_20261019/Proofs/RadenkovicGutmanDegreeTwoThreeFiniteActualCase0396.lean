/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0396 : Family 9 := level9.get ⟨691,by decide⟩
def sourceMap0396 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0396 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0396_checked : acceptsGraphIso
    (source (graph core0396) (root 9) 0 0) SmallGeFourSpectrum207.graph sourceMap0396=true := by decide +kernel
theorem fusedMap0396_checked : acceptsGraphIso
    (fused (graph core0396) (root 9) 0 0) SmallGeFourSpectrum206.graph fusedMap0396=true := by decide +kernel
theorem certified0396 : Certified (graph core0396) (root 9) 0 0 :=
  of_native_maps core0396 SmallGeFourSpectrum207.graph SmallGeFourSpectrum206.graph
    sourceMap0396 fusedMap0396 sourceMap0396_checked fusedMap0396_checked
    DegreeTwoThreeFiniteComparisons.comparison0396
#print axioms sourceMap0396_checked
#print axioms fusedMap0396_checked
#print axioms certified0396
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
