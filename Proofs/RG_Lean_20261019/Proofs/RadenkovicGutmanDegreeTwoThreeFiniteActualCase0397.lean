/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0397 : Family 9 := level9.get ⟨693,by decide⟩
def sourceMap0397 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0397 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0397_checked : acceptsGraphIso
    (source (graph core0397) (root 9) 0 0) SmallGeFourSpectrum212.graph sourceMap0397=true := by decide +kernel
theorem fusedMap0397_checked : acceptsGraphIso
    (fused (graph core0397) (root 9) 0 0) SmallGeFourSpectrum211.graph fusedMap0397=true := by decide +kernel
theorem certified0397 : Certified (graph core0397) (root 9) 0 0 :=
  of_native_maps core0397 SmallGeFourSpectrum212.graph SmallGeFourSpectrum211.graph
    sourceMap0397 fusedMap0397 sourceMap0397_checked fusedMap0397_checked
    DegreeTwoThreeFiniteComparisons.comparison0397
#print axioms sourceMap0397_checked
#print axioms fusedMap0397_checked
#print axioms certified0397
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
