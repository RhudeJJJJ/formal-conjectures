/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0389 : Family 9 := level9.get ⟨653,by decide⟩
def sourceMap0389 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0389 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0389_checked : acceptsGraphIso
    (source (graph core0389) (root 9) 0 0) SmallGeFourSpectrum188.graph sourceMap0389=true := by decide +kernel
theorem fusedMap0389_checked : acceptsGraphIso
    (fused (graph core0389) (root 9) 0 0) SmallGeFourSpectrum187.graph fusedMap0389=true := by decide +kernel
theorem certified0389 : Certified (graph core0389) (root 9) 0 0 :=
  of_native_maps core0389 SmallGeFourSpectrum188.graph SmallGeFourSpectrum187.graph
    sourceMap0389 fusedMap0389 sourceMap0389_checked fusedMap0389_checked
    DegreeTwoThreeFiniteComparisons.comparison0389
#print axioms sourceMap0389_checked
#print axioms fusedMap0389_checked
#print axioms certified0389
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
