/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0388 : Family 9 := level9.get ⟨651,by decide⟩
def sourceMap0388 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0388 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,5,6,7,8,9,10,11,1,2,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap0388_checked : acceptsGraphIso
    (source (graph core0388) (root 9) 0 0) SmallGeFourSpectrum181.graph sourceMap0388=true := by decide +kernel
theorem fusedMap0388_checked : acceptsGraphIso
    (fused (graph core0388) (root 9) 0 0) SmallGeFourSpectrum175.graph fusedMap0388=true := by decide +kernel
theorem certified0388 : Certified (graph core0388) (root 9) 0 0 :=
  of_native_maps core0388 SmallGeFourSpectrum181.graph SmallGeFourSpectrum175.graph
    sourceMap0388 fusedMap0388 sourceMap0388_checked fusedMap0388_checked
    DegreeTwoThreeFiniteComparisons.comparison0388
#print axioms sourceMap0388_checked
#print axioms fusedMap0388_checked
#print axioms certified0388
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
