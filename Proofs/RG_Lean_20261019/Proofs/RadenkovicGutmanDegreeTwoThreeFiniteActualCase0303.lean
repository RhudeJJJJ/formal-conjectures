/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0303 : Family 9 := level9.get ⟨444,by decide⟩
def sourceMap0303 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0303 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,2,3,4,5] (fusedLabel 9 0 0 v)
theorem sourceMap0303_checked : acceptsGraphIso
    (source (graph core0303) (root 9) 0 0) SmallGeFourSpectrum185.graph sourceMap0303=true := by decide +kernel
theorem fusedMap0303_checked : acceptsGraphIso
    (fused (graph core0303) (root 9) 0 0) SmallGeFourSpectrum176.graph fusedMap0303=true := by decide +kernel
theorem certified0303 : Certified (graph core0303) (root 9) 0 0 :=
  of_native_maps core0303 SmallGeFourSpectrum185.graph SmallGeFourSpectrum176.graph
    sourceMap0303 fusedMap0303 sourceMap0303_checked fusedMap0303_checked
    DegreeTwoThreeFiniteComparisons.comparison0303
#print axioms sourceMap0303_checked
#print axioms fusedMap0303_checked
#print axioms certified0303
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
