/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0394 : Family 9 := level9.get ⟨678,by decide⟩
def sourceMap0394 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,5,6,7,8] (sourceLabel 9 0 0 v)
def fusedMap0394 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,9,10,11,1,2,3,4,5,6,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap0394_checked : acceptsGraphIso
    (source (graph core0394) (root 9) 0 0) SmallGeFourSpectrum118.graph sourceMap0394=true := by decide +kernel
theorem fusedMap0394_checked : acceptsGraphIso
    (fused (graph core0394) (root 9) 0 0) SmallGeFourSpectrum117.graph fusedMap0394=true := by decide +kernel
theorem certified0394 : Certified (graph core0394) (root 9) 0 0 :=
  of_native_maps core0394 SmallGeFourSpectrum118.graph SmallGeFourSpectrum117.graph
    sourceMap0394 fusedMap0394 sourceMap0394_checked fusedMap0394_checked
    DegreeTwoThreeFiniteComparisons.comparison0394
#print axioms sourceMap0394_checked
#print axioms fusedMap0394_checked
#print axioms certified0394
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
