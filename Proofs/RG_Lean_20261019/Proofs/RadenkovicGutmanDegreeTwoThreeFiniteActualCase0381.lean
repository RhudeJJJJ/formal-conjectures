/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0381 : Family 9 := level9.get ⟨635,by decide⟩
def sourceMap0381 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0381 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0381_checked : acceptsGraphIso
    (source (graph core0381) (root 9) 0 0) SmallGeFourSpectrum220.graph sourceMap0381=true := by decide +kernel
theorem fusedMap0381_checked : acceptsGraphIso
    (fused (graph core0381) (root 9) 0 0) SmallGeFourSpectrum168.graph fusedMap0381=true := by decide +kernel
theorem certified0381 : Certified (graph core0381) (root 9) 0 0 :=
  of_native_maps core0381 SmallGeFourSpectrum220.graph SmallGeFourSpectrum168.graph
    sourceMap0381 fusedMap0381 sourceMap0381_checked fusedMap0381_checked
    DegreeTwoThreeFiniteComparisons.comparison0381
#print axioms sourceMap0381_checked
#print axioms fusedMap0381_checked
#print axioms certified0381
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
