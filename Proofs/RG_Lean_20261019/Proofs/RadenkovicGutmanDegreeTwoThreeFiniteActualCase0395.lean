/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0395 : Family 9 := level9.get ⟨690,by decide⟩
def sourceMap0395 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0395 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0395_checked : acceptsGraphIso
    (source (graph core0395) (root 9) 0 0) SmallGeFourSpectrum200.graph sourceMap0395=true := by decide +kernel
theorem fusedMap0395_checked : acceptsGraphIso
    (fused (graph core0395) (root 9) 0 0) SmallGeFourSpectrum202.graph fusedMap0395=true := by decide +kernel
theorem certified0395 : Certified (graph core0395) (root 9) 0 0 :=
  of_native_maps core0395 SmallGeFourSpectrum200.graph SmallGeFourSpectrum202.graph
    sourceMap0395 fusedMap0395 sourceMap0395_checked fusedMap0395_checked
    DegreeTwoThreeFiniteComparisons.comparison0395
#print axioms sourceMap0395_checked
#print axioms fusedMap0395_checked
#print axioms certified0395
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
