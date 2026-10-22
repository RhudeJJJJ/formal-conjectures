/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0149 : Family 8 := level8.get ⟨241,by decide⟩
def sourceMap0149 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0149 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0149_checked : acceptsGraphIso
    (source (graph core0149) (root 8) 0 0) SmallGeFourSpectrum082.graph sourceMap0149=true := by decide +kernel
theorem fusedMap0149_checked : acceptsGraphIso
    (fused (graph core0149) (root 8) 0 0) SmallGeFourSpectrum061.graph fusedMap0149=true := by decide +kernel
theorem certified0149 : Certified (graph core0149) (root 8) 0 0 :=
  of_native_maps core0149 SmallGeFourSpectrum082.graph SmallGeFourSpectrum061.graph
    sourceMap0149 fusedMap0149 sourceMap0149_checked fusedMap0149_checked
    DegreeTwoThreeFiniteComparisons.comparison0149
#print axioms sourceMap0149_checked
#print axioms fusedMap0149_checked
#print axioms certified0149
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
