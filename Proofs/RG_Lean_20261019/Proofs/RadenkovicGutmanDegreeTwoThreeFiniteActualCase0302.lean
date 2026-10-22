/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0302 : Family 9 := level9.get ⟨443,by decide⟩
def sourceMap0302 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,5,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0302 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,10,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap0302_checked : acceptsGraphIso
    (source (graph core0302) (root 9) 0 0) SmallGeFourSpectrum134.graph sourceMap0302=true := by decide +kernel
theorem fusedMap0302_checked : acceptsGraphIso
    (fused (graph core0302) (root 9) 0 0) SmallGeFourSpectrum186.graph fusedMap0302=true := by decide +kernel
theorem certified0302 : Certified (graph core0302) (root 9) 0 0 :=
  of_native_maps core0302 SmallGeFourSpectrum134.graph SmallGeFourSpectrum186.graph
    sourceMap0302 fusedMap0302 sourceMap0302_checked fusedMap0302_checked
    DegreeTwoThreeFiniteComparisons.comparison0302
#print axioms sourceMap0302_checked
#print axioms fusedMap0302_checked
#print axioms certified0302
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
