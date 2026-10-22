/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0247 : Family 9 := level9.get ⟨301,by decide⟩
def sourceMap0247 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,9,10,11,6,7,8,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0247 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,5,6,7,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0247_checked : acceptsGraphIso
    (source (graph core0247) (root 9) 0 0) SmallGeFourSpectrum133.graph sourceMap0247=true := by decide +kernel
theorem fusedMap0247_checked : acceptsGraphIso
    (fused (graph core0247) (root 9) 0 0) SmallGeFourSpectrum105.graph fusedMap0247=true := by decide +kernel
theorem certified0247 : Certified (graph core0247) (root 9) 0 0 :=
  of_native_maps core0247 SmallGeFourSpectrum133.graph SmallGeFourSpectrum105.graph
    sourceMap0247 fusedMap0247 sourceMap0247_checked fusedMap0247_checked
    DegreeTwoThreeFiniteComparisons.comparison0247
#print axioms sourceMap0247_checked
#print axioms fusedMap0247_checked
#print axioms certified0247
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
