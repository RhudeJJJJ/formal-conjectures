/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons03
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0156 : Family 8 := level8.get ⟨265,by decide⟩
def sourceMap0156 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0156 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0156_checked : acceptsGraphIso
    (source (graph core0156) (root 8) 0 0) SmallGeFourSpectrum072.graph sourceMap0156=true := by decide +kernel
theorem fusedMap0156_checked : acceptsGraphIso
    (fused (graph core0156) (root 8) 0 0) SmallGeFourSpectrum074.graph fusedMap0156=true := by decide +kernel
theorem certified0156 : Certified (graph core0156) (root 8) 0 0 :=
  of_native_maps core0156 SmallGeFourSpectrum072.graph SmallGeFourSpectrum074.graph
    sourceMap0156 fusedMap0156 sourceMap0156_checked fusedMap0156_checked
    DegreeTwoThreeFiniteComparisons.comparison0156
#print axioms sourceMap0156_checked
#print axioms fusedMap0156_checked
#print axioms certified0156
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
