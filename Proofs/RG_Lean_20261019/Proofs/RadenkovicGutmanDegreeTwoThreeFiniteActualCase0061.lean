/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0061 : Family 7 := level7.get ⟨101,by decide⟩
def sourceMap0061 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap0061 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,9,7,8] (fusedLabel 7 0 0 v)
theorem sourceMap0061_checked : acceptsGraphIso
    (source (graph core0061) (root 7) 0 0) SmallGeFourSpectrum027.graph sourceMap0061=true := by decide +kernel
theorem fusedMap0061_checked : acceptsGraphIso
    (fused (graph core0061) (root 7) 0 0) SmallGeFourSpectrum029.graph fusedMap0061=true := by decide +kernel
theorem certified0061 : Certified (graph core0061) (root 7) 0 0 :=
  of_native_maps core0061 SmallGeFourSpectrum027.graph SmallGeFourSpectrum029.graph
    sourceMap0061 fusedMap0061 sourceMap0061_checked fusedMap0061_checked
    DegreeTwoThreeFiniteComparisons.comparison0061
#print axioms sourceMap0061_checked
#print axioms fusedMap0061_checked
#print axioms certified0061
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
