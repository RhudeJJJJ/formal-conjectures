/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0379 : Family 9 := level9.get ⟨631,by decide⟩
def sourceMap0379 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0379 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0379_checked : acceptsGraphIso
    (source (graph core0379) (root 9) 0 0) SmallGeFourSpectrum219.graph sourceMap0379=true := by decide +kernel
theorem fusedMap0379_checked : acceptsGraphIso
    (fused (graph core0379) (root 9) 0 0) SmallGeFourSpectrum165.graph fusedMap0379=true := by decide +kernel
theorem certified0379 : Certified (graph core0379) (root 9) 0 0 :=
  of_native_maps core0379 SmallGeFourSpectrum219.graph SmallGeFourSpectrum165.graph
    sourceMap0379 fusedMap0379 sourceMap0379_checked fusedMap0379_checked
    DegreeTwoThreeFiniteComparisons.comparison0379
#print axioms sourceMap0379_checked
#print axioms fusedMap0379_checked
#print axioms certified0379
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
