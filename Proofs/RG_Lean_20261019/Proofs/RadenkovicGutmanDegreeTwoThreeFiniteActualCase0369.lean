/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0369 : Family 9 := level9.get ⟨601,by decide⟩
def sourceMap0369 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0369 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0369_checked : acceptsGraphIso
    (source (graph core0369) (root 9) 0 0) SmallGeFourSpectrum218.graph sourceMap0369=true := by decide +kernel
theorem fusedMap0369_checked : acceptsGraphIso
    (fused (graph core0369) (root 9) 0 0) SmallGeFourSpectrum148.graph fusedMap0369=true := by decide +kernel
theorem certified0369 : Certified (graph core0369) (root 9) 0 0 :=
  of_native_maps core0369 SmallGeFourSpectrum218.graph SmallGeFourSpectrum148.graph
    sourceMap0369 fusedMap0369 sourceMap0369_checked fusedMap0369_checked
    DegreeTwoThreeFiniteComparisons.comparison0369
#print axioms sourceMap0369_checked
#print axioms fusedMap0369_checked
#print axioms certified0369
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
