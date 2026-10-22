/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0293 : Family 9 := level9.get ⟨420,by decide⟩
def sourceMap0293 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0293 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0293_checked : acceptsGraphIso
    (source (graph core0293) (root 9) 0 0) SmallGeFourSpectrum135.graph sourceMap0293=true := by decide +kernel
theorem fusedMap0293_checked : acceptsGraphIso
    (fused (graph core0293) (root 9) 0 0) SmallGeFourSpectrum172.graph fusedMap0293=true := by decide +kernel
theorem certified0293 : Certified (graph core0293) (root 9) 0 0 :=
  of_native_maps core0293 SmallGeFourSpectrum135.graph SmallGeFourSpectrum172.graph
    sourceMap0293 fusedMap0293 sourceMap0293_checked fusedMap0293_checked
    DegreeTwoThreeFiniteComparisons.comparison0293
#print axioms sourceMap0293_checked
#print axioms fusedMap0293_checked
#print axioms certified0293
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
