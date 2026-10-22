/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0118 : Family 8 := level8.get ⟨172,by decide⟩
def sourceMap0118 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,8,9,10,5,6,7,2,3,4] (sourceLabel 8 0 0 v)
def fusedMap0118 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![1,0,5,6,7,8,9,10,4,2,3] (fusedLabel 8 0 0 v)
theorem sourceMap0118_checked : acceptsGraphIso
    (source (graph core0118) (root 8) 0 0) SmallGeFourSpectrum045.graph sourceMap0118=true := by decide +kernel
theorem fusedMap0118_checked : acceptsGraphIso
    (fused (graph core0118) (root 8) 0 0) SmallGeFourSpectrum066.graph fusedMap0118=true := by decide +kernel
theorem certified0118 : Certified (graph core0118) (root 8) 0 0 :=
  of_native_maps core0118 SmallGeFourSpectrum045.graph SmallGeFourSpectrum066.graph
    sourceMap0118 fusedMap0118 sourceMap0118_checked fusedMap0118_checked
    DegreeTwoThreeFiniteComparisons.comparison0118
#print axioms sourceMap0118_checked
#print axioms fusedMap0118_checked
#print axioms certified0118
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
