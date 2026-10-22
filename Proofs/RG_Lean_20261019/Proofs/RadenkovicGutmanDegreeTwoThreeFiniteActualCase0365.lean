/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0365 : Family 9 := level9.get ⟨593,by decide⟩
def sourceMap0365 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0365 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0365_checked : acceptsGraphIso
    (source (graph core0365) (root 9) 0 0) SmallGeFourSpectrum217.graph sourceMap0365=true := by decide +kernel
theorem fusedMap0365_checked : acceptsGraphIso
    (fused (graph core0365) (root 9) 0 0) SmallGeFourSpectrum143.graph fusedMap0365=true := by decide +kernel
theorem certified0365 : Certified (graph core0365) (root 9) 0 0 :=
  of_native_maps core0365 SmallGeFourSpectrum217.graph SmallGeFourSpectrum143.graph
    sourceMap0365 fusedMap0365 sourceMap0365_checked fusedMap0365_checked
    DegreeTwoThreeFiniteComparisons.comparison0365
#print axioms sourceMap0365_checked
#print axioms fusedMap0365_checked
#print axioms certified0365
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
