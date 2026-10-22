/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0346 : Family 9 := level9.get ⟨548,by decide⟩
def sourceMap0346 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (sourceLabel 9 0 0 v)
def fusedMap0346 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap0346_checked : acceptsGraphIso
    (source (graph core0346) (root 9) 0 0) SmallGeFourSpectrum126.graph sourceMap0346=true := by decide +kernel
theorem fusedMap0346_checked : acceptsGraphIso
    (fused (graph core0346) (root 9) 0 0) SmallGeFourSpectrum125.graph fusedMap0346=true := by decide +kernel
theorem certified0346 : Certified (graph core0346) (root 9) 0 0 :=
  of_native_maps core0346 SmallGeFourSpectrum126.graph SmallGeFourSpectrum125.graph
    sourceMap0346 fusedMap0346 sourceMap0346_checked fusedMap0346_checked
    DegreeTwoThreeFiniteComparisons.comparison0346
#print axioms sourceMap0346_checked
#print axioms fusedMap0346_checked
#print axioms certified0346
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
