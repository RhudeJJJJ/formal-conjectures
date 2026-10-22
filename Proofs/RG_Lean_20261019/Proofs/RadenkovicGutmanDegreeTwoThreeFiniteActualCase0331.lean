/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0331 : Family 9 := level9.get ⟨510,by decide⟩
def sourceMap0331 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,9,10,11,5,6,7,8,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0331 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0331_checked : acceptsGraphIso
    (source (graph core0331) (root 9) 0 0) SmallGeFourSpectrum132.graph sourceMap0331=true := by decide +kernel
theorem fusedMap0331_checked : acceptsGraphIso
    (fused (graph core0331) (root 9) 0 0) SmallGeFourSpectrum191.graph fusedMap0331=true := by decide +kernel
theorem certified0331 : Certified (graph core0331) (root 9) 0 0 :=
  of_native_maps core0331 SmallGeFourSpectrum132.graph SmallGeFourSpectrum191.graph
    sourceMap0331 fusedMap0331 sourceMap0331_checked fusedMap0331_checked
    DegreeTwoThreeFiniteComparisons.comparison0331
#print axioms sourceMap0331_checked
#print axioms fusedMap0331_checked
#print axioms certified0331
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
