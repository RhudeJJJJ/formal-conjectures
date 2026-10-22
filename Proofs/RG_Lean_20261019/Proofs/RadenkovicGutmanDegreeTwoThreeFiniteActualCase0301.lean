/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0301 : Family 9 := level9.get ⟨440,by decide⟩
def sourceMap0301 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0301 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0301_checked : acceptsGraphIso
    (source (graph core0301) (root 9) 0 0) SmallGeFourSpectrum136.graph sourceMap0301=true := by decide +kernel
theorem fusedMap0301_checked : acceptsGraphIso
    (fused (graph core0301) (root 9) 0 0) SmallGeFourSpectrum182.graph fusedMap0301=true := by decide +kernel
theorem certified0301 : Certified (graph core0301) (root 9) 0 0 :=
  of_native_maps core0301 SmallGeFourSpectrum136.graph SmallGeFourSpectrum182.graph
    sourceMap0301 fusedMap0301 sourceMap0301_checked fusedMap0301_checked
    DegreeTwoThreeFiniteComparisons.comparison0301
#print axioms sourceMap0301_checked
#print axioms fusedMap0301_checked
#print axioms certified0301
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
