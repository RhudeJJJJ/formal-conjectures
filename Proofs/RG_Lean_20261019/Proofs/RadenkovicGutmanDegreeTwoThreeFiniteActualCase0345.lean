/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0345 : Family 9 := level9.get ⟨547,by decide⟩
def sourceMap0345 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,11,8,9,10] (sourceLabel 9 0 0 v)
def fusedMap0345 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0345_checked : acceptsGraphIso
    (source (graph core0345) (root 9) 0 0) SmallGeFourSpectrum210.graph sourceMap0345=true := by decide +kernel
theorem fusedMap0345_checked : acceptsGraphIso
    (fused (graph core0345) (root 9) 0 0) SmallGeFourSpectrum120.graph fusedMap0345=true := by decide +kernel
theorem certified0345 : Certified (graph core0345) (root 9) 0 0 :=
  of_native_maps core0345 SmallGeFourSpectrum210.graph SmallGeFourSpectrum120.graph
    sourceMap0345 fusedMap0345 sourceMap0345_checked fusedMap0345_checked
    DegreeTwoThreeFiniteComparisons.comparison0345
#print axioms sourceMap0345_checked
#print axioms fusedMap0345_checked
#print axioms certified0345
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
