/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0235 : Family 9 := level9.get ⟨269,by decide⟩
def sourceMap0235 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0235 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap0235_checked : acceptsGraphIso
    (source (graph core0235) (root 9) 0 0) SmallGeFourSpectrum138.graph sourceMap0235=true := by decide +kernel
theorem fusedMap0235_checked : acceptsGraphIso
    (fused (graph core0235) (root 9) 0 0) SmallGeFourSpectrum106.graph fusedMap0235=true := by decide +kernel
theorem certified0235 : Certified (graph core0235) (root 9) 0 0 :=
  of_native_maps core0235 SmallGeFourSpectrum138.graph SmallGeFourSpectrum106.graph
    sourceMap0235 fusedMap0235 sourceMap0235_checked fusedMap0235_checked
    DegreeTwoThreeFiniteComparisons.comparison0235
#print axioms sourceMap0235_checked
#print axioms fusedMap0235_checked
#print axioms certified0235
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
