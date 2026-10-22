/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0126 : Family 8 := level8.get ⟨190,by decide⟩
def sourceMap0126 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10] (sourceLabel 8 0 0 v)
def fusedMap0126 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![7,0,1,2,3,4,5,6,10,8,9] (fusedLabel 8 0 0 v)
theorem sourceMap0126_checked : acceptsGraphIso
    (source (graph core0126) (root 8) 0 0) SmallGeFourSpectrum076.graph sourceMap0126=true := by decide +kernel
theorem fusedMap0126_checked : acceptsGraphIso
    (fused (graph core0126) (root 8) 0 0) SmallGeFourSpectrum043.graph fusedMap0126=true := by decide +kernel
theorem certified0126 : Certified (graph core0126) (root 8) 0 0 :=
  of_native_maps core0126 SmallGeFourSpectrum076.graph SmallGeFourSpectrum043.graph
    sourceMap0126 fusedMap0126 sourceMap0126_checked fusedMap0126_checked
    DegreeTwoThreeFiniteComparisons.comparison0126
#print axioms sourceMap0126_checked
#print axioms fusedMap0126_checked
#print axioms certified0126
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
