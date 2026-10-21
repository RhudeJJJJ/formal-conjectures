/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1345 : Family 9 := level9.get ⟨99,by decide⟩
def sourceMap1345 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1345 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1345_checked : acceptsGraphIso
    (source (graph core1345) (root 9) 0 0) SmallGeFourSpectrum098.graph sourceMap1345=true := by decide +kernel
theorem fusedMap1345_checked : acceptsGraphIso
    (fused (graph core1345) (root 9) 0 0) SmallGeFourSpectrum110.graph fusedMap1345=true := by decide +kernel
theorem certified1345 : Certified (graph core1345) (root 9) 0 0 :=
  of_native_maps core1345 SmallGeFourSpectrum098.graph SmallGeFourSpectrum110.graph
    sourceMap1345 fusedMap1345 sourceMap1345_checked fusedMap1345_checked
    DegreeOneSmallComparisons.comparison1345
#print axioms sourceMap1345_checked
#print axioms fusedMap1345_checked
#print axioms certified1345
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
