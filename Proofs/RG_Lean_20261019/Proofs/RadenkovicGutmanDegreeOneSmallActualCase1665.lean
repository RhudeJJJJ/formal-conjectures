/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1665 : Family 9 := level9.get ⟨422,by decide⟩
def sourceMap1665 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,4,5,2,3] (sourceLabel 9 0 0 v)
def fusedMap1665 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,8,9] (fusedLabel 9 0 0 v)
theorem sourceMap1665_checked : acceptsGraphIso
    (source (graph core1665) (root 9) 0 0) DegreeOneSmallSpectrum722.graph sourceMap1665=true := by decide +kernel
theorem fusedMap1665_checked : acceptsGraphIso
    (fused (graph core1665) (root 9) 0 0) DegreeOneSmallSpectrum787.graph fusedMap1665=true := by decide +kernel
theorem certified1665 : Certified (graph core1665) (root 9) 0 0 :=
  of_native_maps core1665 DegreeOneSmallSpectrum722.graph DegreeOneSmallSpectrum787.graph
    sourceMap1665 fusedMap1665 sourceMap1665_checked fusedMap1665_checked
    DegreeOneSmallComparisons.comparison1665
#print axioms sourceMap1665_checked
#print axioms fusedMap1665_checked
#print axioms certified1665
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
