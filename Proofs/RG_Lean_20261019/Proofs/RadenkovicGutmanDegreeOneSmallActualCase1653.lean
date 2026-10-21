/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1653 : Family 9 := level9.get ⟨398,by decide⟩
def sourceMap1653 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (sourceLabel 9 0 0 v)
def fusedMap1653 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,6,7] (fusedLabel 9 0 0 v)
theorem sourceMap1653_checked : acceptsGraphIso
    (source (graph core1653) (root 9) 0 0) SmallGeFourSpectrum147.graph sourceMap1653=true := by decide +kernel
theorem fusedMap1653_checked : acceptsGraphIso
    (fused (graph core1653) (root 9) 0 0) SmallGeFourSpectrum162.graph fusedMap1653=true := by decide +kernel
theorem certified1653 : Certified (graph core1653) (root 9) 0 0 :=
  of_native_maps core1653 SmallGeFourSpectrum147.graph SmallGeFourSpectrum162.graph
    sourceMap1653 fusedMap1653 sourceMap1653_checked fusedMap1653_checked
    DegreeOneSmallComparisons.comparison1653
#print axioms sourceMap1653_checked
#print axioms fusedMap1653_checked
#print axioms certified1653
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
