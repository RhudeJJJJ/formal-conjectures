/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons32
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1623 : Family 9 := level9.get ⟨366,by decide⟩
def sourceMap1623 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (sourceLabel 9 0 0 v)
def fusedMap1623 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1623_checked : acceptsGraphIso
    (source (graph core1623) (root 9) 0 0) SmallGeFourSpectrum147.graph sourceMap1623=true := by decide +kernel
theorem fusedMap1623_checked : acceptsGraphIso
    (fused (graph core1623) (root 9) 0 0) SmallGeFourSpectrum149.graph fusedMap1623=true := by decide +kernel
theorem certified1623 : Certified (graph core1623) (root 9) 0 0 :=
  of_native_maps core1623 SmallGeFourSpectrum147.graph SmallGeFourSpectrum149.graph
    sourceMap1623 fusedMap1623 sourceMap1623_checked fusedMap1623_checked
    DegreeOneSmallComparisons.comparison1623
#print axioms sourceMap1623_checked
#print axioms fusedMap1623_checked
#print axioms certified1623
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
